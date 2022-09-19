module RootsOfLisp where

import Control.Monad (guard, when)
import qualified Control.Monad.Combinators as Monad
import Control.Monad.Trans.Reader (ReaderT (..))
import qualified Data.Char as Char
import Data.Containers.ListUtils (nubOrd)
import Data.Functor ((<&>))
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Data.Traversable (for)
import Data.Void (Void)
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec.Char.Lexer as L

data Expr
  = ExprAtom Text
  | ExprList [Expr]
  deriving stock (Eq, Ord, Show)

pattern ExprFalse :: Expr
pattern ExprFalse = ExprAtom "f"

pattern ExprTrue :: Expr
pattern ExprTrue = ExprAtom "t"

type Env = Map Text Expr

newtype Eval a
  = Eval ([Context] -> Either ([Context], EvalError) a)
  deriving (Applicative, Functor, Monad) via (ReaderT [Context] (Either ([Context], EvalError)))

data Context
  = ContextArgument Int
  | ContextFunction Text
  | ContextLambda
  deriving stock (Show)

showContext :: [Context] -> Text
showContext =
  Text.intercalate ", " . map show1 . reverse
  where
    show1 :: Context -> Text
    show1 = \case
      ContextArgument n -> "argument " <> Text.pack (show n)
      ContextFunction name -> "function «" <> name <> "»"
      ContextLambda -> "lambda"

data EvalError
  = ArityError Int Int
  | EmptyList
  | ExpectedAtomGotList [Expr]
  | ExpectedListGotAtom Text
  | LambdaArityError Int Int
  | MalformedAlternative Expr
  | MalformedLambda Expr
  | UnboundVariable Text
  | UnexpectedExpr Expr

runEval :: Eval a -> Either ([Context], EvalError) a
runEval (Eval f) =
  f []

push :: Context -> Eval a -> Eval a
push x (Eval f) =
  Eval \xs -> f (x : xs)

bomb :: EvalError -> Eval a
bomb err =
  Eval \context -> Left (context, err)

evaluate :: Env -> Expr -> Eval Expr
evaluate env = \case
  -- x
  ExprAtom var -> evaluateAtom env var
  ExprList (ExprAtom name : exprs0) ->
    case name of
      -- (atom ...)
      "atom" ->
        push (ContextFunction name) do
          evaluateArg1 env exprs0 <&> \case
            ExprAtom _ -> ExprTrue
            _ -> ExprFalse
      -- (car ...)
      "car" ->
        push (ContextFunction name) do
          result <- evaluateArg1 env exprs0
          (expr, _) <- push (ContextArgument 1) (matchNonEmptyList result)
          pure expr
      -- (cdr ...)
      "cdr" ->
        push (ContextFunction name) do
          result <- evaluateArg1 env exprs0
          (_, exprs) <- push (ContextArgument 1) (matchNonEmptyList result)
          pure (ExprList exprs)
      -- (cond ...)
      "cond" -> evaluateCond env exprs0
      -- (cons ...)
      "cons" ->
        push (ContextFunction name) do
          (x, xs0) <- evaluateArg2 env exprs0
          case xs0 of
            ExprAtom atom -> push (ContextArgument 2) (bomb (ExpectedListGotAtom atom))
            ExprList xs -> pure (ExprList (x : xs))
      -- (eq ...)
      "eq" ->
        push (ContextFunction name) do
          evaluateArg2 env exprs0 <&> \case
            (ExprAtom atom1, ExprAtom atom2) | atom1 == atom2 -> ExprTrue
            (ExprList [], ExprList []) -> ExprTrue
            _ -> ExprFalse
      "quote" -> push (ContextFunction name) (matchArg1 exprs0)
      -- (x ...)
      _ -> do
        expr <- evaluateAtom env name
        push (ContextFunction name) (evaluate env (ExprList (expr : exprs0)))
  -- ((label ...) ...)
  ExprList (lambda@(ExprList ((ExprAtom "label" : labelAndLambda))) : args0) ->
    push ContextLambda do
      (label, params, numParams, body) <- matchLabelParamsAndBody labelAndLambda
      matchParamsAndArgs numParams args0
      args <- evaluateArgs env args0
      let env1 =
            List.foldl'
              (\acc (param, arg) -> Map.insert param arg acc)
              (Map.insert label lambda env)
              (zip params args)
      evaluate env1 body
  -- ((lambda ...) ...)
  ExprList (ExprList (ExprAtom "lambda" : paramsAndBody) : args0) ->
    push ContextLambda do
      (params, numParams, body) <- matchParamsAndBody paramsAndBody
      matchParamsAndArgs numParams args0
      args <- evaluateArgs env args0
      let env1 = List.foldl' (\acc (param, arg) -> Map.insert param arg acc) env (zip params args)
      evaluate env1 body
  expr -> bomb (UnexpectedExpr expr)

matchArg1 :: [Expr] -> Eval Expr
matchArg1 = \case
  [arg] -> pure arg
  args -> bomb (ArityError (length args) 1)

matchArg2 :: [Expr] -> Eval (Expr, Expr)
matchArg2 = \case
  [arg1, arg2] -> pure (arg1, arg2)
  args -> bomb (ArityError (length args) 2)

matchLabelParamsAndBody :: [Expr] -> Eval (Text, [Text], Int, Expr)
matchLabelParamsAndBody = \case
  [ExprAtom label, ExprList [ExprAtom "lambda", matchParams -> Just (params, numParams), body]]
    | label `notElem` params -> pure (label, params, numParams, body)
  exprs -> bomb (MalformedLambda (ExprList (ExprAtom "label" : exprs)))

matchNonEmptyList :: Expr -> Eval (Expr, [Expr])
matchNonEmptyList = \case
  ExprAtom atom -> bomb (ExpectedListGotAtom atom)
  ExprList [] -> bomb EmptyList
  ExprList (expr : exprs) -> pure (expr, exprs)

matchParams :: Expr -> Maybe ([Text], Int)
matchParams = \case
  ExprList params0 -> do
    params1 <-
      for params0 \case
        ExprAtom param -> Just param
        _ -> Nothing
    let numParams = length params1
    guard (numParams == length (nubOrd params1))
    Just (params1, numParams)
  _ -> Nothing

matchParamsAndArgs :: Int -> [Expr] -> Eval ()
matchParamsAndArgs numParams args =
  when (numParams /= numArgs) (bomb (LambdaArityError numArgs numParams))
  where
    numArgs = length args

matchParamsAndBody :: [Expr] -> Eval ([Text], Int, Expr)
matchParamsAndBody = \case
  [matchParams -> Just (params, numParams), body] -> pure (params, numParams, body)
  exprs -> bomb (MalformedLambda (ExprList (ExprAtom "lambda" : exprs)))

evaluateArg1 :: Env -> [Expr] -> Eval Expr
evaluateArg1 env args = do
  arg <- matchArg1 args
  push (ContextArgument 1) (evaluate env arg)

evaluateArg2 :: Env -> [Expr] -> Eval (Expr, Expr)
evaluateArg2 env args = do
  (arg1, arg2) <- matchArg2 args
  result1 <- push (ContextArgument 1) (evaluate env arg1)
  result2 <- push (ContextArgument 2) (evaluate env arg2)
  pure (result1, result2)

evaluateArgs :: Env -> [Expr] -> Eval [Expr]
evaluateArgs env =
  traverse (\(i, arg) -> push (ContextArgument i) (evaluate env arg)) . zip [(1 :: Int) ..]

evaluateAtom :: Env -> Text -> Eval Expr
evaluateAtom env var =
  case Map.lookup var env of
    Nothing -> bomb (UnboundVariable var)
    Just expr -> pure expr

-- FIXME contexts
evaluateCond :: Env -> [Expr] -> Eval Expr
evaluateCond env = \case
  [] -> undefined
  alt : alts ->
    case alt of
      ExprList [lhs, rhs0] ->
        evaluate env lhs >>= \case
          ExprTrue -> evaluate env rhs0
          _ -> evaluateCond env alts
      _ -> bomb (MalformedAlternative alt)

showEvalError :: EvalError -> Text
showEvalError = \case
  ArityError actual expected ->
    "Expected "
      <> Text.pack (show expected)
      <> " argument(s), but got "
      <> Text.pack (show actual)
  EmptyList -> "empty list"
  ExpectedAtomGotList exprs -> "Expected an atom, but got list " <> showExpr (ExprList exprs)
  ExpectedListGotAtom atom -> "Expected a list, but got atom «" <> atom <> "»"
  LambdaArityError actual expected ->
    "Arity error in lambda: expected "
      <> Text.pack (show expected)
      <> " argument(s), but got "
      <> Text.pack (show actual)
  MalformedAlternative expr -> "Arity error in alternative: " <> showExpr expr
  MalformedLambda expr -> "Malformed lambda: " <> showExpr expr
  UnboundVariable name -> "Unbound variable «" <> name <> "»"
  UnexpectedExpr expr -> "Unexpected expression: " <> showExpr expr

------------------------------------------------------------------------------------------------------------------------
-- The parser

type P a = P.Parsec Void Text a

parseExpr :: Text -> Either Text Expr
parseExpr s =
  case P.parse pexpr "" s of
    Left err -> Left (Text.pack (P.errorBundlePretty err))
    Right expr -> Right expr

pexpr :: P Expr
pexpr =
  plexeme do
    P.choice
      [ ExprAtom <$> pexprAtom,
        ExprList <$> pexprList
      ]

pexprAtom :: P Text
pexprAtom =
  P.takeWhile1P (Just "atom character") \c ->
    Char.isAlphaNum c
      || (Char.isPunctuation c && c /= '(' && c /= ')')
      || Char.isSymbol c

pexprList :: P [Expr]
pexprList = do
  _ <- psymbol "("
  exprs <- Monad.many pexpr
  _ <- psymbol ")"
  pure exprs

plexeme :: P a -> P a
plexeme =
  L.lexeme pspace

pspace :: P ()
pspace =
  L.space P.space1 P.empty P.empty

psymbol :: Text -> P Text
psymbol =
  L.symbol pspace

------------------------------------------------------------------------------------------------------------------------
-- The printer

printExpr :: Expr -> IO ()
printExpr =
  Text.putStrLn . showExpr

showExpr :: Expr -> Text
showExpr = \case
  ExprAtom s -> s
  ExprList es -> "(" <> Text.unwords (map showExpr es) <> ")"

------------------------------------------------------------------------------------------------------------------------
-- The interactive evaluator

eval :: Text -> IO ()
eval s =
  case parseExpr s of
    Left err -> Text.putStrLn ("Parse error: " <> err)
    Right expr ->
      case runEval (evaluate Map.empty expr) of
        Left (context, err) -> do
          Text.putStrLn ("In context: " <> showContext context)
          Text.putStrLn ("Error: " <> showEvalError err)
        Right expr1 -> printExpr expr1

repl :: IO ()
repl = do
  s <- Text.getLine
  eval s
  repl
