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
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.ANSI as Text
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
  ExpectedListGotAtom atom -> "Expected a list, but got atom: " <> atom
  LambdaArityError actual expected ->
    "Arity error in function: expected "
      <> Text.pack (show expected)
      <> " argument(s), but got "
      <> Text.pack (show actual)
  MalformedAlternative expr -> "Arity error in alternative: " <> showExpr expr
  MalformedLambda expr -> "Malformed lambda: " <> showExpr expr
  UnboundVariable name -> "Unbound variable: " <> name
  UnexpectedExpr expr -> "Unexpected expression: " <> showExpr expr

------------------------------------------------------------------------------------------------------------------------
-- The desugarer

desugar :: Expr -> Expr
desugar =
  defun

-- (defun x y z) ==> (label x (lambda y z))
defun :: Expr -> Expr
defun =
  bottomup \case
    ExprList [ExprAtom "defun", expr1, expr2, expr3] ->
      ExprList [ExprAtom "label", expr1, ExprList [ExprAtom "lambda", expr2, expr3]]
    expr -> expr

bottomup :: (Expr -> Expr) -> Expr -> Expr
bottomup f expr =
  case expr of
    ExprAtom _ -> f expr
    ExprList exprs -> f (ExprList (map (bottomup f) exprs))

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
      [ do
          atom <- P.takeWhile1P (Just "atom character") \c ->
            Char.isAlphaNum c
              || (Char.isPunctuation c && c /= '\'' && c /= '(' && c /= ')')
              || Char.isSymbol c
          pure (ExprAtom atom),
        do
          _ <- psymbol "("
          exprs <- Monad.many pexpr
          _ <- psymbol ")"
          pure (ExprList exprs),
        do
          _ <- P.char '\''
          expr <- pexpr
          pure (ExprList [ExprAtom "quote", expr])
      ]

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

eval :: Expr -> (Expr -> IO ()) -> IO ()
eval expr f =
  case runEval (evaluate Map.empty expr) of
    Left (context, err) -> do
      Text.putStrLn ("In context: " <> showContext context)
      Text.putStrLn ("Error: " <> showEvalError err)
    Right expr1 -> f expr1

parse :: Text -> (Expr -> IO ()) -> IO ()
parse s f =
  case parseExpr s of
    Left err -> Text.putStrLn ("Parse error: " <> err)
    Right expr -> f expr

repl :: IO ()
repl = do
  s <- Text.getLine
  Text.putStrLn "\n== parse =="
  parse s \expr0 -> do
    printExpr expr0
    Text.putStrLn "\n== desugar =="
    let expr1 = desugar expr0
    printExpr expr1
    Text.putStrLn "\n== eval =="
    eval expr1 printExpr
    Text.putStrLn "\n== it's zippertime =="
    let loop z = do
          Text.putStrLn (renderz z)
          case step z of
            Nothing -> Text.putStrLn "Evaluation error."
            Just (Left _expr) -> pure ()
            Just (Right z1) -> do
              _ <- getLine
              loop z1
    loop (zippeth expr1)
    Text.putStrLn ""
  repl

------------------------------------------------------------------------------------------------------------------------
-- Zipper experiments

data Z
  = Z Q Ctx

data Q
  = U Expr
  | F [Expr]
  | V Expr

unq :: Q -> Expr
unq = \case
  U expr -> expr
  F exprs -> ExprList exprs
  V expr -> expr

data Ctx
  = Nil
  | Ctx Env [Expr] Ctx [Expr]

ctxenv :: Ctx -> Env
ctxenv = \case
  Nil -> Map.empty
  Ctx env _ _ _ -> env

zippeth :: Expr -> Z
zippeth expr =
  Z (U expr) Nil

unzippeth :: Z -> Expr
unzippeth z =
  case itermay up z of
    Z q _ -> unq q

up :: Z -> Maybe Z
up = \case
  Z _ Nil -> Nothing
  Z q (Ctx _ xs ctx ys) -> Just (Z (U (ExprList (reverse xs ++ [unq q] ++ ys))) ctx)

step :: Z -> Maybe (Either Expr Z)
step (Z q ctx0) =
  case q of
    U expr ->
      case expr of
        ExprAtom atom ->
          case Map.lookup atom (ctxenv ctx0) of
            Nothing ->
              case ctx0 of
                Ctx _ [] _ _ ->
                  if Set.member atom builtin
                    then Just (Right (Z (V expr) ctx0))
                    else Nothing
                _ -> Nothing
            Just expr1 -> Just (Right (Z (U expr1) ctx0))
        ExprList [] -> Nothing
        ExprList (expr1 : exprs1) -> Just (Right (Z (U expr1) (Ctx (ctxenv ctx0) [] ctx0 exprs1)))
    F exprs ->
      case exprs of
        [ExprAtom "atom", expr] ->
          let result =
                case expr of
                  ExprAtom _ -> ExprTrue
                  ExprList _ -> ExprFalse
           in Just (Right (Z (V result) ctx0))
        [ExprAtom "quote", expr] -> Just (Right (Z (V expr) ctx0))
        _ -> error (show exprs)
    V expr ->
      case ctx0 of
        Nil -> Just (Left expr)
        Ctx env xs pctx ys ->
          case (xs, expr) of
            ([], ExprAtom "quote") -> Just (Right (Z (F (expr : ys)) pctx))
            _ ->
              case ys of
                [] -> Just (Right (Z (F (reverse (expr : xs))) pctx))
                z : zs -> Just (Right (Z (U z) (Ctx env (expr : xs) pctx zs)))
  where
    builtin :: Set Text
    builtin =
      Set.fromList
        ["atom", "car", "cdr", "cond", "eq", "label", "lambda", "quote"]

renderz :: Z -> Text
renderz (Z q ctx0) =
  let color =
        case q of
          U _ -> Text.red
          F _ -> Text.magenta
          V _ -> Text.blue
   in go (color (showExpr (unq q))) ctx0
  where
    go expr = \case
      Nil -> expr
      Ctx env xs ctx ys ->
        let expr1 = "(" <> Text.unwords (map showExpr (reverse xs) ++ [expr] ++ map showExpr ys) <> ")"
         in go expr1 ctx

itermay :: (a -> Maybe a) -> a -> a
itermay f x =
  case f x of
    Nothing -> x
    Just y -> itermay f y
