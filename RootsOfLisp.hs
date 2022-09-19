module RootsOfLisp where

import Control.Monad (guard)
import qualified Control.Monad.Combinators as Monad
import qualified Data.Char as Char
import Data.Containers.ListUtils (nubOrd)
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

type Eval a = Either EvalError a

data EvalError
  = ArityError Text Int Int
  | CarEmptyList
  | CdrEmptyList
  | DuplicateParameters Expr
  | ExpectedAtomGotList [Expr]
  | ExpectedListGotAtom Text
  | LambdaArityError Int Int
  | MalformedAlternative Expr
  | MalformedLambda Expr
  | UnboundVariable Text
  | UnexpectedExpr Expr

evaluate :: Env -> Expr -> Eval Expr
evaluate env = \case
  -- x
  ExprAtom var -> evaluateAtom env var
  ExprList (ExprAtom name : exprs0) ->
    case name of
      -- (atom ...)
      "atom" ->
        case exprs0 of
          [arg] ->
            evaluate env arg >>= \case
              ExprAtom _ -> Right ExprTrue
              _ -> Right ExprFalse
          _ -> Left (ArityError name (length exprs0) 1)
      -- (car ...)
      "car" ->
        case exprs0 of
          [arg] ->
            evaluate env arg >>= \case
              ExprAtom atom -> Left (ExpectedListGotAtom atom)
              ExprList [] -> Left CarEmptyList
              ExprList (expr : _) -> Right expr
          _ -> Left (ArityError name (length exprs0) 1)
      -- (cdr ...)
      "cdr" ->
        case exprs0 of
          [arg] ->
            evaluate env arg >>= \case
              ExprAtom atom -> Left (ExpectedListGotAtom atom)
              ExprList [] -> Left CdrEmptyList
              ExprList (_ : exprs) -> Right (ExprList exprs)
          _ -> Left (ArityError name (length exprs0) 1)
      -- (cond ...)
      "cond" -> evaluateCond env exprs0
      -- (cons ...)
      "cons" ->
        case exprs0 of
          [x0, xs0] -> do
            x <- evaluate env x0
            xs1 <- evaluate env xs0
            case xs1 of
              ExprAtom atom -> Left (ExpectedListGotAtom atom)
              ExprList xs2 -> Right (ExprList (x : xs2))
          _ -> Left (ArityError name (length exprs0) 2)
      -- (eq ...)
      "eq" ->
        case exprs0 of
          [expr01, expr02] -> do
            expr1 <- evaluate env expr01
            expr2 <- evaluate env expr02
            case (expr1, expr2) of
              (ExprAtom atom1, ExprAtom atom2) | atom1 == atom2 -> Right ExprTrue
              (ExprList [], ExprList []) -> Right ExprTrue
              _ -> Right ExprFalse
          _ -> Left (ArityError name (length exprs0) 2)
      "quote" ->
        case exprs0 of
          [expr] -> Right expr
          _ -> Left (ArityError "quote" (length exprs0) 1)
      -- (x ...)
      _ ->
        case Map.lookup name env of
          Nothing -> Left (UnboundVariable name)
          Just expr -> evaluate env (ExprList (expr : exprs0))
  -- ((label ...) ...)
  ExprList (lambda@(ExprList ((ExprAtom "label" : labelAndLambda))) : args0) ->
    case labelAndLambda of
      [ ExprAtom label,
        ExprList [ExprAtom "lambda", matchParams -> Just (params, numParams), body]
        ]
          | label `notElem` params ->
              let numArgs = length args0
               in if numParams == numArgs
                    then do
                      args <- traverse (evaluate env) args0
                      let env1 =
                            List.foldl'
                              (\acc (param, arg) -> Map.insert param arg acc)
                              (Map.insert label lambda env)
                              (zip params args)
                      evaluate env1 body
                    else Left (LambdaArityError numArgs numParams)
      _ -> Left (MalformedLambda lambda)
  -- ((lambda ...) ...)
  ExprList (lambda@(ExprList (ExprAtom "lambda" : paramsAndBody)) : args0) ->
    case paramsAndBody of
      [matchParams -> Just (params, numParams), body] ->
        let numArgs = length args0
         in if numParams == numArgs
              then do
                args <- traverse (evaluate env) args0
                let env1 = List.foldl' (\acc (param, arg) -> Map.insert param arg acc) env (zip params args)
                evaluate env1 body
              else Left (LambdaArityError numArgs numParams)
      _ -> Left (MalformedLambda lambda)
  expr -> Left (UnexpectedExpr expr)

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

evaluateAtom :: Env -> Text -> Eval Expr
evaluateAtom env var =
  case Map.lookup var env of
    Nothing -> Left (UnboundVariable var)
    Just expr -> Right expr

evaluateCond :: Env -> [Expr] -> Eval Expr
evaluateCond env = \case
  [] -> undefined
  alt : alts ->
    case alt of
      ExprList [lhs, rhs0] ->
        evaluate env lhs >>= \case
          ExprTrue -> evaluate env rhs0
          _ -> evaluateCond env alts
      _ -> Left (MalformedAlternative alt)

showEvalError :: EvalError -> Text
showEvalError = \case
  ArityError name actual expected ->
    "Arity error in function «"
      <> name
      <> "»: expected "
      <> Text.pack (show expected)
      <> " argument(s), but got "
      <> Text.pack (show actual)
  CarEmptyList -> "car: ()"
  CdrEmptyList -> "cdr: ()"
  DuplicateParameters expr -> "Duplicate parameters in lambda: " <> showExpr expr
  ExpectedAtomGotList exprs -> "Expected an atom, but got list " <> showExpr (ExprList exprs)
  ExpectedListGotAtom atom -> "Expected a list, but got atom «" <> atom <> "»"
  LambdaArityError actual expected ->
    "Arity error in lambda: expected "
      <> Text.pack (show expected)
      <> " argument(s), but got "
      <> Text.pack (show actual)
  MalformedAlternative expr -> "Arity error in alternative: " <> showExpr expr
  MalformedLambda expr -> "Arity error in lambda: " <> showExpr expr
  UnboundVariable name -> "Unbound variable «" <> name <> "»"
  UnexpectedExpr expr -> "Unexpected expr: " <> showExpr expr

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
      case evaluate Map.empty expr of
        Left err -> Text.putStrLn ("Error: " <> showEvalError err)
        Right expr1 -> printExpr expr1

repl :: IO ()
repl = do
  s <- Text.getLine
  eval s
  repl
