module RootsOfLisp where

import qualified Control.Monad.Combinators as Monad
import qualified Data.Char as Char
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
  | EmptyList
  | ExpectedAtomGotList [Expr]
  | ExpectedListGotAtom Text
  | LambdaArityError Int Int
  | MalformedAlternative Expr
  | MalformedFunction [Expr]
  | UnboundVariable Text

evaluate :: Env -> Expr -> Eval Expr
evaluate env = \case
  ExprAtom var -> evaluateAtom env var
  ExprList [] -> Left EmptyList
  ExprList (ExprAtom name : exprs0) ->
    case name of
      "cond" -> evaluateCond env exprs0
      "quote" ->
        case exprs0 of
          [expr] -> Right expr
          _ -> Left (ArityError "quote" (length exprs0) 1)
      _ -> do
        args <- traverse (evaluate env) exprs0
        case name of
          "atom" ->
            case args of
              [arg] ->
                case arg of
                  ExprAtom _ -> Right ExprTrue
                  _ -> Right ExprFalse
              _ -> Left (ArityError name (length args) 1)
          "car" ->
            case args of
              [arg] ->
                case arg of
                  ExprAtom atom -> Left (ExpectedListGotAtom atom)
                  ExprList [] -> Left CarEmptyList
                  ExprList (expr : _) -> Right expr
              _ -> Left (ArityError name (length args) 1)
          "cdr" ->
            case args of
              [arg] ->
                case arg of
                  ExprAtom atom -> Left (ExpectedListGotAtom atom)
                  ExprList [] -> Left CdrEmptyList
                  ExprList (_ : exprs) -> Right (ExprList exprs)
              _ -> Left (ArityError name (length args) 1)
          "cons" ->
            case args of
              [x, xs0] ->
                case xs0 of
                  ExprAtom atom -> Left (ExpectedListGotAtom atom)
                  ExprList xs -> Right (ExprList (x : xs))
              _ -> Left (ArityError name (length args) 2)
          "eq" ->
            case args of
              [expr1, expr2] ->
                case (expr1, expr2) of
                  (ExprAtom atom1, ExprAtom atom2) | atom1 == atom2 -> Right ExprTrue
                  (ExprList [], ExprList []) -> Right ExprTrue
                  _ -> Right ExprFalse
              _ -> Left (ArityError name (length args) 2)
          _ ->
            case Map.lookup name env of
              Nothing -> Left (UnboundVariable name)
              Just expr -> evaluate env (ExprList (expr : exprs0))
  ExprList (ExprList func : args) -> evaluateFunctionCall env func args

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

evaluateFunctionCall :: Env -> [Expr] -> [Expr] -> Eval Expr
evaluateFunctionCall env func args0 =
  case func of
    [name0, params0, body] ->
      case name0 of
        ExprAtom "lambda" ->
          case params0 of
            ExprAtom atom -> Left (ExpectedListGotAtom atom)
            ExprList params1 ->
              let numParams = length params1
                  numArgs = length args0
               in if numParams == numArgs
                    then do
                      params2 <-
                        for params1 \case
                          ExprAtom param -> pure param
                          -- Should we evaluate this? e.g:
                          --   ((lambda ((quote p1) p2 p3) body) a1 a2 a3)
                          --   ((lambda (p1         p2 p3) body) a1 a2 a3)
                          -- Currently if given (quote p1) as an argument we fail.
                          ExprList exprs -> Left (ExpectedAtomGotList exprs)
                      args <- traverse (evaluate env) args0
                      evaluate (List.foldl' (\acc (param, arg) -> Map.insert param arg acc) env (zip params2 args)) body
                    else Left (LambdaArityError numArgs numParams)
        _ -> do
          name <- evaluate env name0
          evaluateFunctionCall env [name, params0, body] args0
    _ -> Left (MalformedFunction func)

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
  EmptyList -> "()"
  ExpectedAtomGotList exprs -> "Expected an atom, but got list " <> showExpr (ExprList exprs)
  ExpectedListGotAtom atom -> "Expected a list, but got atom «" <> atom <> "»"
  LambdaArityError actual expected ->
    "Arity error in lambda: expected "
      <> Text.pack (show expected)
      <> " argument(s), but got "
      <> Text.pack (show actual)
  MalformedAlternative expr -> "Arity error in alternative: " <> showExpr expr
  MalformedFunction exprs -> "Arity error in function: " <> showExpr (ExprList exprs)
  UnboundVariable name -> "Unbound variable «" <> name <> "»"

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
