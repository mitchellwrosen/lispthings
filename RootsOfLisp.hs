module RootsOfLisp where

import qualified Control.Monad.Combinators as Monad
import qualified Data.Char as Char
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.IO as Text
import Data.Void (Void)
import qualified Text.Megaparsec as P
import qualified Text.Megaparsec.Char as P
import qualified Text.Megaparsec.Char.Lexer as L

data Expr
  = ExprAtom Text
  | ExprList [Expr]
  deriving stock (Eq, Ord, Show)

pattern ExprFalse :: Expr
pattern ExprFalse = ExprList []

pattern ExprTrue :: Expr
pattern ExprTrue = ExprAtom "t"

pattern ExprOpAtom :: Expr -> Expr
pattern ExprOpAtom e = ExprList [ExprAtom "atom", e]

pattern ExprOpCar :: Expr -> Expr
pattern ExprOpCar e = ExprList [ExprAtom "car", e]

pattern ExprOpCdr :: Expr -> Expr
pattern ExprOpCdr e = ExprList [ExprAtom "cdr", e]

pattern ExprOpCond :: [(Expr, Expr)] -> Expr
pattern ExprOpCond es <- ExprList (ExprAtom "cond" : (traverse uncond -> Just es))

uncond :: Expr -> Maybe (Expr, Expr)
uncond = \case
  ExprList [e1, e2] -> Just (e1, e2)
  _ -> Nothing

pattern ExprOpCons :: Expr -> Expr -> Expr
pattern ExprOpCons e1 e2 = ExprList [ExprAtom "cons", e1, e2]

pattern ExprOpEq :: Expr -> Expr -> Expr
pattern ExprOpEq e1 e2 = ExprList [ExprAtom "eq", e1, e2]

pattern ExprOpQuote :: Expr -> Expr
pattern ExprOpQuote e = ExprList [ExprAtom "quote", e]

type Eval a = Either Expr a

evaluate :: Expr -> Eval Expr
evaluate = \case
  ExprOpAtom e ->
    evaluate e >>= \case
      ExprAtom _ -> Right ExprTrue
      _ -> Right ExprFalse
  ExprOpCar (evaluate -> Right (ExprList (e : _))) -> Right e
  ExprOpCdr (evaluate -> Right (ExprList (_ : es))) -> Right (ExprList es)
  expr@(ExprOpCond es) ->
    evaluateCond es >>= \case
      Nothing -> Left expr
      Just e -> Right e
  ExprOpCons e0 (evaluate -> Right (ExprList es)) -> do
    e <- evaluate e0
    Right (ExprList (e : es))
  ExprOpEq u1 u2 -> do
    e1 <- evaluate u1
    e2 <- evaluate u2
    case (e1, e2) of
      (ExprAtom s1, ExprAtom s2) | s1 == s2 -> Right ExprTrue
      (ExprList [], ExprList []) -> Right ExprTrue
      _ -> Right ExprFalse
  ExprOpQuote e -> Right e
  e -> Left e

evaluateCond :: [(Expr, Expr)] -> Eval (Maybe Expr)
evaluateCond = \case
  [] -> Right Nothing
  (p, u) : es ->
    evaluate p >>= \case
      ExprTrue -> do
        e <- evaluate u
        Right (Just e)
      _ -> evaluateCond es

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
      case evaluate expr of
        Left expr1 -> Text.putStrLn ("Bad expression: " <> showExpr expr1)
        Right expr1 -> printExpr expr1
