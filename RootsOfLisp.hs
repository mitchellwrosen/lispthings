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

type Eval a = Either Expr a

evaluate :: Expr -> Eval Expr
evaluate expr0 =
  case expr0 of
    ExprList (ExprAtom "cond" : alts) ->
      evaluateCond alts >>= \case
        Nothing -> Left expr0
        Just expr -> Right expr
    ExprList [ExprAtom "quote", expr] -> Right expr
    ExprList (ExprAtom name : args0) -> do
      args <- traverse evaluate args0
      case (name, args) of
        ("atom", [arg]) ->
          case arg of
            ExprAtom _ -> Right ExprTrue
            _ -> Right ExprFalse
        ("car", [ExprList (expr : _)]) -> Right expr
        ("cdr", [ExprList (_ : exprs)]) -> Right (ExprList exprs)
        ("cons", [expr, ExprList exprs]) -> Right (ExprList (expr : exprs))
        ("eq", [expr1, expr2]) ->
          case (expr1, expr2) of
            (ExprAtom atom1, ExprAtom atom2) | atom1 == atom2 -> Right ExprTrue
            (ExprList [], ExprList []) -> Right ExprTrue
            _ -> Right ExprFalse
        _ -> Left expr0
    _ -> Left expr0

evaluateCond :: [Expr] -> Eval (Maybe Expr)
evaluateCond = \case
  ExprList [lhs, rhs0] : alts ->
    evaluate lhs >>= \case
      ExprTrue -> do
        rhs <- evaluate rhs0
        Right (Just rhs)
      _ -> evaluateCond alts
  _ -> Right Nothing

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
