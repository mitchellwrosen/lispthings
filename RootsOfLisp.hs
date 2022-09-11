module RootsOfLisp where

import Data.Text (Text)

data Expr
  = ExprAtom Text
  | ExprPrim Prim
  | ExprList [Expr]
  deriving stock (Eq, Ord, Show)

pattern ExprOpAtom :: Expr -> Expr
pattern ExprOpAtom e = ExprList [ExprPrim PrimAtom, e]

pattern ExprOpCar :: Expr -> Expr
pattern ExprOpCar e = ExprList [ExprPrim PrimCar, e]

pattern ExprOpCdr :: Expr -> Expr
pattern ExprOpCdr e = ExprList [ExprPrim PrimCdr, e]

pattern ExprOpCond :: [(Expr, Expr)] -> Expr
pattern ExprOpCond es <- ExprList (ExprPrim PrimCond : (traverse uncond -> Just es))

uncond :: Expr -> Maybe (Expr, Expr)
uncond = \case
  ExprList [e1, e2] -> Just (e1, e2)
  _ -> Nothing

pattern ExprOpCons :: Expr -> Expr -> Expr
pattern ExprOpCons e1 e2 = ExprList [ExprPrim PrimCons, e1, e2]

pattern ExprOpEq :: Expr -> Expr -> Expr
pattern ExprOpEq e1 e2 = ExprList [ExprPrim PrimEq, e1, e2]

pattern ExprOpQuote :: Expr -> Expr
pattern ExprOpQuote e = ExprList [ExprPrim PrimQuote, e]

pattern ExprFalse :: Expr
pattern ExprFalse = ExprList []

pattern ExprTrue :: Expr
pattern ExprTrue = ExprAtom "t"

data Prim
  = PrimAtom
  | PrimCar
  | PrimCdr
  | PrimCond
  | PrimCons
  | PrimEq
  | PrimQuote
  deriving stock (Eq, Ord, Show)

evaluate :: Expr -> Expr
evaluate = \case
  ExprOpAtom e ->
    case evaluate e of
      ExprAtom _ -> ExprTrue
      _ -> ExprFalse
  ExprOpCar (evaluate -> ExprList (e : _)) -> e
  ExprOpCdr (evaluate -> ExprList (_ : es)) -> ExprList es
  ExprOpCond (evaluateCond -> Just e) -> e
  ExprOpCons e (evaluate -> ExprList es) -> ExprList (evaluate e : es)
  ExprOpEq e1 e2 ->
    case (evaluate e1, evaluate e2) of
      (ExprAtom s1, ExprAtom s2) | s1 == s2 -> ExprTrue
      (ExprList [], ExprList []) -> ExprTrue
      _ -> ExprFalse
  ExprOpQuote e -> e
  e -> error ("bad expression: " ++ show e)

evaluateCond :: [(Expr, Expr)] -> Maybe Expr
evaluateCond = \case
  [] -> Nothing
  (p, e) : es ->
    case evaluate p of
      ExprTrue -> Just (evaluate e)
      _ -> evaluateCond es
