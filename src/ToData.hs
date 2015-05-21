{-|
Module      : RCore.ToData
-}
module ToData where

import Ast

-- import Debug.Trace

nils :: Int -> Val
nils n = foldr Cons Nil $ replicate n Nil

class ToData a where
    todata :: a -> Val

todataIdent :: Ident -> Val
todataIdent ('X':i) = var (nils (read i))
    where var e = Cons (Atom "var") e
todataIdent _ = error "impossible happened in RCore.ToData.Ident.todata"

instance ToData Program where
    todata (PDefs _ xi cs xj) = 
        Cons (todataIdent xi) (Cons (todata cs) (todataIdent xj))

instance ToData a => ToData [a] where
    todata [] = todata (SAss "X0" (AVal Nil)) -- dummy
    todata cs = foldr1 (\x y -> Cons (Atom "seq") (Cons x y)) (map todata cs)

instance ToData Cmd where
    todata (SAss xi e) = Cons (Atom "xoreq") (Cons (todataIdent xi) (todata e))
    todata (SRep q r) = Cons (Atom "rep") (Cons (todata q) (todata r))
    todata (SCond xi cs ds xj) =
        Cons (Atom "cond") (foldr1 Cons [todata xi, todata cs, todata ds, todata xj])
    todata (SLoop xi cs ds xj) =
        Cons (Atom "loop") (foldr1 Cons [todata xi, todata cs, todata ds, todata xj])

instance ToData Exp where
    todata (AVar xi)     = todataIdent xi
    todata (AVal Nil)    = Atom "nil"
    todata (AVal v)      = Cons (Atom "val") v
    todata (ACons xi xj) = Cons (Atom "cons") (foldr1 Cons [todata xi, todata xj])
    todata (AHd xi)      = Cons (Atom "hd") (todata xi)
    todata (ATl xi)      = Cons (Atom "tl") (todata xi)
    todata (AEq xi xj)   = Cons (Atom "eq") (Cons (todata xi) (todata xj))
