{-# OPTIONS_GHC -XMultiParamTypeClasses #-}
{-|
Module      : Trans
-}
module Trans where

import Ast
import Invert

-- import Debug.Trace

-- d _ = [] -- for debug
d x = x -- for debug

nils :: Int -> Val
nils n = foldr Cons Nil $ replicate n Nil

trans :: Program -> Program
trans p = reduceProgram $ 
          alpha $ 
          trans' p

trans' :: Program -> Program
trans' p@(PDefs ps x cs y) =
  PDefs ps x (concatMap (transCmd namesupply) cs) y -- psを修正する必要有り
    where n = length $ vars p
          namesupply = map (('_':) . show) [(n+2)..]

reduceProgram :: Program -> Program
reduceProgram p@(PDefs ps ('_':xi) cs ('_':xj)) = 
  PDefs ps
        l_z                     -- psを修正する必要有り
          ([SAss vl (AVal (nils n))] ++
           updateM i (AVar l_z) ++
           lookupM i l_z ++ 
           d [SAssert "reduceProgram 1" (AEq (AVar l_z) (AVal Nil))] ++
           concatMap reduce cs ++
           d [SAssert "reduceProgram 2" (AEq (AVar l_z) (AVal Nil))] ++
           lookupM j l_z ++ 
           updateM j (AVar l_z) ++
           [SAss vl (AVal (nils n))])
          l_z
    where n = length (vars p) + 2
          i = read xi :: Int
          j = read xj :: Int

-- reduce the number of variables
reduce :: Cmd -> [Cmd]
reduce (SAss ('_':xi) (AVar ('_':xj))) =
  d [SAssert "reduce 1-1" (AEq (AVar l_y) (AVal Nil))] ++
  lookupM j l_y ++ updateM i (AVar l_y) ++ lookupM j l_y ++
  d [SAssert "reduce 1-2" (AEq (AVar l_y) (AVal Nil))]
    where i = read xi :: Int
          j = read xj :: Int
reduce (SAss ('_':xi) e@(AVal _)) = updateM i e
    where i = read xi :: Int
reduce (SAss ('_':xi) (ACons (AVar ('_':xj)) (AVar ('_':xk)))) =
  d [SAssert "reduce 1" (AEq (AVar l_y) (AVal Nil)), 
     SAssert "reduce 2" (AEq (AVar l_z) (AVal Nil))] ++
  lookupM j l_y ++ lookupM k l_z ++
  updateM i (ACons (AVar l_y) (AVar l_z)) ++
  lookupM k l_z ++ lookupM j l_y ++
  d [SAssert "reduce 3" (AEq (AVar l_y) (AVal Nil)), 
     SAssert "reduce 4" (AEq (AVar l_z) (AVal Nil))]
    where i = read xi :: Int
          j = read xj :: Int
          k = read xk :: Int
reduce (SAss ('_':xi) (AHd (AVar ('_':xj)))) =
  d [SAssert "reduce 4-1" (AEq (AVar l_y) (AVal Nil))] ++
  lookupM j l_y ++ updateM i (AHd (AVar l_y)) ++ lookupM j l_y ++
  d [SAssert "reduce 4-2" (AEq (AVar l_y) (AVal Nil))]
    where i = read xi :: Int
          j = read xj :: Int
reduce (SAss ('_':xi) (ATl (AVar ('_':xj)))) =
  d [SAssert "reduce 5-1" (AEq (AVar l_y) (AVal Nil))] ++
  lookupM j l_y ++ updateM i (ATl (AVar l_y)) ++ lookupM j l_y ++
  d [SAssert "reduce 5-2" (AEq (AVar l_y) (AVal Nil))]
    where i = read xi :: Int
          j = read xj :: Int
reduce (SAss ('_':xi) (AEq (AVar ('_':xj)) (AVar ('_':xk)))) =
  d [SAssert "reduce 6-1" (AEq (AVar l_y) (AVal Nil)),
     SAssert "reduce 6-1b" (AEq (AVar l_z) (AVal Nil))] ++
  lookupM j l_y ++ lookupM k l_z ++ 
  updateM i (AEq (AVar l_y) (AVar l_z)) ++
  lookupM k l_z ++ lookupM j l_y ++
  d [SAssert "reduce 6-2" (AEq (AVar l_y) (AVal Nil)), 
     SAssert "reduce 6-2b" (AEq (AVar l_z) (AVal Nil))]
    where i = read xi :: Int
          j = read xj :: Int
          k = read xk :: Int
reduce (SCond (AVar ('_':xj)) cs ds (AVar ('_':xk))) =
  d [SAssert "reduce 11-1" (AEq (AVar l_y) (AVal Nil))] ++
  lookupM j l_y ++
  [SCond (AVar l_y)
         (lookupM j l_y ++ 
          d [SAssert "reduce 11-2" (AEq (AVar l_y) (AVal Nil))] ++
          concatMap reduce cs ++ 
          d [SAssert "reduce 11-3" (AEq (AVar l_y) (AVal Nil))] ++
          lookupM k l_y)
         (lookupM j l_y ++ 
          d [SAssert "reduce 11-4" (AEq (AVar l_y) (AVal Nil))] ++
          concatMap reduce ds ++ 
          d [SAssert "reduce 11-5" (AEq (AVar l_y) (AVal Nil))] ++
          lookupM k l_y)
         (AVar l_y)] ++
  lookupM k l_y ++
  d [SAssert "reduce 11-6" (AEq (AVar l_y) (AVal Nil))]
    where j = read xj :: Int
          k = read xk :: Int
reduce (SLoop (AVar ('_':xj)) cs ds (AVar ('_':xk))) =
  d [SAssert "reduce 7-1" (AEq (AVar l_y) (AVal Nil))] ++
  lookupM j l_y ++
  [SLoop (AVar l_y)
         (lookupM j l_y ++ 
          d [SAssert "reduce 9-1" (AEq (AVar l_y) (AVal Nil))] ++
          concatMap reduce cs ++ 
          d [SAssert "reduce 10-1" (AEq (AVar l_y) (AVal Nil))] ++
          lookupM k l_y)
         (lookupM k l_y ++ 
          d [SAssert "reduce 9-1" (AEq (AVar l_y) (AVal Nil))] ++
          concatMap reduce ds ++ 
          d [SAssert "reduce 10-1" (AEq (AVar l_y) (AVal Nil))] ++
          lookupM j l_y)
         (AVar l_y)] ++
  lookupM k l_y ++
  d [SAssert "reduce 8-1" (AEq (AVar l_y) (AVal Nil))]
    where j = read xj :: Int
          k = read xk :: Int
reduce (SLookup (AVar ('_':xi)) ('_':xj)) = 
    lookupM i l_y ++ updateM j (AVar l_y) ++ lookupM i l_y ++
    [SAssert "reduce slookup" (AEq (AVar l_y) (AVal Nil))]
    -- lookupM i l_y ++ updateM i (AVar l_y) ++ lookupM j l_y ++ updateM i (AVar l_y) ++ lookupM i l_y
    -- d [SAssert "reduce slookup-1" (AEq (AVar l_y) (AVal Nil))] ++
    -- lookupM i l_y ++ [SLookup (AVar l_y) l_z] ++
    -- updateM j (AVar l_x) ++ [SLookup (AVar l_x) l_w] ++
    -- [SUpdate (AVar l_z) (AVar l_w)] ++
    -- [SLookup (AVar l_x) l_w] ++  updateM j (AVar l_x) ++
    -- [SLookup (AVar l_y) l_z] ++ lookupM i l_y ++
    -- d [SAssert "reduce slookup-2" (AEq (AVar l_y) (AVal Nil))]
  where i = read xi :: Int
        j = read xj :: Int
reduce (SUpdate (AVar ('_':xi)) (AVar ('_':xj))) =
    lookupM j l_y ++ updateM i (AVar l_y) ++ lookupM j l_y
  where i = read xi :: Int
        j = read xj :: Int
reduce (SAssert str e) = []
reduce (SShow str) = [SShow str]
reduce cmd = error $ "in RWhile.Trans.reduce: " ++ show cmd

-- U, V, K, T, Vr are nil
lookupM :: Int -> Ident -> [Cmd]
lookupM j x = [SLookup (AVal (nils j)) x] -- code ++ [SAss x (AVar l_t1)] ++ invert code
  where code = aux j

updateM :: Int -> Exp -> [Cmd]
updateM j e = [SUpdate (AVal (nils j)) e] -- code ++ [SAss l_t1 e] ++ invert code
  where code = aux j

aux :: Int -> [Cmd]
aux j = d [SAssert "aux 1" (AEq (AVar l_jj) (AVal Nil)),
           SAssert "aux 2" (AEq (AVar l_t2) (AVal Nil)),
           SAssert "aux 3" (AEq (AVar l_t3) (AVal Nil)),
           SAssert "aux 4" (AEq (AVar l_t4) (AVal Nil)),
           SAssert "aux 5" (AEq (AVar l_vr) (AVal Nil)),
           SAssert "aux 6" (AEq (AVar l_nil) (AVal Nil))] ++
        set_uv j ++ [loop] ++ invert (set_uv j) ++ 
        [SRep (ACons (AVar l_t1) (AVar l_t2)) (AVar vl)] ++
        d [SAssert "aux 5-b" (AVar vl)] -- vl is non-empty
  where loop = SLoop (AVar l_t2)
                     []
                     (invert (set_uv j) ++
                      [ SRep (ACons (AVar l_t4) (AVar vl)) (AVar vl)
                      , SRep (AVar l_vr) (ACons (AVar l_t4) (AVar l_vr))
                      , SRep (AVar l_jj) (ACons (AVar l_nil) (AVar l_jj)) ] ++
                      set_uv j)
                     (AVar l_t3)

set_uv :: Int -> [Cmd]
set_uv j =
  d [SAssert "set_uv 1" (AEq (AVar l_t2) (AVal Nil)),
     SAssert "set_uv 2" (AEq (AVar l_t3) (AVal Nil)),
     SAssert "set_uv 3" (AEq (AVar l_t4) (AVal Nil)) ] ++
  [SAss l_t2 (AEq (AVar l_jj) (AVar l_nil)),
   SAss l_t4 (AVal (nils j)),
   SAss l_t3 (AEq (AVar l_jj) (AVar l_t4)),
   SAss l_t4 (AVal (nils j))] ++
  d [SAssert "set_uv 4" (AEq (AVar l_t4) (AVal Nil))]

vl    = "X0"
l_nil = "X1"
l_jj  = "X2"
l_t1  = "X3"
l_t2  = "X4"
l_t3  = "X5"
l_t4  = "X6"
l_vr  = "X7"
l_y   = "X8"
l_z   = "X9"
l_x   = "X10"
l_w   = "X11"


-- ----------------------------------------------------------------------

nil = AVar "_1"
true  = ACons nil nil
false = nil
isTrue x@(AVal Nil) = x
isTrue x@(AVal (Cons Nil Nil)) = x
isTrue e = AEq nil (AEq nil e)

transCmd :: [Ident] -> Cmd -> [Cmd]
transCmd ns (SRep q r) = snd (transRep ns q r)
transCmd ns (SAss xi e) = snd (transAsn ns xi e)
transCmd ns@(x:ms) (SCond e cs ds f) =
  let s_e = transCmd ms (SAss x e)
      s_f = transCmd ms (SAss x f) in
  s_e ++ [SCond (AVar x)
                (invert s_e ++ concatMap (transCmd ns) cs ++ s_f)
                (invert s_e ++ concatMap (transCmd ns) ds ++ s_f)
                (AVar x)] ++
  invert s_f
transCmd ns@(x:ms) (SLoop e cs ds f) =
  let s_e = transCmd ms (SAss x e)
      s_f = transCmd ms (SAss x f) in
  s_e ++ [SLoop (AVar x)
                (invert s_e ++ concatMap (transCmd ns) cs ++ s_f)
                (invert s_f ++ concatMap (transCmd ns) ds ++ s_e)
                (AVar x)] ++
  invert s_f
transCmd (x:y:ns) (SUpdate e f) =
    let s_e = transCmd ns (SAss x e)
        s_f = transCmd ns (SAss y f)
    in s_e ++ s_f ++ [SUpdate (AVar x) (AVar y)] ++ invert s_f ++ invert s_e
transCmd (x:ns) (SLookup e z) =
    let s_e = transCmd ns (SAss x e)
    in s_e ++ [SLookup (AVar x) z] ++ invert s_e

transAsn :: [Ident] -> Ident -> Exp -> ([Ident],[Cmd])
-- transAsn ns x e | traceShow e False = undefined
-- transAsn ns x y@(AVar _) = (ns, [SAss x y])
-- transAsn ns x e@(AVal _) = (ns, [SAss x e])
-- transAsn ns x e@(ACons (AVal Nil) (AVal Nil)) = (ns, [SAss x (AVal (Cons Nil Nil))])
-- transAsn ns x e@(ACons (AVar "_1") (AVar "_1")) = (ns, [SAss x e])
-- transAsn ns x (AEq e f) | e == f = (ns, [SAss x (AVal (Cons Nil Nil))])
-- transAsn (y:ns) x (AEq e (AVar "_1")) = 
--   (ns, code ++ [SAss x (AEq (AVar y) nil)] ++ invert code)
--   where (_,code) = transAsn ns y e
-- transAsn (y:ns) x (AEq e (AVal Nil)) = 
--   (ns, code ++ [SAss x (AEq (AVar y) nil)] ++ invert code)
--   where (_,code) = transAsn ns y e
-- transAsn (y:ns) x (AEq (AVar "_1") f) = 
--   (ns, code ++ [SAss x (AEq nil (AVar y))] ++ invert code)
--   where (_,code) = transAsn ns y f
-- transAsn (y:ns) x (AEq (AVal Nil) f) = 
--   (ns, code ++ [SAss x (AEq nil (AVar y))] ++ invert code)
--   where (_,code) = transAsn ns y f
-- transAsn ns x e@(AEq (AVar _) (AVar _)) = (ns, [SAss x e])
-- transAsn (y:ns) x (AEq e f@(AVar _)) =
--   (ns', code ++ [SAss x (AEq (AVar y) f)] ++ invert code)
--   where (ns',code) = transAsn' ns y e
-- transAsn (y:ns) x (AEq e@(AVar _) f) =
--   (ns', code ++ [SAss x (AEq e (AVar y))] ++ invert code)
--   where (ns',code) = transAsn' ns y e
-- transAsn (y:z:ns) x (AEq e f) =
--   (ns2, code ++ [SAss x (AEq (AVar y) (AVar z))] ++ invert code)
--   where (ns1,code1) = transAsn' ns  y e
--         (ns2,code2) = transAsn' ns1 z f
--         code = code1 ++ code2
-- transAsn ns x e@(AHd (AVar _)) = (ns, [SAss x e])
-- transAsn (y:ns) x (AHd (AVal Nil)) = (ns, [SAss x (AHd nil)])
-- transAsn (y:ns) x (AHd e) = (ns, code ++ [SAss x (AHd (AVar y))] ++ invert code)
--   where (ns1,code) = transAsn' ns y e
-- transAsn ns x e@(ATl (AVar _)) = (ns, [SAss x e])
-- transAsn (y:ns) x (ATl e) = (ns, code ++ [SAssert "transAsn 1" (AVar y), SAss x (ATl (AVar y))] ++ invert code)
--   where (ns1,code) = transAsn' ns y e
transAsn (y:ns) x e = (ns1, code ++ [SAss x (AVar y)] ++ invert code)
  where (ns1,code) = transAsn' ns y e

transAsn' :: [Ident] -> Ident -> Exp -> ([Ident],[Cmd])
transAsn' ns x xj@(AVar _) = (ns,[SAss x xj])
transAsn' ns x d@(AVal _) = (ns, [SAss x d])
-- transAsn' (y:ns) x (ACons (AVal Nil) f) =
--   let (ns', cs) = transAsn' ns y f
--   in (ns', cs ++ [SAss x (ACons nil (AVar y))])
-- transAsn' (y:ns) x (ACons e (AVal Nil)) = 
--   let (ns', cs) = transAsn' ns y e
--   in (ns', cs ++ [SAss x (ACons (AVar y) nil)])
transAsn' (y:z:ns) x (ACons e f) = 
  let (ns1, cs1) = transAsn' ns  y e
      (ns2, cs2) = transAsn' ns1 z f
  in (ns2, cs1 ++ cs2 ++ [SAss x (ACons (AVar y) (AVar z))])
-- transAsn' ns x e@(AHd (AVal Nil)) = (ns, [SAss x (AHd nil)])
transAsn' ns x e@(AHd (AVar _)) = (ns, [SAss x e])
transAsn' (y:ns) x (AHd e) =
  let (ns1, cs1) = transAsn' ns y e
  in (ns1, cs1 ++ [SAss x (AHd (AVar y))])
-- transAsn' (y:ns) x e@(ATl (AVal Nil)) = (ns, [SAss x (ATl nil)])
-- transAsn' ns x e@(ATl (AVar _)) = (ns, [SAss x e])
transAsn' (y:ns) x (ATl e) =
  let (ns1, cs1) = transAsn' ns y e
  in (ns1, cs1 ++ [SAss x (ATl (AVar y))])
-- transAsn' (y:ns) x (AEq e (AVal Nil)) =
--   let (ns1, cs) = transAsn' ns y e
--   in (ns1, cs ++ [SAss x (AEq (AVar y) nil)])
-- transAsn' (y:ns) x (AEq e (AVar "_1")) = 
--   let (ns1, cs) = transAsn' ns y e
--   in (ns1, cs ++ [SAss x (AEq (AVar y) nil)])
-- transAsn' (y:ns) x (AEq (AVal Nil) f) =
--   let (ns1, cs) = transAsn' ns y f
--   in (ns1, cs ++ [SAss x (AEq nil (AVar y))])
-- transAsn' (y:ns) x (AEq (AVar "_1") f) =
--   let (ns1, cs) = transAsn' ns y f
--   in (ns1, cs ++ [SAss x (AEq nil (AVar y))])
transAsn' (y:z:ns) x (AEq e f) = 
  let (ns1, cs1) = transAsn' ns  y e
      (ns2, cs2) = transAsn' ns1 z f
  in (ns2, cs1 ++ cs2 ++ [SAss x (AEq (AVar y) (AVar z))])

transRep :: [Ident] -> Exp -> Exp -> ([Ident],[Cmd])
transRep (y:ns) q r = 
  let (_,cs1) = transAsn  ns y r        -- set variable y
      (_,cs2) = transRep' ns r (AVar y) -- clear variables in r
      (_,cs3) = transRep' ns q (AVar y) -- set variables in q
      (_,cs4) = transAsn  ns y q        -- clear variable y
  in (ns, cs1 ++ cs2 ++ cs3 ++ cs4)

transRep' :: [Ident] -> Exp -> Exp -> ([Ident],[Cmd])
transRep' ns (AVar x) e = transAsn ns x e
transRep' (y:ns) d@(AVal _) e =
  let (_,cs1) = transAsn ns y (AEq d e)
  in (ns, cs1 ++ [SLoop (AVar y) [] [] (AVar y), SAss y true])
transRep' ns (ACons q1 q2) e =
  let (_,cs1) = transRep' ns q1 (AHd e)
      (_,cs2) = transRep' ns q2 (ATl e)
  in (ns, cs1 ++ cs2)
transRep' ns q r = error $ "impossible happened in Trans.transRep': " ++ show q ++ ", " ++ show r

-- |Alpha renaming
class Renaming a where
    alpha :: a -> a

instance Renaming Program where
    alpha p = let vs = vars p in 
              subst (zip vs (map (\n -> '_' : show n) [2..])) p

instance Renaming Cmd where
    alpha cmd = let vs = vars cmd in 
                subst (zip vs (map (\n -> '_' : show n) [2..])) cmd
