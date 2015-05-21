{-|
Module      : Eval
-}
module Eval where

import Ast
import Invert
import Text.PrettyPrint
import Data.List (intersect, nub)

import Debug.Trace

lookupEnv :: Ident -> Env -> Val
lookupEnv x ev = case lookup x ev of
                   Nothing -> error ("in lookupEnv: Variable " ++ x ++ " not found\n" ++
                                     render (prettyEnv ev))
                   Just v -> v

update :: Ident -> Val -> Env -> Env
update x v []           = error ("in update: Variable " ++ x ++ " is not found")
update z v ((y,w) : ev) = if z == y then (y,v) : ev
                                    else (y,w) : update z v ev

minus :: Env -> Ident -> Env
ev `minus` x = filter (\ (y,_) -> y /= x) ev

initEnv :: [Ident] -> Env
initEnv = map (\z -> (z,Nil))

-- |Evaluator
eval :: [Proc] -> Env -> Exp -> Val
eval ps ev (AVar x) = lookupEnv x ev
eval ps _  (AVal v) = v
eval ps ev (ACons e f) = Cons (eval ps ev e) (eval ps ev f)
eval ps ev (AHd e) = case eval ps ev e of
                       Cons v _ -> v
                       Atom _   -> error ("RWhileWM.Eval.eval hd atom: " ++ show (AHd e) ++ "\n" ++ show ev)
                       Nil      -> error ("RWhileWM.Eval.eval hd nil: "  ++ show (AHd e) ++ "\n" ++ show ev)
eval ps ev (ATl f) = case eval ps ev f of
                       Cons _ v -> v
                       Atom _   -> error ("in RWhileWM.Eval.eval tl nil: " ++ show f ++ ":" ++ show ev)
                       Nil      -> error ("in RWhileWM.Eval.eval tl nil: " ++ show f ++ ":" ++ show ev)
eval ps ev (AEq e f) = if v1 == v2 then Cons Nil Nil else Nil
    where v1 = eval ps ev e
          v2 = eval ps ev f


-- |Execution of commands
exec :: [Proc] -> Env -> Cmd -> Env
-- exec ps ev c | traceShow (pretty c,prettyEnv ev) False = undefined
-- exec ps ev c | traceShow ("exec: " ++ show c) False = undefined
exec ps ev (SAss x e) =
    let v' = eval ps (ev `minus` x) e in
    case lookupEnv x ev of
      Nil -> update x v' ev
      v   -> if v == v'
             then update x Nil ev
             else if v' == Nil
                  then ev
                  else error ("Variable " ++ x ++ " does not match: " ++ render (prettyEnv ev) ++ "\n(" ++ show x ++ ", " ++ show e ++ ") = " ++ show v ++ ","  ++ show v')
exec ps ev (SCond e cs ds f)
  | eval ps ev e /= Nil = let ev' = foldl (exec ps) ev cs
                          in if eval ps ev' f /= Nil then ev'
                             else error ("in exec.SCond.true: " ++ show f ++ " must be true\n" ++
                                         show ev)
  | otherwise        = let ev' = foldl (exec ps) ev ds
                       in if eval ps ev' f == Nil then ev' else error ("in exec.SCond.false: " ++ show f ++ " must be false")
exec ps ev (SLoop e cs ds f) 
  | eval ps ev e /= Nil = loop ps ev (e,cs,ds,f)
  | otherwise         = error ("Assertion failed on entry of loop: " ++ show (SLoop e cs ds f))
exec ps ev (SRep q r) = let v = eval ps ev r
                            ev' = clear ev (vars r)
                        in execSRep ev' q v
exec ps ev (SUpdate e f) = let v1 = eval ps ev e
                               v2 = eval ps ev f
                               vl = lookupEnv "X0" ev -- Vl
                               vl' = update' v1 v2 vl
                           in update "X0" vl' ev -- Vl
  where update' Nil v2  (Cons Nil vl)        = Cons v2 vl
        update' Nil v2  (Cons v vl) | v2 == v = Cons Nil vl
        update' Nil Nil vl                   = vl
        update' (Cons Nil v1) v2 (Cons v vl) = Cons v (update' v1 v2 vl)
        update' v1 v2 vl                     = error ("Illegal update: \n" ++ 
                                                      "Vl: " ++ show (pretty vl) ++ "\n" ++
                                                      "j: " ++ show (pretty v1) ++ "\n" ++
                                                      "E: " ++ show (pretty v2) ++ "\n" ++
                                                      render (pretty (SUpdate e f))
                                                     )
exec ps ev (SLookup e x) = 
    let v  = eval ps ev e
        x' = lookupEnv x ev
        vl = lookupEnv "X0" ev
        v' = lookup v vl
    in if v' == x' then update x Nil ev
       else if x' == Nil then update x v' ev 
            else if v' == Nil then ev
                 else error ("in exec.SLookup: " ++ render (pretty (SLookup e x)))
  where lookup Nil          (Cons v1 vl) = v1
        lookup (Cons Nil v) (Cons v1 vl) = lookup v vl
        lookup e            f = error $ "in RWhileWM.Eval.exec.SLookup (" ++ show e ++ ") (" ++ show f ++ ")"
-- exec ev (SAssert x v) = if lookupEnv x ev == v then ev
--                         else error ("SAsssert failed: " ++ show ev ++ "\n(x,v)=" ++ show x ++ "," ++ show v)
exec ps ev (SAssert str e) 
    | eval ps ev e /= Nil = ev
    | otherwise        = error ("Impossible happened, assertion failed (" ++ str ++ "): " ++ show e ++ ", " ++ show ev)
exec ps ev (SShow e) = trace (show (pretty (eval ps ev e))) ev
exec ps ev (SCall id args) = let Just (fs, cs) = lookup id (map tip ps)
                                 tip (Proc x fs cs) = (x,(fs,cs))
                             in foldl (exec ps) ev (map (subst (zip fs args)) cs)
exec ps ev (SUncall id args) = 
    let Just (fs, cs) = lookup id (map tip ps)
        tip (Proc x fs cs) = (x,(fs,cs))
    in foldl (exec ps) ev (map (subst (zip fs args)) (invert cs))

clear :: Env -> [Ident] -> Env
clear ev vs = map f ev
    where f (x,v) | x `elem` vs = (x,Nil)
                  | otherwise   = (x,v)

execSRep :: Env -> Exp -> Val -> Env
-- execSRep _  e           f          | traceShow (e,f) False = undefined
execSRep ev (AVar x)    d          = if lookupEnv x ev == Nil
                                     then update x d ev 
                                     -- else if lookupEnv x ev == d
                                     --      then update x Nil ev
                                          else error ("in execSrep: lookup failed: " ++ show x ++ "\n" ++
                                                      show ev)
execSRep ev (AVal e)    d | e == d = ev
execSRep ev (ACons q r) (Cons e f) = execSRep (execSRep ev r f) q e
execSRep ev q           d          = error $ "in execSRep (pat,val): (" ++ render (pretty q) ++ ", " ++ render (pretty d) ++ ")"

loop :: [Proc] -> Env -> (Exp,[Cmd],[Cmd],Exp) -> Env
-- loop ev1 (e1,cs1,cs2,e2) | traceShow ("loop",cs1,cs2) False = undefined
loop ps ev1 (e1,cs1,cs2,e2) =
    let ev2 = foldl (exec ps) ev1 cs1
    in if eval ps ev2 e2 /= Nil
       then ev2
       else let ev3 = foldl (exec ps) ev2 cs2
            in if eval ps ev3 e1 == Nil
            then loop ps ev3 (e1,cs1,cs2,e2)
            else error ("Assertion failed in loop (assertion should be false): " ++ show e1 ++ ", " ++ show ev3)

execProgram :: Program -> Val -> Val
execProgram prog@(PDefs ps x cs y) v =
    let ev0 = update x v (initEnv (vars prog))
        ev1 = foldl (exec ps) ev0 cs
    in if allNil (ev1 `minus` y)
       then lookupEnv y ev1
       else error $ "Some vars are not Nil: " ++ render (prettyEnv ev1)
  where allNil :: Env -> Bool
        allNil ev = all (== Nil) (map snd ev)


class WellFormed a where
    wellFormedRWhileWM :: a -> Bool
    wellFormedRWhile   :: a -> Bool
    wellFormedRCore    :: a -> Bool

instance WellFormed Program where
    wellFormedRWhileWM (PDefs ps x cs y) = all wellFormedRWhileWM cs
    wellFormedRWhile   (PDefs ps x cs y) = all wellFormedRWhile cs
    wellFormedRCore    (PDefs ps x cs y) = all wellFormedRCore cs

instance WellFormed Cmd where
    wellFormedRWhileWM (SAss x e)        = x `notElem` vars e
    wellFormedRWhileWM (SRep _ _)        = True
    wellFormedRWhileWM (SCond _ cs ds _) = all wellFormedRWhileWM cs && 
                                           all wellFormedRWhileWM ds
    wellFormedRWhileWM (SLoop _ cs ds _) = all wellFormedRWhileWM cs &&
                                           all wellFormedRWhileWM ds
    wellFormedRWhileWM (SUpdate e f)     = null (vars e `intersect` vars f)
    wellFormedRWhileWM (SLookup e x)     = x `notElem` vars e
    wellFormedRWhileWM (SShow _)         = True
    wellFormedRWhileWM (SAssert _ _)     = True
    wellFormedRWhileWM (SCall _ _)       = True
    wellFormedRWhileWM (SUncall _ _)     = True

    wellFormedRWhile (SAss x e)        = x `notElem` vars e
    wellFormedRWhile (SRep _ _)        = True
    wellFormedRWhile (SCond _ cs ds _) = all wellFormedRWhile cs && all wellFormedRWhile ds
    wellFormedRWhile (SLoop _ cs ds _) = all wellFormedRWhile cs && all wellFormedRWhile ds
    wellFormedRWhile (SUpdate e f)     = False
    wellFormedRWhile (SLookup e x)     = False
    wellFormedRWhile (SShow _)         = True
    wellFormedRWhile (SAssert _ _)     = True
    wellFormedRWhile (SCall _ _)       = False
    wellFormedRWhile (SUncall _ _)     = False

    wellFormedRCore (SAss x e)        = x `notElem` vars e && simpleExp e
    wellFormedRCore (SRep q r)        = simpleExp q && simpleExp r
    wellFormedRCore (SCond x cs ds y) = isVar x && isVar y && 
                                        all wellFormedRCore cs && all wellFormedRCore ds
    wellFormedRCore (SLoop x cs ds y) = isVar x && isVar y && 
                                        all wellFormedRCore cs && all wellFormedRCore ds
    wellFormedRCore (SUpdate e f)     = False
    wellFormedRCore (SLookup e x)     = False
    wellFormedRCore (SShow _)         = True
    wellFormedRCore (SAssert _ _)     = True
    wellFormedRCore (SCall _ _)       = False
    wellFormedRCore (SUncall _ _)     = False

isVar          :: Exp -> Bool
isVar (AVar _) = True
isVar _        = False

simpleExp :: Exp -> Bool
simpleExp (AVar _)                  = True
simpleExp (ACons (AVar _) (AVar _)) = True
simpleExp (AVal _)                  = True
simpleExp (AEq (AVar _) (AVar _))   = True
simpleExp _                         = False
