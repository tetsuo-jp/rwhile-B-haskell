module Ast where

import Text.PrettyPrint
import Data.List ((\\), nub)
import Data.Maybe (fromMaybe)

import Debug.Trace

{-
  Programs in P ::= read X; C^*; write X
-}
data Program = PDefs [Proc] Ident [Cmd] Ident
               deriving (Eq,Ord,Show)

-- Procedures
data Proc = Proc Ident [Ident] [Cmd]
          deriving (Eq,Ord,Show)

{-
  Commands in C ::= X ^= E | Q <= R
                  | if E then C else D fi F
                  | from E do C loop D until F
                  | LOOKUP j X
                  | UPDATE j E
-}
data Cmd =
   SAss Ident Exp
 | SRep Exp Exp
 | SCond Exp [Cmd] [Cmd] Exp
 | SLoop Exp [Cmd] [Cmd] Exp
 | SUpdate Exp Exp
 | SLookup Exp Ident
 | SShow Exp
 | SAssert String Exp
 | SCall Ident [Ident]
 | SUncall Ident [Ident]
  deriving (Eq,Ord,Show)

{-
  Expressions in E, F ::= X | nil | cons E F | hd E | tl E | =? E F
-}
data Exp =
   AVar Ident
 | AVal Val
 | ACons Exp Exp
 | AHd Exp
 | ATl Exp
 | AEq Exp Exp
  deriving (Eq,Ord,Show)

-- |Environment
type Env = [(Ident,Val)]

isEqSet :: Eq a => [a] -> [a] -> Bool
isEqSet xs ys = null (xs \\ ys) && null (ys \\ xs)

class Show a => Pretty a where
    pretty :: a -> Doc
    pretty' :: a -> Doc
    pretty' e = traceShow ("in RWhileWM.Ast.pretty': " ++ show e) (pretty e)

instance Pretty Val where
    -- pretty Nil        = text "nil"
    pretty v | flag = integer n
      where (flag,n) = isInt v
            isInt Nil = (True, 0)
            isInt (Cons Nil w) = let (flag, n) = isInt w
                                 in (flag, n+1)
            isInt _   = (False, undefined)
    pretty (Atom s)   = text "'" <> text s
    pretty (Cons e f) = text "(" <> pretty e <> text "." <> pretty f <> text ")"

instance Pretty Exp where
    pretty (AVar x)    = text x
    pretty (AVal d)    = pretty d
    pretty (ACons e f) = text "cons" <+> pretty' e <+> pretty' f
    pretty (AHd e)     = text "hd" <+> pretty' e
    pretty (ATl e)     = text "tl" <+> pretty' e
    pretty (AEq e f)   = text "=?" <+> pretty' e <+> pretty' f

    pretty' (AVar x)   = text x
    pretty' (AVal d)   = pretty d
    pretty' e          = parens (pretty e)

instance Pretty Cmd where
    pretty (SAss x e)        = text x <+> text "^=" <+> pretty e
    pretty (SRep e f)        = pretty e <+> text "<=" <+> pretty f
    pretty (SCond e cs ds f) = sep [text "if" <+> pretty e,
                                    if null cs then empty else text "then" <+> pretty cs,
                                    if null ds then empty else text "else" <+> pretty ds,
                                    text "fi" <+> pretty f]
    pretty (SLoop x cs ds y) = sep [text "from"  <+> pretty x,
                                    if null cs then empty else text "do"    <+> pretty cs,
                                    if null ds then empty else text "loop"  <+> pretty ds,
                                    text "until" <+> pretty y]
    pretty (SUpdate e f)     = text "UPDATE"  <+> pretty' e <+> pretty' f
    pretty (SLookup e x)     = text "LOOKUP"  <+> pretty' e <+> text x
    pretty (SAssert x e)     = text "assert" <+> text "\"" <> text x <> text "\"" <+> parens (pretty e)
    pretty (SShow e)         = text "show" <+> pretty' e
    pretty (SCall x as)      = text "call" <+> text x <> parens (sep (punctuate semi (map text as)))
    pretty (SUncall x as)    = text "uncall" <+> text x <> parens (sep (punctuate semi (map text as)))

instance Pretty a => Pretty [a] where
    pretty es = sep $ punctuate semi $ map pretty es

instance Pretty Program where
    pretty (PDefs ps x cs y) = sep $ punctuate semi $ filter (not . isEmpty)
                               [text "read" <+> text x,
                                nest 2 $ if null cs then empty else pretty cs,
                                text "write" <+> text y]

instance Pretty Proc where
    pretty (Proc f xs c) = text "procedure" <+> text f <> parens (sep (punctuate comma (map text xs)))

prettyEnv :: Env -> Doc
prettyEnv evs = braces (sep (punctuate comma (map f evs)))
    where f (x,v) = text x <+> text ":=" <+> pretty v

{-|
  DATA in D ::= nil | (D.D) | 'atom
-}
data Val = Nil
         | Cons Val Val
         | Atom String
           deriving (Eq,Ord,Show)

type Ident = String

-- |Variables, the increasing order, no duplication
class Vars a where
    vars :: a -> [Ident]

instance Vars Program where
    vars (PDefs ps x cs y) = nub (vars ps ++ x : y : vars cs)

instance Vars Proc where
    vars (Proc _ fs cs) = nub (vars cs) \\ fs

instance Vars a => Vars [a] where
    vars = concatMap vars

instance Vars Cmd where
    vars (SAss x e)            = x : vars e
    vars (SRep e1 e2)          = vars e1 ++ vars e2
    vars (SCond e1 cs1 cs2 e2) = vars e1 ++ vars cs1 ++ vars cs2 ++ vars e2
    vars (SLoop e1 cs1 cs2 e2) = vars e1 ++ vars cs1 ++ vars cs2 ++ vars e2
    vars (SUpdate e1 e2)       = vars e1 ++ vars e2
    vars (SLookup e x)         = x : vars e
    vars (SShow _)             = []
    vars (SAssert _ _)         = []
    vars (SCall _ fs)          = fs
    vars (SUncall _ fs)        = fs

instance Vars Exp where
    vars (AVar x)    = [x]
    vars (AVal _)    = []
    vars (ACons e f) = vars e ++ vars f
    vars (AHd e)     = vars e
    vars (ATl e)     = vars e
    vars (AEq e f)   = vars e ++ vars f

substString ss x = fromMaybe x (lookup x ss)

-- |Substitution
class Subst a where
  subst :: [(Ident,Ident)] -> a -> a

instance Subst Exp where
  subst ss (AVar x) = AVar (substString ss x)
  subst ss e@(AVal _)  = e
  subst ss (ACons e f) = ACons (subst ss e) (subst ss f)
  subst ss (AHd e)     = AHd (subst ss e)
  subst ss (ATl e)     = ATl (subst ss e)
  subst ss (AEq e f)   = AEq (subst ss e) (subst ss f)

instance Subst Cmd where
  subst ss (SAss x e)        = SAss (substString ss x) (subst ss e)
  subst ss (SRep p q)        = SRep (subst ss p) (subst ss q)
  subst ss (SCond e cs ds f) = SCond (subst ss e) (map (subst ss) cs) (map (subst ss) ds) (subst ss f)
  subst ss (SLoop e cs ds f) = SLoop (subst ss e) (map (subst ss) cs) (map (subst ss) ds) (subst ss f)
  subst ss (SUpdate e f)     = SUpdate (subst ss e) (subst ss f)
  subst ss (SLookup e x)     = SLookup (subst ss e) (substString ss x)
  subst ss (SShow str)       = SShow str
  subst ss (SAssert str e)   = SAssert str (subst ss e)
  subst ss (SCall x as)      = SCall (substString ss x) (map (substString ss) as)
  subst ss (SUncall x as)      = SUncall (substString ss x) (map (substString ss) as)

instance Subst Program where
  subst ss (PDefs ps x cs y) = PDefs ps (substString ss x) (map (subst ss) cs) (substString ss y)
