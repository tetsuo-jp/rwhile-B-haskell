{-|
Module      : Invert
-}
module Invert where

import Ast

-- |Inverter
class Invert a where
    invert :: a -> a

instance Invert Program where
    invert (PDefs ds x cs y) = PDefs ds y (invert cs) x

instance Invert a => Invert [a] where
    invert cs = reverse (map invert cs)

instance Invert Cmd where
    invert c@(SAss _ _)      = c
    invert (SRep e f)        = SRep f e
    invert (SCond e cs ds f) = SCond f (invert cs) (invert ds) e
    invert (SLoop e cs ds f) = SLoop f (invert cs) (invert ds) e
    invert c@(SUpdate _ _)   = c
    invert c@(SLookup _ _)   = c
    invert c@(SShow _)       = c
    invert c@(SAssert _ _)   = c
    invert (SCall x as)      = SUncall x as
    invert (SUncall x as)    = SCall x as
