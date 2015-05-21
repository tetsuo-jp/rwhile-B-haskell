module Parser where

import Text.Parsec
import qualified Text.Parsec.Token as P
import Control.Applicative ((<$), (<$>), (<*>), (<*), (*>))

import Ast

rwhilewmDef :: P.LanguageDef ()
rwhilewmDef = P.LanguageDef 
               { P.commentStart    = "(*"
               , P.commentEnd      = "*)"
               , P.commentLine     = ""
               , P.nestedComments  = False
               , P.identStart      = letter <|> char '_'
               , P.identLetter     = alphaNum <|> char '\''
               , P.opStart         = oneOf "=^<."
               , P.opLetter        = oneOf "?="
               , P.reservedOpNames = ["=?", "^=", "<=", "."]
               , P.reservedNames   = ["read", "write", "nil", "cons", "hd", "tl", "if", "then", "else", "fi", "from", "do", "loop", "until", "UPDATE", "LOOKUP", "show", "procedure"]
               , P.caseSensitive   = True
               }

P.TokenParser { P.parens = parens
              , P.braces = braces
              , P.identifier = identifier
              , P.reservedOp = reservedOp
              , P.reserved = reserved
              , P.whiteSpace = whiteSpace 
              , P.symbol = symbol 
              , P.semi = semi
              , P.semiSep = semiSep
              , P.commaSep = commaSep
              , P.semiSep1 = semiSep1
              , P.dot = dot
              , P.natural = natural
              , P.stringLiteral = stringLiteral } = P.makeTokenParser rwhilewmDef

type Parser = Parsec String ()

pProgram :: Parser Program
pProgram = do whiteSpace
              procs <- many pProc
              x1 <- reserved "read" *> identifier <* symbol ";"
              cs <- pCmd `endBy` symbol ";"
              x2 <- reserved "write" *> identifier
              return (PDefs procs x1 cs x2)
           <?> "program"

pProc :: Parser Proc
pProc = do reserved "procedure"
           id <- identifier
           args <- parens (commaSep identifier)
           body <- semiSep1 pCmd
           return $ Proc id args body

pCmd :: Parser Cmd
pCmd = try pAss <|> try pRep <|> pCond <|> pLoop <|> try pUPDATE <|> pLOOKUP <|> pShow <|> pAssert -- e.g. X ^= E and X <= Y overlap
       <|> pCall <|> pUncall
       <?> "command"

pAss :: Parser Cmd
pAss = SAss <$> (identifier <* reservedOp "^=") <*> pExp
       <?> "assignment"

pRep :: Parser Cmd
pRep = SRep <$> pPat <* reservedOp "<=" <*> pPat
       <?> "pRep"

pPat :: Parser Exp
pPat = pVar
   <|> try (AVal  <$> pVal)     -- '(' overlaps
   <|> ACons <$> (reserved "cons" *> pPat2) <*> pPat2
   <?> "pPat"

pPat2 :: Parser Exp
pPat2 = pVar
    <|> try (AVal <$> pVal)     -- '(' overlaps
    <|> ACons <$> (symbol "(" *> (reserved "cons" *> pPat2)) <*> (pPat2 <* symbol ")")
    <?> "pPat2"

pVar :: Parser Exp
pVar = AVar <$> identifier
   <?> "variable"

pVal :: Parser Val
pVal = Nil  <$  reserved "nil"
   <|> Cons <$> (symbol "(" *> pVal <* symbol ".") <*> pVal <* symbol ")"
   <|> nils <$> natural
   <|> Atom <$> (symbol "'" *> many alphaNum <* spaces)
   <?> "value"
  where nils n = foldr Cons Nil $ replicate (fromInteger n) Nil

pCond :: Parser Cmd
pCond = do e1  <- reserved "if"   *> pExp
           cs1 <- reserved "then" *> pCmd `sepBy` symbol ";" <|> return []
           cs2 <- reserved "else" *> pCmd `sepBy` symbol ";" <|> return []
           e2  <- reserved "fi"   *> pExp
           return (SCond e1 cs1 cs2 e2)
        <?> "conditional"

pLoop :: Parser Cmd
pLoop = do e1  <- reserved "from"  *> pExp
           cs1 <- reserved "do"    *> pCmd `sepBy` symbol ";" <|> return []
           cs2 <- reserved "loop"  *> pCmd `sepBy` symbol ";" <|> return []
           e2  <- reserved "until" *> pExp
           return (SLoop e1 cs1 cs2 e2)
        <?> "loop"

pUPDATE :: Parser Cmd
pUPDATE = SUpdate <$> (reserved "UPDATE" *> pExp2) <*> pExp2
          <?> "update"

pLOOKUP :: Parser Cmd
pLOOKUP = do _ <- reserved "LOOKUP"
             e <- pExp2
             x <- identifier
             return $ SLookup e x
          <?> "lookup"

pShow :: Parser Cmd
pShow = SShow <$> (reserved "show" *> pExp)
        <?> "show"

pAssert :: Parser Cmd
pAssert = SAssert <$> (reserved "assert" *> stringLiteral) <*> pExp2
          <?> "assert"

pCall :: Parser Cmd
pCall = do reserved "call" 
           x <- identifier
           fs <- parens (commaSep identifier)
           return $ SCall x fs
          <?> "call"

pUncall :: Parser Cmd
pUncall = 
    do reserved "uncall" 
       x <- identifier
       fs <- parens (commaSep identifier)
       return $ SUncall x fs
    <?> "uncall"

pExp :: Parser Exp
pExp = AVal  <$> pVal    -- '(' overlaps
   <|> pVar
   <|> ACons <$> (reserved "cons" *> pExp2) <*> pExp2
   <|> AHd   <$> (reserved "hd"   *> pExp2)
   <|> ATl   <$> (reserved "tl"   *> pExp2)
   <|> AEq   <$> (reservedOp "=?" *> pExp2) <*> pExp2
   <?> "expression"

pExp2 :: Parser Exp
pExp2 = try (AVal  <$> pVal)    -- '(' overlaps
    <|> pVar
    <|> parens (
             ACons <$> (reserved "cons" *> pExp2) <*> pExp2
         <|> AHd   <$> (reserved "hd"   *> pExp2)
         <|> ATl   <$> (reserved "tl"   *> pExp2)
         <|> AEq   <$> (reservedOp "=?" *> pExp2) <*> pExp2)
    <?> "expression2"

pEnv :: Parser Env
pEnv = braces (commaSep ((,) <$> (identifier <* reservedOp ":=") <*> pVal))

parseProgram :: String -> Either ParseError Program
parseProgram = parse (pProgram <* eof) "(unknown)"

parseExp :: String -> Either ParseError Exp
parseExp = parse (pExp <* eof) "(unknown)"

parsePat :: String -> Either ParseError Exp
parsePat = parse (pPat <* eof) "(unknown)"

parseCmd :: String -> Either ParseError Cmd
parseCmd = parse (pCmd <* eof) "(unknown)"

pC :: String -> Cmd
pC str = case parseCmd str of
           Left err -> error $ show ("in parseCmd': " ++ str)
           Right cmd -> cmd

parseVal :: String -> Either ParseError Val
parseVal = parse (pVal <* eof) "(unknown)"

parseEnv :: String -> Either ParseError Env
parseEnv = parse (pEnv <* eof) "(unknown)"
