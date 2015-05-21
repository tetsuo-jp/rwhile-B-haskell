{-|
Module      : Main
-}
module Main where

import System.Console.GetOpt
import System.Environment
import System.Exit
import System.Timeout
import Control.Monad (unless)
import System.IO (hPutStr, stderr)

import Parser
import Text.Parsec.Error (messageString, errorMessages)
import Eval
import Ast (pretty)
import Trans (trans)
import ToData (todata)

-- import Debug.Trace

data Flag = Time Int | From KindD | To KindD deriving Show
data KindD = RCore | RCoreData | RWhile | RWhileWM deriving (Show,Read)

options :: [OptDescr Flag]
options = [ Option ['t'] ["time"] (ReqArg (Time . read) "10") "timeout after N seconds"
          , Option []    ["from"] (ReqArg (From . read) "RWhileWM") "transform from"
          , Option []    ["to"]   (ReqArg (To   . read) "RCore") "transform to"
          ]

processArg :: [Flag] -> (Int,KindD,KindD)
processArg []     = (10,RWhileWM,RCore)
processArg (a:as) = let (time,from,to) = processArg as in
                    case a of
                      Time time' -> (time',from,to)
                      From from' -> (time,from',to)
                      To   to'   -> (time,from,to')

main :: IO ()
main = do args <- getArgs
          case getOpt Permute options args of
            (t,[prog],[]) ->
                let (time,from,to) = processArg t in
                do prog_str <- loadFile prog
                   prog <- case parseProgram prog_str of
                             Left err -> print err >> exitWith (ExitFailure 1)
                             Right p  -> return p
                   let wellFormed = case from of 
                                      RCore    -> wellFormedRCore
                                      RWhile   -> wellFormedRWhile
                                      RWhileWM -> wellFormedRWhileWM
                   unless (wellFormed prog) (print "not well formed" >> exitWith (ExitFailure 1))
                   case (from,to) of
                     (_,    RCoreData) -> print (pretty (todata prog))
                     (_,    RCore)     -> print (pretty (trans prog))
                     (_,    RWhileWM)  -> print (pretty (trans prog))
                     (_,    _)         -> print "not implemented in Main.main"
            (t,[prog,val],[]) ->
                do res <- let (time,_,_) = processArg t
                          in timeout (time * 1000000) $ parseAndRun prog val
                   case res of
                     Nothing -> exitWith $ ExitFailure 124
                     _       -> return ()
            (_,_,errs) -> hPutStr stderr (concat errs ++ "\n" ++ usageInfo header options) >> exitWith (ExitFailure 1)
              where header = "Usage: rw [options] <file>"

loadFile :: String -> IO String
loadFile "-"      = getContents
loadFile filename = readFile filename

parseAndRun :: String -> String -> IO ()
parseAndRun prog_file val_file =
  do prog_str <- loadFile prog_file
     val_str  <- loadFile val_file
     case Parser.parseProgram prog_str of
       Left err   -> print err >> exitWith (ExitFailure 1)
       Right prog -> case parseVal val_str of
                       Left err  -> mapM_ (hPutStr stderr . messageString) (errorMessages err) >> exitWith (ExitFailure 1)
                       Right val -> print $ pretty $ execProgram prog val
