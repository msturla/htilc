module Main where

import ParserLC
import PrettyPrintLC
import TypeInference
import Examples

plainExpr :: String -> Doc
plainExpr = ppExpr . parseLC

inferExpr :: String -> Doc
inferExpr = ppTypingResult . inferType . parseLC

main = do
	   str <- getLine
	   print (inferExpr (expr (read str)))