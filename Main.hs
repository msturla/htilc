module Main where

import ParserLC
import PrettyPrintLC
import TypeInference
import Examples

plainExpr :: String -> Doc
plainExpr = ppExpr . parseLC

inferExpr :: String -> Doc
inferExpr = ppTypingResult . inferType . parseLC

main = print (inferExpr (expr 20))