module Examples(expr)
--module Examples(expr, module Main)
where

-- import Main

expr :: Int -> String
-- Ejemplos con Var, Zero, Succ y App
expr 1 = "x"
expr 2 = "0"
expr 3 = "succ(x)"
expr 4 = "succ(0)"
expr 5 = "f x"
expr 6 = "f 0"
expr 7 = "succ(f 0)"
expr 8 = "0 f"
expr 9 = "f 0 succ(succ(0))"
expr 10 = "f (0 succ(succ(0)))"
expr 11 = "f x y z"
expr 12 = "f (x y z)"
expr 13 = "f succ(x) y z"
expr 14 = "f (succ(x) y z)"
expr 15 = "x x"
expr 16 = "(\\x -> x)"
expr 17 = "(\\x -> x) y"
expr 18 = "\\s -> \\x -> \\y -> s x y"
expr 19 = "\\s -> \\x -> \\y -> s (x y)"
expr 20 = "(\\s -> \\x -> \\y -> s) (x y)"
expr 21 = "if (g True) then succ(0) else pred(f 0)"
expr 22 = "\\s -> if (g s) then succ(f s) else pred(s)"
expr 23 = "if (g s) then succ(f s) else pred(s)"
expr 24 = "(\\s -> \\x -> \\y -> s) (a b)"
expr 25 = "(z (\\y -> z))"
expr n = error $ "La expresion " ++ show n ++ " no esta definida"