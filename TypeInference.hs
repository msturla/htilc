module TypeInference (TypingJudgment, Error(..), inferType)

where

import Data.List(intersect)
import Exp
import Type
import Unification

------------
-- Errors --
------------
data Error a = OK a | Error String


--------------------
-- Type Inference --
--------------------
type TypingJudgment = (Env, AnnotExp, Type)


inferType :: PlainExp -> Error TypingJudgment
inferType e = case infer' e 0 of
    OK (_, tj) -> OK tj
    Error s -> Error s


infer' :: PlainExp -> Int -> Error (Int, TypingJudgment)
infer' (VarExp x)     n = let freshT = TVar n
                          in OK (n + 1,
                            (extendE emptyEnv x freshT, VarExp x, freshT))
infer' ZeroExp n = OK (n, (emptyEnv, ZeroExp, TNat))
infer' TrueExp n = OK (n, (emptyEnv, TrueExp, TBool))
infer' FalseExp n = OK (n, (emptyEnv, FalseExp, TBool))
infer' (SuccExp exp) n = inferPredSucc exp n
infer' (PredExp exp) n = inferPredSucc exp n
infer' (IsZeroExp exp) n = case (infer' exp n) of 
							OK (n', (env', e', t')) ->
								case mgu [(t', TNat)] of
									UOK sub -> OK (n', (sub <.> env', sub <.> (SuccExp e'), TBool))
									UError t1 t2 -> uError t1 t2
							Error err -> Error err
infer' (IfExp e1 e2 e3) n = case (infer' e1 n) of 
							OK (n1, (env1, e1', tbool)) ->
								case mgu [(tbool, TBool)] of
									UOK sub -> case (infer' e2 n1) of
										OK (n2, (env2, e2', t2)) -> case (infer' e3 n2) of
											OK (n3, (env3, e3', t3)) ->
												case mgu [(t2, t3)] of
													UOK sub2 -> case unifyThreeEnvs env1 env2 env3 of
														UOK sub3 -> let finalSub = addSubs [sub, sub2, sub3] in
																		OK (n3,  (joinE [finalSub <.> env1, finalSub <.> env2, finalSub <.> env3],
																		finalSub <.> (IfExp e1' e2' e3'),
																		finalSub <.> t2))
														UError terr1 terr2 -> uError terr1 terr2
													UError terr1 terr2 -> uError terr1 terr2
											Error err -> Error err
										Error err -> Error err
									UError t1 t2 -> uError t1 t2
							Error err -> Error err
infer' (LamExp sym () exp) n = case (infer' exp n) of
								OK (n', (env', e', t')) ->
									if elem sym (domainE env') then
										let t = evalE env' sym in 
										OK (n', (removeE env' sym, LamExp sym t e', TFun t t'))
									else
										let freshT = TVar n'
										in OK (n' + 1, (extendE env' sym freshT, LamExp sym freshT e', TFun freshT  t'))
								Error err -> Error err
infer' (AppExp e1 e2) n = case (infer' e1 n) of
							OK (n1, (env1, e1', t1)) ->
								case (infer' e2 n1) of
									OK (n2, (env2, e2', t2)) ->
										let freshT = TVar n2 in
										case mgu [(t1, TFun t2 freshT)] of 
											UOK sub1 -> case unifyFreeVars env1 env2 of
												UOK sub2 -> let finalSub = sub1 <.> sub2 in
															OK (n2 + 1, ( joinE [finalSub <.> env1, finalSub <.> env2],
															AppExp (finalSub <.> e1') (finalSub <.> e2'),
															finalSub <.> freshT))
												UError terr1 terr2  -> uError terr1 terr2
											UError terr1 terr2 -> uError terr1 terr2
									Error err -> Error err
							Error err -> Error err

							
-- Auxiliary functions for iner'


addSubs :: [Subst] -> Subst
addSubs ss = foldr (<.>) emptySubst ss

unifyThreeEnvs :: Env -> Env -> Env -> UnifResult
unifyThreeEnvs env1 env2 env3 = case unifyFreeVars env1 env2 of 
								UOK sub1 -> case unifyFreeVars env1 env3 of
									UOK sub2 -> case unifyFreeVars env2 env3 of
										UOK sub3 -> UOK (sub1 <.> sub2 <.> sub3)
										UError t1 t2 -> UError t1 t2
									UError t1 t2 -> UError t1 t2
								UError t1 t2 -> UError t1 t2
								

unifyFreeVars :: Env -> Env -> UnifResult
unifyFreeVars env1 env2 = mgu (getGoals env1 env2)



inferPredSucc exp n = case (infer' exp n) of 
							OK (n', (env', e', t')) ->
								case mgu [(t', TNat)] of
									UOK sub -> OK (n', (sub <.> env', sub <.> (SuccExp e'), TNat))
									UError t1 t2 -> uError t1 t2
							Error err -> Error err


getGoals :: Env -> Env -> [UnifGoal]
getGoals env1 env2 = [(evalE env1 x, evalE env2 x) |
	                        x <- intersect (domainE env1) (domainE env2)]


--------------------------------
-- YAPA: Error de unificacion --
--------------------------------
uError :: Type -> Type -> Error (Int, a)
uError t1 t2 = Error $ "Cannot unify " ++ show t1 ++ " and " ++ show t2
