module Substitution where

import Data.Char
import Data.List (intercalate, nub)
import Logic
import Parser
import Data.Maybe (fromJust)
-- Subsitution where you are mapping the left side which is a Variable to the right side that is a Term.
newtype Substitution = Subs [(Term, Term)]

-- Defining the show instance.
instance Show Substitution where
  show (Subs s) = "{" ++ intercalate ", " (map helper s) ++ "}"
    where
      helper (v, t) = show v ++ " = " ++ show t

instance Eq Substitution where
  Subs (a:as) == Subs (b:bs) = a == b && as == bs

nulls :: [(Term, Term)]
nulls = []
doSingleSub :: (Term, Term) -> Term -> Term
doSingleSub (Var v, t) (Var subvar2)
  | v == subvar2 = t
  | otherwise = Var subvar2
doSingleSub(Var v,t)(Atm a) = Atm a 
doSingleSub s@(Var v,t) (Comp n ts) = Comp n (map (doSingleSub s) ts)

-- Applying a Substition to a term to give another term. The Apply list function makes it so it can map two of the terms together.
dosub :: [(Term, Term)] -> [Term] -> [Term]
dosub [] tl = tl
dosub (sub : []) tL = map (doSingleSub sub) tL
dosub (sub1 : s) tL = dosub s (map (doSingleSub sub1) tL)

compo :: Maybe [(Term, Term)] -> Maybe [(Term, Term)] -> Maybe [(Term, Term)]
compo _ Nothing = Nothing
compo s (Just []) = s
compo (Just su1) (Just su2) = Just (s1 ++ su2)
  where
    varlst = mapthefst su1
    termlst = mapthesnd su1
    termlst' = dosub su2 varlst
    s1 = zip termlst' termlst

dom :: Maybe Substitution -> [Term]
dom (Just (Subs s)) = map fst s

-- Unification
{-
*Main> a = Var "A"
*Main> b = Var "B"
*Main> c = unify a b
*Main> c
[{A = B}]
*Substitution> a2 = Comp "app"[Comp "cons" [Atm "a", Comp "cons" [Atm "b", Comp "cons" [Atm "c"]]]]
*Substitution> a1 = Comp "app"[Comp "cons" [ Var "A", Var "B"]]
*Substitution> testunify a1 a2
Just {A = a, B = cons(b, cons(c))}

-}
unify :: Term -> Term -> Maybe Substitution
unify a b 
  | unify' a b == Nothing = Nothing
  | otherwise = Just(Subs(fromJust(unify' a b)))
unify' :: Term -> Term -> Maybe [(Term, Term)]
unify' (Atm a) (Atm b) = if a == b then Just nulls else Nothing

unify' (Var a) (Var b) = if a /= b then Just [(Var a,Var b)] else Just nulls
unify' (Var x) t2 = Just ([(Var x, t2) | Var x `notElem` vars t2])
unify' t1 (Var y) = Just ([(Var y, t1) | Var y `notElem` vars t1])
unify' (Comp n ns) (Comp a as) 
  | n /= a = Nothing
  | length ns /= length as = Nothing
  | null ns && null as  = Just nulls
  | n == a = unifylistofterms  ns as
  | otherwise = Nothing 
unify' _ _ = Nothing


unifylistofterms :: [Term] -> [Term] -> Maybe [(Term,Term)]
unifylistofterms [t1] [t2] = unify' t1 t2
unifylistofterms ((term1:lstofterms1)) ((term2:lstofterms2))
        | Nothing == unify' term1 term2                = Nothing
        | otherwise                       = unifyLstHelper term1 term2 lstofterms1 lstofterms2
      
unifyLstHelper :: Term -> Term -> [Term] -> [Term] -> Maybe [(Term, Term)]
unifyLstHelper term1 term2 lstofterms1 lstofterms2 = let  subs1 = unify' term1 term2
                                                          subs1' = fromJust subs1
                                                          subs_lstofterms1 = dosub subs1' lstofterms1
                                                          subs_lstofterms2 = dosub subs1' lstofterms2
                                                          subs2 = unifylistofterms subs_lstofterms1 subs_lstofterms2
                                                        in compo subs1 subs2



mapthefst :: [(Term,Term)] -> [Term]
mapthefst  = map fst 
mapthesnd :: [(Term,Term)] -> [Term]
mapthesnd  = map snd



isin :: Term -> Term -> Bool
isin (Var v) t = isinhelper (Var v) (vars t) 

isinhelper :: Term -> [Term] -> Bool
isinhelper (Var v) [] = False
isinhelper (Var v) ts = (Var v == head ts) || isinhelper (Var v) (tail ts)