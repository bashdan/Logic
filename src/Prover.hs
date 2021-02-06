module Prover where

import Logic
import Substitution
import Data.Maybe
import Data.List (intercalate, nub)

-- Debug switch
--import Debug.Trace (trace)
trace' :: a -> b -> b
trace' _a _b = _b

-- Substitution = Subs [(Term, Term), (Term, Term) ... ]
data State = Cand ([Term], Substitution) | Soln Substitution

-- If it is a null substitution, we found a Predicate that matches the Query and does not need support
-- If it is not a null substitution, then we omit this from next state, if it has a substitution, then
-- we need to recursively resolve

instance Show State where
    show (Soln ss)       = show ss
    show (Cand (ts, ss)) = "C " ++ show ts ++ "," ++ show ss

instance Eq State where
    Soln a == Soln b = a == b
    Soln _ == Cand _ = False

-- An entry point to clean up calls to resolve
solve :: Stack -> [Term] -> [State]
solve st qs = unnameS $ resolve st qs 0 (Subs nulls)

-- Resolve tries keeps propagating search until there is no applicable q/qs
resolve :: Stack -> [Term] -> Int -> Substitution -> [State]
resolve st qs n ss = concatMap eval (search (freshen n st) qs ss)
    where eval (Soln ss)       = [Soln ss]
          eval (Cand (ts, ss)) = resolve st ts (n+1) ss

-- Search looks for more states (qs, subs) to resolve
search :: Stack -> [Term] -> Substitution -> [State]
search _         []      ss = [Soln ss]
search (Stck rs) (q:qs) (Subs ss) = prune [trace' ("Cand {"++show (dosub (unsub s) (xs++qs))++"},{"++show (Subs (unsub s++ss))++"} rs="++show xs) $ 
                                           Cand (dosub (unsub s) (xs++qs), Subs (unsub s++ss)) | 
                                           x :- xs <- rs, 
                                           s <- trace' ("att': x="++show x++" xs="++show xs++" with q="++show q) $ maybeToList $ unify q x]
    where unsub (Subs s) = s
          prune = map ((\(ts, s) -> if null ts then Soln s else Cand (ts, s)) . reduce)

--------------------------------------------------------------------------------

-- reduce may be useful to other functions
reduce :: State -> ([Term], Substitution)
reduce (Soln s) = ([], s)
reduce (Cand c) = c

subcomp :: [(Term, Term)] -> [(Term, Term)] -> [(Term, Term)]
subcomp a b = fromJust (Just a `compo` Just b)

renameVar :: Int -> Term -> Term
renameVar _ (Atm a)     = Atm a
renameVar _ (Str s)     = Str s
renameVar n (Var s)     = Var (s ++ "$" ++ show n)
renameVar n (Comp s ts) = Comp s $ map (renameVar n) ts

unnameVar :: Term -> Term
unnameVar (Atm a) = Atm $ takeWhile ('$' /=) a
unnameVar (Var v) = Var $ takeWhile ('$' /=) v
unnameVar (Comp l ts) = Comp l $ map unnameVar ts

unnameS :: [State] -> [State]
unnameS []            = []
unnameS ((Soln s):ss) = Soln (unnameSub s) : unnameS ss

unnameSub :: Substitution -> Substitution
unnameSub (Subs ps) = Subs $ map unn ps
    where unn (v, t) = (unnameVar v, unnameVar t)

freshen :: Int -> Stack -> Stack
freshen n (Stck rs) = Stck $ map (rename n) rs
    where rename :: Int -> Rule -> Rule
          rename n (r :- []) = renameVar n r :- []
          rename n (r :- rs) = renameVar n r :- map (renameVar n) rs