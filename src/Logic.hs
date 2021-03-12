module Logic where

import Parser
import Data.Char (isAlphaNum)
import Data.List
import Prelude hiding (succ, pred)

-- An atom is a string beginning with a lowercase character
type Atom = String

-- A variable is a string beginning with an uppercase character
type Variable = String

-- The Term is the universal type. There are many contexts in which it will be
-- used but very few instances where its uses overlap. So long that the parsing
-- is careful, we will not misconfigure the Term type system nor confuse the
-- contexts in which the Term is used.
data Term = Atm Atom | 
            Var Variable | 
            Comp String [Term] |
            ETerm -- "Extra" or "Error" Term

-- The complex constructor for rule standardizes what it appears as
-- If it is necessary to create a simpler Rule from a Compound:
--      ie: Predicate P(a,..,z) then it is constructed by String "P"
--          and list of subterms Term
data Rule = Term :- [Term]

-- The stack holds our list of rules for adding and updating
newtype Stack = Stck [Rule]

-- Substitutions attempt to assign Variables to other unifyable terms
--type Substitution = [(Term, Term)]

--------------------------------------------------------------------------------

instance Show Term where
    show (Atm a)           = a
    show (Var v)           = v
    show (Comp s l@(t:ts)) = s ++ "(" ++ intercalate ", " (map show l) ++ ")"
    show ETerm             = "error term"

instance Show Rule where
    show (t :- [])         = show t
    show (t :- rs)         = show t ++ " :- " ++ intercalate ", " (map show rs)

instance Show Stack where
    show (Stck [])         = "empty stack"
    show (Stck rs)         = show $ intercalate ", " (map show rs)

--------------------------------------------------------------------------------

instance Eq Term where
    Atm a == Atm b               = a == b
    Atm a == Var v               = a == v
    (Comp c ts) == (Comp d ss)   = c == d && ts == ss
    Var a == Var v               = a == v
    _     == _                   = False

--------------------------------------------------------------------------------
-- Functions for Lists in Logic

-- A function just to help the parser, but it might help in other cases
consify :: [Term] -> Term
consify [] = Atm "nil"
consify (t:ts) = Comp "cons" [t, consify ts]

-- TODO decide on the futures of these fucnctions
head0 :: Term -> Term
head0 (Comp s ts) = if s == "cons" && not (null ts) then head ts
                    else ETerm -- It probably wasn't a List. Perhaps debug.

tail0 :: Term -> Term
tail0 (Comp s (_:x:xs)) = if s == "cons" && null xs then x
                          else ETerm

removeItem _ [] = []
removeItem x (y:ys) | x == y    = removeItem x ys
                    | otherwise = y : removeItem x ys
--}

--------------------------------------------------------------------------------
-- Functions for Numbers in Logic

-- @TODO decide the fate of these perhaps
{--
succ :: Term -> Term
succ Zero    = Num 1
succ (Num 0) = succ Zero
succ (Num n) = Num (n+1)
succ _       = ETerm

pred :: Term -> Term
pred Zero    = Num (-1)
pred (Num 0) = pred Zero
pred (Num n) = Num (n-1)
pred _       = ETerm
--}
--------------------------------------------------------------------------------
-- Functions for the Stack in Logic

compRule :: Term -> Rule
compRule (Comp s ts) = Comp s ts :- []

emptyStack :: Stack
emptyStack = Stck []

addStack :: Stack -> Rule -> Stack
addStack (Stck []) r = Stck [r]
addStack (Stck rs) r = Stck $ r:rs

--------------------------------------------------------------------------------

firstLower :: Parser String
firstLower     = do c <- lower
                    cs <- many (satisfy isAlphaNum)
                    return (c:cs)

firstUpper :: Parser String
firstUpper     = do c <- upper
                    cs <- many (satisfy isAlphaNum)
                    return (c:cs)

notFollowedBy :: Parser a -> Parser b -> Parser a
p `notFollowedBy` q = do res1 <- p
                         res2 <- option Nothing (Just <$> q)
                         case res2 of 
                              Nothing    -> return res1
                              Just _res2 -> err

atom :: Parser Atom
atom = do token firstLower `notFollowedBy` char '('

variable :: Parser Variable
variable = do token firstUpper `notFollowedBy` char '('

num :: Parser Term
num = do spaces
         n <- nat
         makeNum n (Atm "zero")
    where makeNum :: Int -> Term -> Parser Term
          makeNum x t
            | x == 0    = return t
            | otherwise = makeNum (x-1) (Comp "succ" [t])

simpleTerm :: Parser Term
simpleTerm = (do Atm <$> atom) </> 
             (do Var <$> variable) </> 
             (do num) </> 
             (do list) </>
             (do comp)
         
list :: Parser Term
list = do char '['
          th <- token termlist
          tl <- token listtail
          case tl of
              ETerm -> return $ consify th
              _     -> return $ consify' th tl
     where listtail = (do char '|'; ts <- simpleTerm
                          char ']'; return ts) </>
                      (do char ']'; return ETerm)
           consify' :: [Term] -> Term -> Term
           consify' []     t = t
           consify' (x:xs) t = Comp "cons" [x, consify' xs t]

termlist :: Parser [Term]
termlist = do sepBy (char ',') (token simpleTerm)

comp :: Parser Term
comp = do spaces; l <- firstLower;
          ts <- parens termlist
          return (Comp l ts)

complist :: Parser [Term]
complist = do sepBy (char ',') (token comp)

rule1 :: Parser Rule
rule1 = do s <- notFollowedBy comp (symbol ":-"); return (compRule s)
          
rule :: Parser Rule
rule =  (do rule1) </>
        (do p <- comp
            symbol ":-"
            ps <- complist
            return (p :- ps))

comment :: Parser ()
comment = do spaces
             token (char '%')
             _ <- many (satisfy ('\n' /=))
             return ()

debugParse :: String -> IO ()
debugParse t = case runParser simpleTerm t of 
     [(a, "")] -> print a
     []        -> putStrLn "err"

debugStack :: Stack -> IO ()
debugStack (Stck rs) = mapM_ (print . show) rs

termcomment :: Parser Term
termcomment = do t <- simpleTerm; token comment; return t

--------------------------------------------------------------------------------

vars :: Term -> [Term]
vars (Atm _)     = []
vars (Var v)     = [Var v]
vars (Comp _ ts) = concatMap vars ts
-- vars (Subs s) = (map fst s) ++ ((map snd s) >>= vars)

-- This function returns the union of vars across multiple queries
unionVars :: [Term] -> [Term]
unionVars [q]    = nub $ vars q
unionVars (q:qs) = vars q `intersect` unionVars qs

predVars :: Rule -> [Term]
predVars (Comp s ts :- []) = vars (Comp s ts) -- "Degenerate form"
predVars (Comp s ts :- rs) = vars (Comp s ts) ++ concatMap vars rs

replace :: Term -> Term -> Term -> Term
replace (Var y) t (Var x)         = if x == y then t else Var x
replace (Var y) t (Comp s (x:xs)) = Comp s (map (replace (Var y) t)(x:xs))