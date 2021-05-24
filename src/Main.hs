{-# LANGUAGE ParallelListComp, PatternGuards #-}
module Main where

import System.Environment (getArgs)
import Logic
import Substitution
import Parser
import Prover
import Debug.Trace (trace)
import Prelude
import Data.List (nub, find)

--------------------------------------------------------------------------------

-- Main for reading file as argument
main :: IO ()
main = do args <- getArgs
          let files = filter (("--" /=) . take 2) args
          fileContents <- mapM readFile files
          setup (concat fileContents)
          
setup :: String -> IO ()
setup input = do let rules = [ r | ((r, ""):_) <- parseType ruleF input ]
                     queries = [ q | ((q, ""):_) <- parseType queryF input ]
                     stack = foldl addStack emptyStack rules
                 mapM_ (answer stack) queries
                 interpreter stack [] "Setup finished. Running interpreter"
    where parseType f i = map (runParser f) $ lines i

-- Solve one query (list of predicates)
answer :: Stack -> [Term] -> IO ()
answer st qs = do let as = nub $ solve st qs
                  if null as then putStr "No"
                             else putStr "Yes"
                  if null $ concatMap vars qs then putStr "" -- If there are no vars to convey
                                              else mapM_ printSln as
    where printSln (Soln (Subs ss)) = 
            let ansLst = ans (nub' ss) (unionVars qs) in 
                case ansLst of
                    [a] -> putStr $ "\n" ++ show (fst a) ++ " = " ++ show (snd a)
                    _   -> mapM_ (\(v, t) -> putStrLn (show v ++ " = " ++ show t)) ansLst

interpreter :: Stack -> [Term] -> String -> IO ()
interpreter st qs s = do putStrLn s
                         input <- getLine
                         case runParser action input of
                            [(Fact f, "")] -> interpreter (addStack st f) qs ("Added " ++ show f)
                            [(Query q, "")] -> doAction st q "answer"
                            [(ADebug x, "")] -> doAction st qs x
                            [(NoAction, "")] -> interpreter st qs ""
                            [(_, _)] -> interpreter st qs ("Not parsed " ++ input)
                            [] -> interpreter st qs ("Not parsed* " ++ input) -- Could've crashed

--------------------------------------------------------------------------------
-- Functions to make X = ans in terms of X instead of W, Y, Z, etc.

ans :: [(Term, Term)] -> [Term] -> [(Term, Term)]
ans vts qvs = [(p, q) | p <- qvs, (_, q) <- map (curSub vts) qvs]

nub' :: [(Term, Term)] -> [(Term, Term)]
nub' [] = []
nub' ((a, b):m) = if a == b then nub' m else (a,b):nub' m

curSub :: [(Term, Term)] -> Term -> (Term, Term)
curSub vts (Var a) = if subToDo vts (Var a) then curSub vts (nextSub vts (Var a))
                                            else head $ filter (\(Var v, _) -> a == v) vts
    where subToDo :: [(Term, Term)] -> Term -> Bool
          subToDo [] _ = False
          subToDo ((Var x, Var y):m) (Var a) = (a == x) || subToDo m (Var a)
          subToDo ((Var _, _):m) a = subToDo m a
          nextSub :: [(Term, Term)] -> Term -> Term
          nextSub [] a = a
          nextSub ((Var x, Var y):m) (Var a) = if a == x then Var y else nextSub m (Var a)
          nextSub ((Var _, _):m) a = nextSub m a

extract :: [State] -> [Substitution] -> [Substitution]
extract [] ss = ss
extract ((Soln s):ss') sb = extract ss' (s:sb)

extract1 :: [State] -> Substitution
extract1 [] = Subs nulls
extract1 (Soln s:_) = s

-- Handle some IO looping to read/write data structures

print1Ans :: [Term] -> Substitution -> IO ()
print1Ans ts (Subs q) = print $ dosub q ts

moreAns :: Parser ()
moreAns = do token (char ';'); return ()

data Action = Fact Rule | Query [Term] | NoAction | ADebug String

instance Show Action where
    show (Fact c)           = show c
    show (Query cs)         = show cs
    show (ADebug s)         = s

ruleF :: Parser Rule
ruleF = (do r <- rule; char '.'; token spaces; comment; return r) </>
        (do r <- rule; char '.'; token spaces; return r) </>
        (do r <- rule; char '.'; return r)

queryF :: Parser [Term]
queryF = (do qs <- complist; char '?'; token spaces; comment; return qs) </>
         (do qs <- complist; char '?'; token spaces; return qs) </>
         (do qs <- complist; char '?'; return qs)

action' :: String -> Parser Action
action' s = do token (string s); return (ADebug s)
         
clAction :: Parser Action
clAction = (do action' "listing") </>
           (do action' "restart") </>
           (do action' "qs")

doAction :: Stack -> [Term] -> String -> IO ()
doAction st qs s = case s of
    "quit" -> putStrLn "quitting"
    "listing" -> interpreter st qs (show st)
    "qs" -> interpreter st qs (show qs)
    "restart" -> interpreter (Stck []) [] "Restarted interpreter"
    "answer" -> do answer st qs
                   interpreter st [] ""
    _ -> interpreter st qs ("Not implemented " ++ s)

actionReduce :: Parser Action
actionReduce = do a <- action
                  token comment
                  return a

action :: Parser Action
action = (do ADebug . show <$> clAction) </>
         (do comment; return NoAction) </>
         (do r <- rule; char '.'; return (Fact r)) </>
         (do q <- complist; char '?'; return (Query q)) </>
         (do ADebug . show <$> simpleTerm) </>
         (do token (satisfy ('\n' ==)); return NoAction)
