module SOL where

import Data.List
import Data.Maybe

import Types
import TestData

printF :: Formula -> IO()
printF
  = putStrLn . showF
  where
    showF (Var v)
      = v
    showF (Not f)
      = '!' : showF f
    showF (And f f')
      = "(" ++ showF f ++ " & " ++ showF f' ++ ")"
    showF (Or f f')
      = "(" ++ showF f ++ " | " ++ showF f' ++ ")"


-- There is no test module so the accuracy cannot be ensured. 
-- The sample answer provided for dp and allSat seemed a little bit messy. Not sure about the correctness of dp. 

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp k
  = fromJust . lookup k

-- 3 marks
vars :: Formula -> [Id]
vars (Var id)
  = [id]
vars (Not f)
  = (nub. sort) (vars f)
vars (And f1 f2)
  = (nub. sort) (vars f1 ++ vars f2)
vars (Or f1 f2)
  = vars (And f1 f2)
    
-- 1 mark
idMap :: Formula -> IdMap
idMap f
  = zip (vars f) [1..]

--------------------------------------------------------------------------
-- Part II

-- An encoding of the Or distribution rules.
-- Both arguments are assumed to be in CNF, so the
-- arguments of all And nodes will also be in CNF.
distribute :: CNF -> CNF -> CNF
distribute a (And b c)
  = And (distribute a b) (distribute a c)
distribute (And a b) c
  = And (distribute a c) (distribute b c)
distribute a b
  = Or a b

-- 4 marks
toNNF :: Formula -> NNF
toNNF (Not (Not f))
  = toNNF f
toNNF (Not (Or f1 f2))
  = And (toNNF (Not f1)) (toNNF (Not f2))
toNNF (Not (And f1 f2))
  = Or (toNNF (Not f1)) (toNNF (Not f2))
toNNF (Not f)
  = Not (toNNF f)
toNNF (And f1 f2)
  = And (toNNF f1) (toNNF f2)
toNNF (Or f1 f2)
  = Or (toNNF f1) (toNNF f2)
toNNF (Var id)
  = Var id

-- 3 marks
toCNF :: Formula -> CNF
toCNF f
  = toCNF' (toNNF f)
    where toCNF' :: Formula -> CNF
          toCNF' (Var id)
            = Var id
          toCNF' f@(Not (Var id))
            = f
          toCNF' (And f1 f2)
            = And (toCNF' f1) (toCNF' f2)
          toCNF' (Or f1 f2)
            = distribute f1 f2

-- 4 marks
flatten :: CNF -> CNFRep
flatten cnf
  = flatten' cnf []
    where idmap = idMap cnf
          flatten' :: CNF -> CNFRep -> CNFRep
          flatten' (Var id) res
            = [[lookUp id idmap]]
          flatten' (Not (Var id)) res
            = [[lookUp id idmap * (-1)]]
          flatten' (Not f) res
            = map (map (*(-1))) (flatten' f res)
          flatten' (And f1 f2) res
            = flatten' f1 res ++ flatten' f2 res ++ res
          flatten' (Or f1 f2) res
            = concat (flatten' f1 res ++ flatten' f2 res) : res
            

--------------------------------------------------------------------------
-- Part III

-- 5 marks
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits []
  = ([], [])
propUnits cRep
  -- 当singles为null时，说明此时的cRep已经满足条件（无singleton），则应该停止循环，此时的singleton list为[]
  | null singles = (cRep, [])
  | otherwise    = (res_crep, list')
    where (res_crep, list) = propUnits (deleteAllsin cRep singles)
          list' = list ++ singles
          -- 注意！！使用list comprehension的时候要记得判断是否为null
          singles = concat [s | s@[_] <- cRep]

          deleteClause :: CNFRep -> Int -> CNFRep -> CNFRep
          deleteClause (c : cs) s crep
            | s `elem` c = deleteClause cs s crep
            | (-s) `elem` c = deleteClause cs s crep'
            | otherwise  = deleteClause cs s (c : crep)
              where c' = c \\ [-s] 
                    crep' = c' : crep
          deleteClause _ s res
                      = res
                      
          deleteAllsin :: CNFRep -> [Int] -> CNFRep
          deleteAllsin cnf sings@(s : ss)
            = deleteAllsin (deleteClause cnf s []) ss
          deleteAllsin res _
            = res

-- 4 marks
dp :: CNFRep -> [[Int]]
dp cRep
  | null cRep'      = [list]
  | [] `elem` cRep' = []
  | otherwise       = map (nub . (list ++)) (true ++ false)
    where (cRep', list) = propUnits cRep
          f = head (head cRep')
          true = dp ([f] : cRep)
          false = dp ([-f] : cRep)

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat f
  = map sort (allSat' dps [])
    where allSat' :: [[Int]] -> [[(Id, Bool)]] -> [[(Id, Bool)]]
          allSat' list@(l : ls) res
            = allSat' ls (map findId l : res)
          allSat' _ res
            = res
          cnf = toCNF f
          flat = flatten cnf
          idmap = idMap f
          dps = dp flat
          findId :: Int -> (Id, Bool)
          findId n
            | n > 0     = (id1, True)
            | otherwise = (id2, False)
              where [id1] = [ x | (x, y) <- idmap, y == n]
                    [id2] = [ x | (x, y) <- idmap, y == (-n)]