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

--------------------------------------------------------------------------
-- Part I

-- 1 mark
lookUp :: Eq a => a -> [(a, b)] -> b
-- Pre: The item being looked up has a unique binding in the list
lookUp el list
  = (fromJust.(lookup el)) list

-- 3 marks
vars :: Formula -> [Id]
vars (Var id)
  = [id]
vars (Not frm)
  = vars frm
vars (Or frm1 frm2)
  = (nub.sort) ((vars frm1) ++ (vars frm2))
vars (And frm1 frm2)
  = (nub.sort) ((vars frm1) ++ (vars frm2))

-- 1 mark
idMap :: Formula -> IdMap
idMap frm
  = zip (vars frm) [1..]

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
toNNF (Not (Var id))
  = (Not (Var id))
toNNF (Not (Not frm))
  = toNNF frm
toNNF (Not (Or frm1 frm2))
  = (And (toNNF (Not frm1)) (toNNF (Not frm2)))
toNNF (Not (And frm1 frm2))
  = (Or (toNNF (Not frm1)) (toNNF (Not frm2)))
toNNF (Var id)
  = (Var id)
toNNF (Or frm1 frm2)
  = (Or (toNNF frm1) (toNNF frm2))
toNNF (And frm1 frm2)
  = (And (toNNF frm1) (toNNF frm2))

-- 3 marks
toCNF :: Formula -> CNF
toCNF formula
  = toCNF' (toNNF formula)
  where
    toCNF' (Var id)
      = (Var id)
    toCNF' (Not (Var id))
      = (Not (Var id))
    toCNF' (And frm1 frm2)
      = (And (toCNF' frm1) (toCNF' frm2))
    toCNF' (Or frm1 frm2)
      = distribute frm1 frm2

-- 4 marks
flatten :: CNF -> CNFRep
flatten cnf
  = flatten' cnf (idMap cnf)
  where
    flatten' (And frm1 frm2) idMaps
      = ((flattenClause frm1 idMaps) : (flatten' frm2 idMaps))
    flatten' frm idMaps
      = [flattenClause frm idMaps]

flattenClause :: CNF -> IdMap -> [Int]
flattenClause (Var id) idMaps
  = [(lookUp id idMaps)]
flattenClause (Not (Var id)) idMaps
  = [(-(lookUp id idMaps))]
flattenClause (Or frm1 frm2) idMaps
  = (flattenClause frm1 idMaps) ++ (flattenClause frm2 idMaps)
      
      
    

--------------------------------------------------------------------------
-- Part III

-- 5 marks
propUnits :: CNFRep -> (CNFRep, [Int])
propUnits cnfRep
  | maybe == Nothing
    = (cnfRep, [])
  | otherwise
    = (cnfRep', singleton : sols)
  where
    maybe = findSingleton cnfRep
    singleton = fromJust maybe
    (cnfRep', sols) = propUnits (deleteClauses (deleteLiterals cnfRep))

    deleteClauses list
      = filter (not.(elem singleton)) list
    deleteLiterals list
      = map (filter (/= -singleton)) list

    findSingleton :: CNFRep -> (Maybe Int)
    findSingleton [] 
      = Nothing
    findSingleton ([x] : _)
      = Just x
    findSingleton (_ : t)
      = findSingleton t

-- 4 marks
dp :: CNFRep -> [[Int]]
dp cnfRep
  | nextRep == []
    = [sols]
  | elem [] nextRep
    = []
  | otherwise
    = map (sols++) ((dp ([literal] : nextRep)) ++ dp ([-literal] : nextRep))
  where
    (nextRep, sols) = propUnits cnfRep
    literal = head (head nextRep)

--------------------------------------------------------------------------
-- Part IV

-- Bonus 2 marks
allSat :: Formula -> [[(Id, Bool)]]
allSat frm
  = allResults'
  where
    cnfRep = flatten (toCNF (toNNF frm))
    result = dp cnfRep
    idMaps = idMap frm
    maxEl = length idMaps
    allResults = concatMap (makeWholeSorted 1 maxEl) result
    allResults' = map (bindResult idMaps) allResults

-- This function takes as it's 3rd parameter a solution and
-- adds all possible missing numbers to it
makeWholeSorted :: Int -> Int -> [Int] -> [[Int]]
makeWholeSorted n maxEl list
  | n > maxEl
    = [[]]
  | elem n list
    = map (n :) (makeWholeSorted (n+1) maxEl list)
  | elem (-n) list
    = map ((-n) :) (makeWholeSorted (n+1) maxEl list)
  | otherwise
    = makeWholeSorted n maxEl (n : list) ++
      makeWholeSorted n maxEl ((-n) : list)

-- This is the inverse of the lookUp function
inverseLookUp :: Eq b => b -> [(a, b)] -> a
inverseLookUp el list
  = lookUp el (map (\(x,y) -> (y,x)) list)

-- This creates a result from an input like
-- [("var", 1)] [-1] to [("var", False)]
bindResult :: IdMap -> [Int] -> [(Id, Bool)]
bindResult idMaps list
  = map makePair list
  where
    makePair n
      | n < 0
        = (inverseLookUp (-n) idMaps, False)
      | otherwise
        = (inverseLookUp n idMaps, True)