{-
-- Module Interpreter:  functions to interpret expressions
-- Author: Abdul Rahim Nizamani, ITIT, Gothenburg University, Sweden

-}

module Interpreter where

import Instances
import Data.Graph.AStar
import Data.Either
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromJust)
import Debug.Trace
import Data.Maybe
import qualified Data.Map as Map
import Control.Exception
import Data.List
import Data.Time.Clock
import Control.Monad
import qualified Control.Monad.Parallel as P
import Data.Function (on)

type Surface = Bool

-- check if the answer is the same as given, using Astar search
findAnswerDecl :: Set Concept -> LTM -> Set Rewarding -> Int -> Int -> (Lhs,Rhs) -> (Bool,Length)
findAnswerDecl concepts ltm rew width depth (exp,rhs) =
            let (ans, len) = solveAnswer width depth concepts ltm rew (exp,Nothing,Set.empty) (Just rhs)
            in ((isJust ans && (fromJust ans == rhs)), len)

-- find the solution (all proof steps) using the Astar search
findSolution :: Set Concept -> LTM -> Set Rewarding -> Int -> Int -> (Lhs,Rhs) -> [StateD]
-- if rhs is x, then search for any answer
--findSolution concepts ltm rew decay width depth (exp,(Var "x")) = do
--        ans <- solve decay width depth concepts ltm rew (Right (exp,Nothing), Set.empty) Nothing
--        if ans /= Nothing
--        then return ((Right (exp,Nothing), Set.empty) : fromJust ans)
--        else return ([(Left "No solution found", Set.empty)])
-- else search for the given answer
findSolution concepts ltm rew width depth (exp,rhs) =
        let ans = solve width depth concepts ltm rew (exp,Nothing,Set.empty) (Just rhs)
        in if isJust ans && notnull (fromJust ans)
            then (exp,Nothing,Set.empty) : fromJust ans
            else []

getAnswer width depth concepts mod rew start =
    if isRoot start
    then Just start
    else let result = aStar (expandNode mod width depth) 
                            stateDist (hDist rew) (isGoal mod width depth rew Nothing) (start,Nothing,Set.empty)
         in if isNothing result
            then Nothing
            else
              let result' = fromJust result
              in if null result'
                  then Nothing
                  else Just . fst' $ last result'

solveAnswer :: Int -> Int -> Set Concept
                -> LTM -> Set Rewarding -> StateD
                -> Maybe Exp -> (Maybe Exp, Length)
solveAnswer width depth concepts mod rew start end =
    let result = aStarIterative 1 width depth concepts mod rew start end
    in if isNothing result
        then (Nothing, 0)
        else
            let result' = fromJust result
            in if null result'
                then (Nothing, 0)
                else
                    let len = length result'
                        (ans,_,_) = last result'
                    in (Just ans, len)

solve = aStarIterative 1

aStarSimple :: Int -> Int -> Int ->
                  Set Concept -> LTM -> Set Rewarding -> 
                  StateD -> (Maybe Exp) -> ((Maybe [StateD]))
aStarSimple startDepth width maxDepth concepts mod rew start end 
        = aStar (expandNode mod width maxDepth) 
                stateDist (hDist rew) (isGoal mod width maxDepth rew end) start

aStarIterative :: Int -> Int -> Int 
                  -> Set Concept -> LTM -> Set Rewarding 
                  -> StateD -> (Maybe Exp) 
                  -> (Maybe [StateD])
aStarIterative startDepth width maxDepth concepts mod rew start end | startDepth > maxDepth = Nothing
aStarIterative startDepth width maxDepth concepts mod rew start end =
    let result = aStar (expandNode mod width startDepth)
                       stateDist (hDist rew) (isGoal mod width maxDepth rew end) start
    in if isJust result
            then result
            else aStarIterative (startDepth+1) width maxDepth concepts mod rew start end 

varBindings :: Axiom -> [(String,Exp)]
varBindings (Axiom (_,_,_,_,_,((Var q),dir,exp))) = [(q,exp)]
varBindings _ = []

-- (Either String (Exp,Maybe Axiom), Set Exp)
stateDist ::  StateD -> StateD -> Int
stateDist (e,_,_) (f,_,_) | e == f = 0
stateDist _ _ = 1 -- minimum length
--stateDist (_,Just a1,_) (_,Just a2,_) = return (axV a2 - axV a1)

hDist :: Set Rewarding -> StateD -> Int
hDist r (exp,_,_) = length [f | f <- getSymbols exp, (Rew f) `Set.notMember` r]

isGoal :: LTM -> Int -> Int -> Set Rewarding -> Maybe Exp -> StateD -> Bool
isGoal _ _ _ _ (Just goal) (wm,_,_)    = wm == goal
isGoal ltm width depth rewarding Nothing state@(r,_,_) = isGoal' rewarding r && Set.null (expandNode ltm width depth state)
--        let symbols = Set.fromList . map Rew $ getSymbols r
--        in isGoal' wm && symbols `Set.isSubsetOf` rewarding
isGoal' rew (Root r) = Set.member (Rew (0,r)) rew
isGoal' rew (Unary (Oper u) e) = Set.member (Rew (1,u)) rew && isGoal' rew e
isGoal' rew (Binary (Oper b) e (Root r)) = Set.member (Rew (2,b)) rew && Set.member (Rew (0,r)) rew && isGoal' rew e
isGoal' _ _ = False

expandNode :: LTM -> Int -> Int -> StateD -> Set StateD
expandNode _ _ maxLength (_,_,prev) | Set.size prev >= maxLength   =    Set.empty
expandNode m maxSize maxLength (exp,_,p) = 
    let prev = Set.insert exp p
        r' = interpreter True m maxSize maxLength exp
        --if not (null r')
        --then do
        --        putStrLn $ "\nExp: " ++ show exp ++ "\n"
        --        putStrLn $ "New wm: " ++  show (length r')
        --        putStrLn $ unlines $ map ("   " ++ ) $ map show $ nub' [r |Right r <- r']
        --        getChar
        --        return ()
        --else return ()
        right = [(x,d) | (x,d) <- nubBy' fst r',
                            size x <= maxSize, 
                            Set.notMember x prev]
                            -- all (\s -> Set.notMember s prev) (getSubExp x) ]
        traced = "\nExp: " ++ show exp ++ "\n" ++ unlines (map ("   " ++ ) $ map show [r |(r,_) <- right])
    in --trace traced
        (Set.fromList $ map (\(x,y) -> (x,y,prev)) right)

-- | Interprets any haskell expression from the given module
-- Only produces a single step
-- if argument indicates if it is the first level (False if in recursion mode)
interpreter :: Surface -> LTM -> Int -> Int -> Exp -> [(Exp,Maybe Axiom)]
-- Constant
interpreter b (Ltm facts axioms) width depth e@(Root arg) =
    concatMap (applyFact b e) $ Set.toList facts
-- Function application
interpreter b ltm@(Ltm facts axioms) width depth e@(Unary fname arg) =
    let expA = concatMap (applyRule b e) $ Set.toList axioms
        expF = concatMap (applyFact b e) $ Set.toList facts
        argnew' = interpreter False ltm width depth arg
        argnew = [(Unary fname r, d) | (r,d) <- argnew', r /= arg]
    in expA ++ expF ++ argnew
-- Infix applications
interpreter b ltm@(Ltm facts axioms) width depth e@(Binary op e1 e2) =
    let e1new' = interpreter False ltm width depth e1
        e2new' = interpreter False ltm width depth e2
        e1new = [((Binary op x e2),d) | (x,d) <- e1new', x /= e1]
        e2new = [((Binary op e1 x),d) | (x,d) <- e2new', x /= e2]
        expsA = concatMap (applyRule b e) $ Set.toList axioms
        expsF = concatMap (applyFact b e) $ Set.toList facts
    --putStrLn $ "Interpreter: \n" ++ (unlines $ map (\(x,y) -> "  " ++ show x) exps)
        -- traced = "Interpreter: \n" ++ (unlines $ map (\(x,y) -> "  " ++ show x) exps)
    in -- trace traced
        (expsA ++ expsF ++ e1new ++ e2new)
-- Literal and variable
interpreter _ _ _ _ e = [(e,Nothing)] -- concatMap (applyRule e) axioms

applyFact :: Surface -> WM -> Fact -> [(WM,Maybe Fact)]
applyFact _ wm a@(Axiom (_,_,_,_,_,(lhs,Bi,rhs)))
  | wm == lhs = [(rhs,Just a)]
  | otherwise
        = if (wm `containsExp` lhs)
            then map (\x -> (x,Just a)) $ filter (/= wm) $ replaceLhsRhsWm lhs rhs wm -- replace lhs with rhs in func
            else []
applyFact b wm a@(Axiom (_,_,_,_,_,(lhs,Uni,rhs))) -- surface application of shallow rules
  | wm == lhs && b = [(rhs,Just a)]
  | otherwise = []
applyFact b wm a@(Axiom (_,_,_,_,_,(lhs,Neg,rhs))) -- negative rules
    = []
-- | Check if the function argument matches with the given expression
applyRule :: Surface -> WM -> Axiom -> [(WM,Maybe Axiom)]
applyRule _ func a@(Axiom (_,_,_,_,_,(lhs,Bi,rhs)))
  | isJust bind && null (sameVarBinding . nub' $ fromJust bind)
        = let --result = [(foldl (\r (v,c) -> replaceAllSubExp r v c) rhs (fromJust bind),Just a)]
              result = [(replaceAllSubExp rhs (Map.fromList $ fromJust bind),Just a)]
              -- traced = "\napplyRule: " ++ unlines (map (show . fst) result) ++ "\n" ++ show bind
          in result
  | otherwise = []
  where bind = expVarBinding lhs func
applyRule b func a@(Axiom (_,_,_,_,_,(lhs,Uni,rhs)))
  | b && isJust bind && null (sameVarBinding . nub' $ fromJust bind)
        = let --result = [(foldl (\r (v,c) -> replaceAllSubExp r v c) rhs (fromJust bind),Just a)]
              result = [(replaceAllSubExp rhs (Map.fromList $ fromJust bind),Just a)]
              -- traced = "\napplyRule: " ++ unlines (map (show . fst) result) ++ "\n" ++ show bind
          in result
  | otherwise = []
  where bind = expVarBinding lhs func


notProvable :: Axiom -> [Axiom] -> Bool
notProvable ax axioms | (not . containsVarAx) ax = True
notProvable ax@(Axiom (_,_,_,_,_,_)) axioms = 
     not $ any (isInstance ax) axioms

