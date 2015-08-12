
module AliceLib where
import System.Environment (getArgs, getProgName)
import System.Random
import Data.Array.IO
import Parsing
import Data.Ord
import Data.Char
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Instances
import Interpreter
import Data.List
import Data.Time
import qualified Control.Monad.Parallel as P
import Control.Monad (when,forM,liftM,filterM)
import Data.Word
import Data.Maybe
import System.IO
import System.Directory (doesFileExist)
import Data.Maybe (isNothing)
import Data.Function (on)
import Control.Arrow
import Control.Monad (foldM)
import Control.Concurrent (forkIO,takeMVar,newEmptyMVar,putMVar)
import Control.Parallel.Strategies
import System.Timeout
import System.Console.ANSI
import TestData
import Debug.Trace
import Data.Time.Calendar
import Domains.Arithmetic
import Domains.PropLogic
import Domains.English
import Test.QuickCheck

type Concepts = Set Exp
type Utility = Int
type Delta = (Set Axiom,Set Axiom)

type Verbose = Bool -- print results or not

data Runtime = Continuous | Stepwise deriving Eq

showScore :: Int
showScore = 1000

timeLimit = 100000000 -- microseconds, time limit for checking a delta

decay = 0.5 -- decay parameter for long term memory

normalizeOutput s' = if null s
                     then s
                     else let s2 = map fst $ filter (\(x,y) -> not (x==' ' && y==' ')) $ zip s (tail s)      -- "x  y" -> ("x  y","  y")
                          in s2 ++ [last s]
    where s = filter (\x -> x/='#' && x/='\\') s'

-- minimum number of examples for given number of variable count
minExamples :: Int -> Int
minExamples n | n < 1 = 1
minExamples n = n + 1

whiteVivid = SetColor Foreground Vivid White
whiteDull  = SetColor Foreground Dull White

-- | Free variables are those that occur in lhs but not in rhs.
-- | For example, the axiom (x*0=0) has one free variable.
freeVariables = 1

showSolution :: [StateD] -> String
showSolution [] = ""
showSolution [x] = showState x
showSolution (x:xs) = let x' = showState x
                      in x' ++ "\n--------\n" ++ showSolution xs

showState :: StateD -> String
showState (exp,Nothing,_) = showExp exp
showState (exp,Just d, _) = showExp exp ++ ", using " ++ showAxiom d

showExp :: Exp -> String
showExp exp = let x = show exp
              in if take 1 x == "(" && take 1 (reverse x) == ")"
                    then drop 1 (reverse . drop 1 . reverse $ x)
                    else x

showAxiom (Axiom (_,_,_,_,_,(lhs,dir,rhs))) = showExp lhs ++ show dir ++ showExp rhs
-- | Use abstraction (anti-unification) when d > 6
useAbstraction = True

maximum' i xx = if null xx then i else maximum xx

runOnce :: Bool -> Verbose -> Agent -> Item -> IO (Agent,Bool,[(Int,Axiom)],([StateD],[(String,Exp)]))
runOnce test vb agent@(Agent comm param (axioms,concepts,graph',pats',rew,rem)) item = do
        time <- getCurrentTime
        let updatedConcepts = foldl insertInConcepts concepts $ extractConcepts time item
        (graph,pats,axioms',result,rewNew,changes,(rem',computation,subst)) <- findDelta test vb time (Agent comm param (axioms,updatedConcepts,graph',pats',rew,rem)) item
        let newRem = take 10 (rem' ++ rem)
        let newAgent  = (Agent comm param (axioms',updatedConcepts,graph,pats,rewNew,newRem))
        let iter = if test then getIterations agent else 1 + getIterations agent
        return (setIterations newAgent iter,result,changes,(computation,subst))

printNeg (Axiom (_,_,_,_,_,(lhs,dir,rhs)))
    = let result = take 40 . normalizeOutput $ '-' : (show lhs ++ show dir ++ show rhs)
      in result ++ take (40 - length result) (repeat ' ')
printPos (Axiom (_,_,_,_,_,(lhs,dir,rhs)))
    = let result = take 40 . normalizeOutput $ '+' : (show lhs ++ show dir ++ show rhs)
      in result ++ take (40 - length result) (repeat ' ')
printAxiom (Axiom (_,_,_,_,_,(lhs,dir,rhs)))
    = let result = take 40 . normalizeOutput $ (show lhs ++ show dir ++ show rhs)
      in result ++ take (40 - length result) (repeat ' ')
printItem n s = let result = take n s
              in result ++ take (n - length result) (repeat ' ')
    
ifReadyDo :: Handle -> IO a -> IO (Maybe a)
ifReadyDo hnd x = hReady hnd >>= f
   where f True = x >>= return . Just
         f _    = return Nothing

-- | Saves an agent in a file
saveAgent :: Bool -> Agent -> IO ()
saveAgent True _ = return ()
saveAgent False (Agent (filename,comments) (width,depth,axiom,(redun,consis,mode,iter)) (ltm,concepts,graph,_,_,_)) = do
    file <- openFile filename WriteMode
    hSetEncoding file utf8
    hPutStr file comments
    time <- getCurrentTime
    hPutStr file $ "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                   ",(\\v Width)" ++ head deepRule ++ "(" ++ show width ++ "))\n"
    hPutStr file $ "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                   ",(\\v Depth)" ++ head deepRule ++ "(" ++ show depth ++ "))\n"
    hPutStr file $ "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                   ",(\\v LtmSize)" ++ head deepRule ++ "(" ++ show axiom ++ "))\n"
    hPutStr file $ "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                   ",(\\v Redundancy)" ++ head deepRule ++ "(" ++ show redun ++ "))\n"
    hPutStr file $ "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                   ",(\\v Consistency)" ++ head deepRule ++ "(" ++ show consis ++ "))\n"
    hPutStr file $ "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                   ",(\\v Mode)" ++ head deepRule ++ "(" ++ show mode ++ "))\n"
    hPutStr file $ "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                   ",(\\v Iterations)" ++ head deepRule ++ "(" ++ show iter ++ "))\n"
    hPutStr file . unlines . map show 
                 . sortBy ((compare `on` containsVarAx) `och` (compare `on` axRecency))
                 $ Set.toList $ allAxioms ltm
    hPutStr file $ unlines $ map show $ Set.toList concepts
    hPutStr file $ unlines $ map show $ getEdges graph
    hClose file
--axiomaticity a1 a2 = compare (containsVarAx a1) (containsVarAx a2)

createAgent :: String -> Int -> Int -> Int -> IO Bool
createAgent name wmsize clen ltmsize = do
    exist <- doesFileExist name
    if exist
    then return False
    else do
    time <- getCurrentTime
    writeFile name $ unlines
        $["{-", 
          "    Alice Agent: " ++ name,
          "-}",
          "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                ",(\\v Width)" ++ head deepRule ++ "(" ++ show wmsize ++ "))",
          "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                ",(\\v Depth)" ++ head deepRule ++ "(" ++ show clen ++ "))",
          "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                ",(\\v Axiom)" ++ head deepRule ++ "(" ++ show ltmsize ++ "))",
          "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                ",(\\v Redundancy)" ++ head deepRule ++ "(" ++ "False" ++ "))",
          "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                ",(\\v Consistency)" ++ head deepRule ++ "(" ++ "True" ++ "))",
          "(A,0,0,True," ++ show time ++ "," ++ show time ++ 
                ",(\\v Mode)" ++ head deepRule ++ "(" ++ "Popper" ++ "))"
         ]
    return True

updateGraph :: Graph Pattern -> Set Pattern -> Set Concept -> LTM -> Set Rewarding
                -> Int -> Int -> Bool -> Consistency -> Map Exp (Substitution,Rhs)
                -> IO (Graph Pattern,Set Pattern)
updateGraph graph' pats' _ _ _ _ _ _ _ exps | Map.null exps = return (graph',pats')
updateGraph graph' pats' concepts ltm' rew width depth redun consis exps = do
    --putStrLn "pats'"
    --mapM (putStrLn . show) $ Set.toList pats'
    let ltm = Ltm (Set.filter axIsFact (ltmFacts ltm')) Set.empty -- only facts used for computations
    let concepts' = Set.size $ Set.filter (isUnitConcept) concepts
    let vars  = Set.fromList . getVars
    let exps' = filter (\x -> tsize x <= 7) . filter (\x -> x `Set.notMember` pats') $ Map.keys exps
    let pats  = Set.union pats' $ Set.fromList exps'
    let substitutions = map fst $ Map.elems exps
    units <- sample' (oneof $ map return [c | (C (0,_,_,_,_,Root c)) <- Set.toList concepts])
    --putStrLn "exps'"
    --mapM (putStrLn . show) $ exps'
    let checkPurity vx vy = all (`elem` vx) vy
    let graph1
            = if null exps'                             -- if all exps already in graph
              then graph'                       -- then return same
              else  let newGraph = [((x,y),(Satisfiable,Set.empty))
                                                | x <- Set.toList pats,
                                                  y <- Set.toList pats,
                                                  x /= y,
                                                  not (isVar x),
                                                  let varsX = nub' $ getVars x,
                                                  let varsY = getVars y,
                                                  varsX == sort varsX,
                                                  varsX `elem` [["x"],["x","y"],["x","y","z"]],
                                                  checkPurity varsX varsY
                                    ]
                    in Map.unionWithKey (\(e1,e2) (a,s1) (b,s2) ->
                                                let vrs = getVars e1
                                                    vrs' = nub' vrs
                                                in if  a == Invalid -- && not (Set.null s1)
                                                   then (a,s1)
                                                   else if b==Invalid -- && not (Set.null s2)
                                                        then (b,s2)
                                                        else if e1 == e2 || (size e2) >= (2 * size e1)
                                                                -- || Set.fromList vrs /= vars e2
                                                                -- || vrs' /= sort vrs'
                                                              then (Invalid,Set.empty)
                                                              else if a == Valid
                                                                   then (Valid,s1)
                                                                   else if b == Valid
                                                                        then (Valid,s2)
                                                                        else (Satisfiable,Set.union s1 s2) )
                                            graph' (makeGraph newGraph)
                          
    
    let func1=(\(e1,e2) (b,set) ->
                case b of
                 Invalid -> (b,set)
                 _ -> 
                  let varSet = Set.union (getVarsSet' e1) (getVarsSet' e2)
                      substitutions' = [s | s <- substitutions, Map.keysSet s == varSet]
                      checkConvergence constants val@(Invalid,_) = val
                      checkConvergence constants (b',set') =
                                        let constants' = (Map.elems constants)
                                            newSet = Set.insert constants' set'
                                            newSet' = Set.toList newSet
                                            validified = if null newSet' then False else satisfy concepts' newSet' (length . head $ newSet') consis
                                            exp1 = replaceAllSubExp e1 $ Map.map Root constants
                                            exp2 = replaceAllSubExp e2 $ Map.map Root constants
                                            ans1 = getAnswer width depth concepts ltm rew exp1
                                            ans2 = getAnswer width depth concepts ltm rew exp2
                                        in  if constants' `Set.member` set'
                                            then (b',set')
                                            else 
                                              if isJust ans1 && isJust ans2
                                              then if ans1 == ans2
                                                 then if b'==Valid
                                                      then (b',set')
                                                      else if validified then (Valid,newSet) else (Satisfiable,newSet)
                                                 else (Invalid,Set.singleton (Map.elems constants))
                                              else (b',set')
                  in if null substitutions'
                     then checkConvergence (Map.fromList $ zip (Set.toList varSet) units) 
                                           (b,set)
                     else checkConvergence (head substitutions')
                                           (checkConvergence (Map.fromList $ zip (Set.toList varSet) units)
                                                             (b,set))
                                )
    
    let func =(\(e1,e2) (b,set) ->
                case b of
                 Invalid -> (b,set)
                 _ -> 
                  let e1' = Map.lookup e1 exps
                  in if isNothing e1'
                     then (b,set)
                     else
                      let (subst,rhs) = fromJust e1'
                          newSet = Set.insert (Map.elems subst) set
                          newSet' = Set.toList newSet
                          satisfied = if null newSet' then False else satisfy concepts' newSet' (length . head $ newSet') consis
                          exp = replaceAllSubExp e2 $ Map.map Root subst
                      in if exp == rhs
                         then if b==Valid
                              then (b,set)
                              else if satisfied then (Valid,newSet) else (Satisfiable,newSet)
                         else 
                          let (ans, len) = solveAnswer width depth concepts ltm rew (exp,Nothing,Set.empty) (Just rhs)
                          in if isJust ans
                              then if (fromJust ans == rhs)
                                     then if b==Valid
                                          then (b,set)
                                          else if satisfied then (Valid,newSet) else (Satisfiable,newSet)
                                     else (Invalid,Set.singleton (Map.elems subst))
                              else
                                 let (ans2, len) = solveAnswer width depth concepts ltm rew (exp,Nothing,Set.empty) Nothing
                                 in if isNothing ans2
                                     then (Satisfiable,set)
                                     else if fromJust ans2 == rhs
                                           then if b==Valid
                                                then (b,set)
                                                else if satisfied then (Valid,newSet) else (Satisfiable,newSet)
                                           else (Invalid,Set.singleton (Map.elems subst))  )
    let graph2 = Map.mapWithKey func1 graph1
    return (graph2,pats)

{-
updateShape :: Set Shape -> Set Concept -> Set Axiom -> Set Rewarding
                -> Int -> Int -> Exp -> (Shape,Substitution)
                -> IO Shape
updateShape shapes' concepts ltm' rew width depth rhs (s@(Shape (shape1,vars1,list)),subst) = do
    -- shapes <- shuffle $ Set.toList shapes'
    let shapes = Set.toList shapes'
    let ltm = Set.filter isFact ltm'
    if null subst || Set.fromList (map fst subst) /= vars1
    then return (s,Set.empty)
    else do
    let suitableShapes = [(shape2,foldl (\x (var,const) -> replaceAllSubExp x var (makeR const)) shape2 subst)
                                | (Shape (shape2,vars2,_)) <- shapes,
                                  vars1 == vars2,
                                  shape1 /= shape2,
                                  size shape2 < 2 * (size shape1)]
    candidates <- P.mapM (\(sh,exp) -> do
                                (ans, len) <- solveAnswer width depth concepts ltm rew (exp,Nothing,Set.empty) (Just rhs)
                                if isJust ans && (fromJust ans == rhs)
                                then return (True,sh,Nothing)
                                else do
                                  (ans2, len) <- solveAnswer width depth concepts ltm rew (exp,Nothing,Set.empty) Nothing
                                  if isJust ans2
                                  then do
                                    if (fromJust ans2 == rhs)
                                      then return (True,sh,Nothing)
                                      else return (False,sh,Just (W (shape1,sh)))
                                  else return (False,sh,Nothing))
                          $ suitableShapes
    let subst' = map snd $ sortBy (compare `on` fst) subst
    let newList = Map.fromList [(e,Set.singleton subst') | (True,e,_) <- candidates]
    let list' = Map.unionWith Set.union list newList
    return (Shape (shape1,vars1,list'))
-}

-- search for a suitable candidate to add to the long-term memory
findDelta :: Bool -> Verbose -> UTCTime -> Agent -> Item -> 
             IO (Graph Pattern,Set Pattern,LTM,Bool,Set Rewarding,[(Int,Axiom)],(RecentlyRemoved,[StateD],[(String,Exp)]))
findDelta test vb time
          agent@(Agent c (width,depth,ltmSize,(redun,consistency,mode,iter)) (ltm,concepts,graph',pats',rew',rem')) 
          item@(Item t t' v)
-- input and ouput are same, so no need to perform computation
  | t == t' = do 
    let rew = updateRewarding rew' item
    let newShapes = Map.filterWithKey (\k a -> null $ getUnary k) $ makeShapes (t,t')
    let ltm' = insertInLTM ltm $ Axiom (fromIntegral v,1,True,time,time,(t,Bi,t'))
    (graph,pats) <- updateGraph graph' pats' concepts ltm' rew width depth redun consistency newShapes
    return (graph,pats,ltm,True,rew,[],([],[],[]))
-- Variable in right-hand-side: deductive computation
  | isVar t' && not (containsVar t) =
    case t' of
     (Var _) -> if v < 0
                then return (Map.empty,Set.empty,ltm,True,Set.empty,[],([],[],[]))
                else do
                    let ans = solve width depth concepts ltm rew' (t,Nothing,Set.empty) Nothing
                    let solution = if isNothing ans then [] else (t,Nothing,Set.empty) : fromJust ans
                    -- putStrLn $ "Computation size: " ++ show (length solution)
                    return $ (Map.empty,Set.empty,ltm,isJust ans,Set.empty,[],([],solution,[]))
     _ -> return (Map.empty,Set.empty,ltm,False,Set.empty,[],([],[],[]))
-- variable in the question: abduction
  | (containsVar t' || containsVar t) && v >= 0 = do
    let axiom = Axiom (fromIntegral v,1,True,time,time,(t,Bi,t'))
    let bindings = [b | Just b <- (map (\x -> findVarBinding x axiom) (Set.toList $ ltmFacts ltm))]
    let bind = if null bindings then [] else head bindings
    return (Map.empty,Set.empty,ltm,null bind,Set.empty,[],([],[],bind))
-- test mode: just solve it, do not update theory
  | test = do
    let ans = findSolution concepts ltm rew' width depth (t,t')
    let result = if v < 0 then null ans else notnull ans
    return $ (Map.empty,Set.empty,ltm,result,Set.empty,[],([],ans,[]))
-- negative item
  | v < 0 && isGoal' rew' t' = do
    let solution = findSolution concepts ltm rew' width depth (t,t')
    -- putStrLn (show . length $ solution)
    let badAxioms = [ax | (_,Just ax,_) <- solution]
    let candidates = tail . sortBy (compare `on` length)
                     $ subsequences badAxioms
    let validCandidates = dropWhile (not . fst) -- see if removing a subset of bad axioms solves the problem
                . map (\x -> let ltm' = ltmDifference ltm (Set.fromList x)
                                 newAns = findSolution concepts ltm' rew' width depth (t,t')
                             in (null newAns,x))
                $ candidates
    let positiveUpdate = if null badAxioms
                         then Set.empty
                         else Set.singleton $ Axiom (fromIntegral v,1,True,time,time,(t,Neg,t'))
    let delta = if null validCandidates
                   then [(positiveUpdate,Set.singleton ax) | (_,Just ax,_) <- solution]
                   else [(positiveUpdate,Set.singleton ax) | ax <- (snd $ head validCandidates)]
    (ltm',changes,newRem) <- theoryUpdate vb width depth ltmSize concepts rew' graph' ltm rem' delta
    let graph'' = makeFalse graph' validCandidates
    let ltmNew = biToUni ltm' t t'
    let result = null $ findSolution concepts ltmNew rew' width depth (t,t')
    return $ (graph',pats',ltmNew,result,rew',changes,(newRem,solution,[]))
-- negative item with non-rewarding symbol in goal
  | v < 0 = do
    let ltmNew = biToUni ltm t t'
    return (graph',pats',ltmNew,True,rew',[],([],[],[]))
-- small fact with unary function
  | isUnary' t && size t < 3
    && ltmNotmember (Axiom (fromIntegral v,1,True,time,time,(t,Bi,t'))) ltm = do
    let positiveAxiom = Axiom (fromIntegral v,1,True,time,time,(t,Bi,t'))
    let rew = updateRewarding rew' item
    -- let newShapes = Map.filterWithKey (\k a -> null $ getUnary k) $ makeShapes (t,t')
    -- (graph,pats) <- updateGraph graph' pats' concepts ltm rew width depth redun newShapes
    let delta = [(Set.singleton positiveAxiom,Set.empty)]
    (ltmNew,changes,rem1) <- theoryUpdate vb width depth ltmSize concepts rew graph' ltm rem' delta
    let comput = findSolution concepts ltmNew rew width depth (t,t')
    return (graph',pats',ltmNew,True,rew,changes,(rem1,comput,[]))
  | otherwise = {-# SCC "findDelta" #-} do  -- positive item
    let positiveAxiom = Axiom (fromIntegral v,1,True,time,time,(t,Bi,t'))
    let optimumScore   = v
    let concepts' = Set.size $ Set.filter isUnitConcept concepts
    let newShapes = makeShapes (t,t')           -- Map Exp (Map String String,Rhs)
    --putStrLn $ show $ Map.size newShapes
    --putStrLn $ unlines . map show . Set.toList . Map.keysSet $ newShapes   -- (even (5 # 8))⊢(1)
    let rew = updateRewarding rew' item 
    -- when vb $ putStrLn $ "newShapes' : " ++ show newShapes
    -- newShapes <- P.mapM (updateGraph graph' concepts ltm rew width depth) $ newShapes'
    (graph,pats) <- updateGraph graph' pats' concepts (insertInLTM ltm positiveAxiom) rew width depth redun consistency newShapes -- foldl insertInShapes graph' $ map fst newShapes
    -- try to solve positive examples with current theory
    let ans = findSolution concepts ltm rew width depth (t,t')
    let solved = notnull ans && notnull (tail ans)
    -- if all positive examples solved
    if (solved && mode == Einstein) || (solved && mode == Popper && not (isSmallFact positiveAxiom))
    then do newTime <- getCurrentTime
            let updatedAxioms = [(Set.singleton (Axiom (v',freq+v,isfact,f,newTime,(lhs,dir,rhs))),Set.empty)
                                    | (_,Just (Axiom (v',freq,isfact,f,_,(lhs,dir,rhs))),_) <- ans]
            (ltm',changes,newRem) <- theoryUpdate vb width depth ltmSize concepts rew graph ltm rem' updatedAxioms
            return $! (graph,pats,ltm',True,rew,changes,(newRem,ans,[]))
    -- if some positive examples are NOT SOLVED with current theory, then:
    else do
        --let positiveRhs = [rhs | Item _ rhs _ <- pos, not (containsVar rhs)]
        let theoryFacts = Set.toList
                          . (if isBasicFact rew positiveAxiom then Set.insert positiveAxiom else id)
                          $ ltmFacts ltm
        -- generate all possible candidates for delta
        let facts = -- if isSmallFact positiveAxiom || (size positiveAxiom <= 8 && size t <= 5)
                    if isFact positiveAxiom && (size positiveAxiom <= 8 && size t <= 5) && -- isBasicFact rew positiveAxiom &&
                            (if redun then True else atMostOne (filter (\x -> Rew x `Set.notMember` rew) $ [x | x@(i,y) <- getSymbolsAx positiveAxiom, i>=1,y/=combiner]))
                         then [positiveAxiom]
                         else []
        let runContext exp source a b = 
                let x = replaceAllSubExp2 exp (Root a) (Root source)
                    y = replaceAllSubExp2 exp (Root b) (Root source)
                    ltm' = insertInLTM ltm positiveAxiom
                    (a',_) = solveAnswer width 1 concepts ltm' rew (x,Nothing,Set.empty) (Just $ Root "OK")
                    (b',_) = solveAnswer width 1 concepts ltm' rew (y,Nothing,Set.empty) (Just $ Root "OK")
                in
                    if isNothing a' || isNothing b'
                        then Nothing
                        else Just (a' == b')
        let isSynonymous a b =
                if (Axiom (0,0,True,time,time,(Root a,Bi,Root b))) `elem` theoryFacts
                then False
                else let s =  [f | f <- theoryFacts,
                                   size (axLhs f) > 1,
                                   let r = filter isJust [runContext (axLhs f) c a b | c <- (nub' $ getConsts $ axLhs f)],
                                   notnull r,
                                   and (map fromJust r)]
                  in notnull s -- length s >= 3
        let synonyms = if (Rew (0,"OK")) `Set.member` rew
                       then [Axiom (fromIntegral v,1,False,time,time,(Root c,Bi,Root syn))
                                   | c <- nub' $ getConsts t,
                                     syn <- [c' | C (0,_,_,_,_,Root c') <- Set.toList concepts, c /= c', isSynonymous c' c]
                            ]
                       else []
        let mixed = [ax | ax@(Axiom (_,_,_,_,_,(lhs,_,rhs))) <- generateMixedAxioms time concepts,
                          null [0 | f <- theoryFacts, isNeg f, f `isInstanceOf` ax],
                          satisfy concepts'
                                  [map snd (fromJust r)
                                        | f <- theoryFacts,
                                          isBi f,
                                          f `isInstanceOf` ax,
                                          let r = axiomVarBinding f ax,
                                          isJust r
                                  ] (Set.size $ getVarsSet ax) consistency
                    ]
        let ltmAx = Set.toList $ ltmAxioms ltm -- filter containsVarAx $ Set.toList ltm
        let special = Set.fromList $ concat [getConstsAx ax | ax <- ltmAx]
        let mixedPlus = [ax |   ax@(Axiom (_,_,_,_,_,(lhs,_,rhs))) <- generateFuncsAbs time [positiveAxiom],
                                isMixedPlus ax, all (\x -> x `Set.member` special) (getConstsAx ax),
                                null [0 | f <- theoryFacts, isNeg f, f `isInstanceOf` ax],
                                satisfy concepts'
                                        [map snd (fromJust r)
                                            | f <- theoryFacts,
                                              isBi f,
                                              f `isInstanceOf` ax,
                                              let r = axiomVarBinding f ax,
                                              isJust r
                                        ]  (Set.size $ getVarsSet ax) consistency ]
        let units = nub' [f | C (0,_,_,_,_,Root f) <- Set.toList concepts]
        --let graphAlg = Map.filterWithKey
        --                (\(x,y) (b,set) -> 
        --                        b && (not . Set.null $ set) && satisfy concepts' (Set.toList set) (Set.size $ getVarsSet' x) consistency
        --                ) graph
        --let algebraic = [Axiom (0,1,False,time,time,(x,Bi,y)) | ((x,y),_) <- Map.toList graphAlg]
        -- Verbose -> Int -> Int -> Set Concept -> LTM -> Set Rewarding -> Axiom -> [[String]]
        let algebraic = [Axiom (0,1,False,time,time,(x,Bi,y))
                            |   ((x,y),(Valid,set)) <- Map.toList graph,
                                -- (not . Set.null $ set),
                                ltmNotmember (Axiom (0,1,False,time,time,(x,Bi ,y))) ltm,
                                ltmNotmember (Axiom (0,1,False,time,time,(x,Uni,y))) ltm
                                --let str = findConvergence False width depth concepts ltm rew (Axiom (0,1,False,time,time,(x,Bi,y))),
                                --satisfy concepts' (Set.toList set) (Set.size $ getVarsSet' x) consistency
                        ]
        let prevRecExamples = if isUnary'' . fst' . axiom' $ positiveAxiom
                              then [(((Unary (Oper f) x),right),ltmDelete ax ltm)
                                        | ax@(Axiom (_,_,_,_,_,((Unary (Oper f) x),Bi,right))) <- Set.toList $ ltmFacts ltm,
                                          f == getUnaryOper t]
                              else []
        let computesAllExamples ax = 
                let result = 
                     [r == ans
                        | (r,(Just ans,_)) <- [(right,solveAnswer width depth concepts (insertInLTM ltmExp ax) rew (left,Nothing,Set.empty) (Just right))
                                             | ((left,right),ltmExp) <- prevRecExamples]]
                in length result >= 2 && and result
        
        let recursive = if isUnary positiveAxiom --isBasicFact rew positiveAxiom 
                        then [ax | ax <- generateFuncsRec ltm width depth special time concepts positiveAxiom,
                                   computesAllExamples ax
                                   --positiveAxiom `isInstanceOf` ax
                                   --satisfy concepts' [map snd (fromJust r)
                                   --            |   f <- theoryFacts,
                                   --                f `isInstanceOf` ax,
                                   --                let r = axiomVarBinding f ax,
                                   --                isJust r]
                                   --        (Set.size $ getVarsSet ax)
                                   --        consis 
                                ]
                        else []
        let deltas = -- remove redundant candidates
                     (\x -> if redun == True 
                              then x
                              else filter (\ax@(Axiom (_,_,_,_,_,(t1,_,t2))) -> 
                                                if isSmallFact ax
                                                then True
                                                else let ltmT = (ltmDelete ax ltm)
                                                         sol = findSolution concepts ltmT rew width depth (t1,t2)
                                                     in null sol
                                          ) x)
                     . filter (\ax -> notProvable ax ltmAx)
                     . filter (\ax -> ltmNotmember ax ltm)
                     . filter (\ax -> not (ax `elem` rem'))
                     $ nub' (facts ++ mixed ++ mixedPlus ++ algebraic ++ synonyms) -- ++ recursive)
        (delta',diverted) <- partitionM (hasNoDivergence vb width depth concepts ltm rew) deltas
        
        -- time <- getCurrentTime
        let delta = case mode of
                    Einstein -> if ltmSize <= size ltm && ltmSize > 0
                                then [(Set.singleton d,Set.singleton nd) | d <- delta',nd <- Set.toList (allAxioms ltm),
                                                                           (not . isSmallFact) nd]
                                else [(Set.singleton d,Set.empty) | d <- delta']
                    Popper -> [(Set.singleton d,Set.empty) | d <- delta']
        --putStrLn $ "delta: " ++ show (length delta)
        result <- occam vb width depth optimumScore [] [item] positiveAxiom concepts ltm rew delta
        --putStrLn $ if isNothing result then "Nothing" else "Just"
        (ltmNew,changes,rem1) <- theoryUpdate vb width depth ltmSize concepts rew graph ltm rem' $ maybeToList result
        (ltmNew2,changes',rem2,comput) <- 
                            if mode == Popper
                            then do
                                let newans = findSolution concepts ltmNew rew width depth (t,t')
                                newTime <- getCurrentTime
                                let updatedAxioms = [(Set.singleton (Axiom (v',freq+v,isfact,f,newTime,(lhs,dir,rhs))),Set.empty)
                                                            | (_,Just (Axiom (v',freq,isfact,f,_,(lhs,dir,rhs))),_) <- newans]
                                (a,b,c) <- theoryUpdate vb width depth ltmSize concepts rew graph ltmNew rem' updatedAxioms
                                return (a,b,c,newans)
                            else return (ltmNew,[],rem1,ans)
        (ltmNew3,changes'',rem3) <- 
                            if redun == True -- if redundancy is false, then remove existing axioms solved by the new axiom.
                                then return (ltmNew2,[],rem2)
                                else do let toRemove = snd
                                                       . foldl (\(l,b) ax@(Axiom (_,_,_,_,_,(t,_,t'))) ->
                                                                    let ltmT = (ltmDelete ax l)
                                                                        sol = findSolution concepts ltmT rew width depth (t,t')
                                                                    in if null sol
                                                                       then (l,b)
                                                                       else (ltmT,ax:b))
                                                               (ltmNew2,[])
                                                       . reverse
                                                       . sortBy (compare `on` size)
                                                       . (\(Ltm fc ax) -> (Set.toList (Set.filter (not . isSmallFact) fc))
                                                                          ++ Set.toList ax)
                                                       $ ltmNew2
                                        theoryUpdate vb width depth ltmSize concepts rew graph ltmNew2 rem' [(Set.empty, Set.fromList toRemove)]
        return $ (graph,pats,ltmNew3,isJust result || solved,rew,changes ++ changes' ++ changes'',(rem3,comput,[]))
-- [["P","F"],["P","P"],["P","Q"],["P","R"],["Q","P"],["Q","Q"],["Q","R"],["R","F"],["R","P"],["R","Q"],["R","R"],["T","R"]]
-- 2

-- (x # (y + z)) == (x # (y # z))
-- Valid
-- [[0,0,0],[0,0,1],[0,0,4],[0,0,6],
-- [1,0,0],[1,0,4],
-- [2,0,1],[2,0,6],[2,0,9],
-- [3,0,4],
-- [4,0,1],
-- [5,0,0],
-- [6,0,0],[6,0,2],[6,0,6],[7,0,0],[7,0,1],[7,0,6],[8,0,0],[9,0,0],[9,0,6],[9,0,9]])
-- satisfy (number of concepts) [["1","0"]] (variable count) consistentcy
satisfy :: Int -> [[String]] -> Int -> Consistency -> Bool
satisfy concepts values varCount consis | null values || varCount < 1 = False
satisfy concepts values varCount consis | any (\x -> length x /= varCount) values = False
satisfy concepts values varCount False = length (nub' values) >= varCount -- [[0]]

satisfy concepts values 1 _  = length (nub' values) >= (if concepts > 2 then 3 else 2)  -- [[0],[1]]
satisfy concepts values varCount consis = 
    let result1' = map (\x -> (head (head x),map tail x))             -- [ (0,[[1],[7]]), (1,[[0],[1]]), (2,[[0]]) ]
                   . groupBy ((==) `on` (head))                         -- [ [[0,1],[0,7]], [[1,0],[1,1]], [[2,0]] ]
                   . sortBy (compare `on` (head))                       -- [[0,1],[0,7],[1,0],[1,1],[2,0]]
                   $ values                                             -- [[0,1],[0,7],[1,0],[1,1],[2,0]]
        result1 = map (\(x,y) -> (x,satisfy concepts                    -- [ (0,True), (1,True), (2,False) ]
                                    (if concepts > 2 then filter (any (/=x)) y else y)
                                    (varCount - 1) consis)
                                    -- && if concepts > 2 then not (all (==[x]) y) else True)
                      ) $ result1'
        result2 = map (\(x,y) -> (x,satisfy concepts y (varCount - 1) consis)) -- [ (0,True), (1,True), (7,False)]
                 . map (\x -> (head (head x),map tail x))             -- [ (0,[[1],[2]]), (1,[[0],[1]]), (7,[[0]]) ]
                 . groupBy ((==) `on` (head))                         -- [ [[0,1],[0,2]], [[1,0],[1,1]], [[7,0]] ]
                 . sortBy (compare `on` (head))                       -- [[0,1],[0,2],[1,0],[1,1],[7,0]]
                 $ map reverse values                                 -- [[1,0],[7,0],[0,1],[1,1],[0,2]]
        results1 = [True | (_,True) <- result1]
        results2 = [True | (_,True) <- result2]
        pass = if consis
                    then 2 -- (if concepts > 2 then 3 else 2) 
                    else 1
    in 
        -- length (nub' (map head values)) >= pass
        -- satisfy (nub' $ map tail values) (varCount - 1) consis
        length results1 >= pass
        -- || length (nub' $ map snd result1') >= pass * (if concepts > 2 then 3 else 2)
        -- && length results2 >= pass

findConvergence :: Verbose -> Int -> Int -> Set Concept -> LTM -> Set Rewarding -> Axiom -> [[String]]
findConvergence _ _ _ _ _ _ ax | null (getVarsAx ax) = []
findConvergence vb width depth concepts ltm rew ax@(Axiom (_,_,_,_,_,(x,dir,y))) =
    let ltmClosed = Ltm (ltmFacts ltm) Set.empty
        ltmDeepClosed = Ltm (Set.filter axIsBi $ ltmFacts ltm) Set.empty
        ltm1 = if dir == Bi then ltmDeepClosed else ltmClosed
        vars = sort . nub' . getVarsAx $ ax
        varLength = length vars
        consts = [e | C (0,_,_,_,_,(Root e)) <- Set.toList concepts]
        substs = filter (\x -> length x == varLength) $ subsequences consts
        substitutions = [(s, foldl (\(x',y') (v,c) -> (replaceAllSubExp2 x' (makeV v) (Root c),replaceAllSubExp2 y' (makeV v) (Root c))) (x,y) $ zip vars s)
                            | s <- substs]
        results = map (\(s,(x,y)) ->
                           let (x',_) = solveAnswer width depth concepts ltm1 rew (x,Nothing,Set.empty) Nothing
                               (y',_) = solveAnswer width depth concepts ltmDeepClosed rew (y,Nothing,Set.empty) Nothing
                               result = if isNothing x' || isNothing y'
                                        then False
                                        else x' == y'
                           in (s,result)
                       )
                       $ substitutions
    in [x | (x,True) <- results]

-- result = replaceAllSubExp2 (Root "T") (Var "x") (Root "T")

hasDivergence :: Verbose -> Int -> Int -> Set Concept -> LTM -> Set Rewarding -> Axiom -> IO Bool
hasDivergence vb a b c d e f = --do result <- hasNoDivergence vb a b c d e f
                               --   return $ not result
                               return False
-- (\x | \y),(\x)
hasNoDivergence :: Verbose -> Int -> Int -> Set Concept -> LTM -> Set Rewarding -> Axiom -> IO Bool
hasNoDivergence vb width depth concepts ltm' rew ax@(Axiom (_,_,_,_,_,(x,dir,y))) = do
    let ltmClosed = Ltm (ltmFacts ltm') Set.empty
    let ltmDeepClosed = Ltm (Set.filter axIsBi $ ltmFacts ltm') Set.empty
    let ltm1 = if dir == Bi then ltmDeepClosed else ltmClosed
    let vars' = getVarsAx $ ax
    if null vars'
    then return True
    else do  -- at least one
    let vars = nub' vars'
    let units = [e | C (0,_,_,_,_,e@(Root _)) <- Set.toList concepts]
    let substitutions' = 
            nub' $ foldl (\axioms v -> [(replaceAllSubExp2 x' (makeV v) c,replaceAllSubExp2 y' (makeV v) c)
                                                | (x',y') <- axioms,
                                                  v `Set.member` (getVarsSet' x'),
                                                  c <- units])
                         [(x,y)] vars
    substitutions <- shuffle $ filter (\(x,y) -> not (containsVar x || containsVar y)) substitutions'
    results <- P.mapM (\(x,y) -> do
                           let (x',_) = solveAnswer width depth concepts ltm1 rew (x,Nothing,Set.empty) Nothing
                           let (y',_) = solveAnswer width depth concepts ltmDeepClosed rew (y,Nothing,Set.empty) x'
                           let result = if isNothing x'
                                        then True
                                        else if isRoot y
                                                then (fromJust x') == y
                                                else if isJust y'
                                                      then x' == y'
                                                      else True
                           --return $ trace (show x ++ "=" ++ show x' ++ ", " ++ show y ++ "=" ++ show y' ++ " : " ++ show result) 
                           return               ((x,y),result)
                       )
                       $ substitutions
    return $ and (map snd results)

occam :: Verbose -> Width -> Depth -> Int -> [Item] -> [Item] -> Axiom
         -> Set Concept -> LTM -> Set Rewarding -> [Delta]
         -> IO (Maybe Delta)
occam vb width depth optimumScore neg pos posAx concepts ltm rew delta = do
        result' <- P.mapM (timeout timeLimit . performance width depth concepts ltm rew neg pos posAx) delta
        let result = [(x,y,z) | Just (Just x,y,z,_) <- result']
        return . listToMaybe . map fst' . take 1 . sortBy preference $ result

findInconsistent :: Verbose -> Int -> Int -> Set Concept -> Set Rewarding -> LTM -> IO (Set Axiom)
findInconsistent vb width depth concepts rew ltm = -- return Set.empty
    (liftM Set.fromList) . filterM (hasDivergence vb width depth concepts ltm rew) $ Set.toList (allAxioms ltm)

theoryUpdate :: Verbose -> Int -> Int -> Int
                -> Set Concept -> Set Rewarding -> Graph Pattern
                -> LTM -> RecentlyRemoved -> [Delta]
                -> IO (LTM,[(Int,Axiom)],RecentlyRemoved)
theoryUpdate vb width depth ltmSize concepts rew graph ltm rem delta = do
    time <- getCurrentTime
    let invalid = Set.fromList [Axiom (0,1,False,time,time,(x,Bi,y))
                                        |   ((x,y),(Invalid,_)) <- Map.toList graph,
                                            ltmMember (Axiom (0,1,False,time,time,(x,Bi ,y))) ltm]
    let neg = Set.unions [n | (_,n) <- delta]
    let pos = Set.difference (Set.unions [p | (p,_) <- delta])
                             (Set.union invalid $ Set.fromList rem)
    let ltm1 = ltmDifference ltm neg
    let ltm2 = foldl insertInLTM ltm1 $ Set.toList pos
    let ltm3 = ltmUpdateViability time decay ltm2
    inconsistent <- findInconsistent vb width depth concepts rew ltm3
    let ltm4 = ltmDifference ltm3 inconsistent
    let more = size ltm4 - ltmSize
    let comp a b = if axFirst a == axLast a
                    then if axFirst b == axLast b
                            then compare (axFirst a) (axFirst b)
                            else GT
                    else if axFirst b == axLast b
                            then LT
                            else compare (axV a) (axV b)
    let (ltm5,neg2) = if more > 0
                        then let (smallFacts',notSmallFacts') = partition (isSmallFact) $ Set.toList $ allAxioms ltm4
                                 smallFacts = sortBy (comp) smallFacts'
                                 notSmallFacts = sortBy comp notSmallFacts'
                                 extras = if length notSmallFacts < more
                                              then notSmallFacts ++ take (more - length notSmallFacts) smallFacts
                                              else take more notSmallFacts
                                 result = ltmDifference ltm4 $ Set.fromList extras
                             in (result,Set.fromList extras)
                        else (ltm4,Set.empty)
    let neg3 = Set.filter (\(Axiom (_,_,_,_,_,(x,_,y))) -> 
                                            if (x,y) `Map.member` graph 
                                            then (\x -> fst x == Invalid) (graph Map.! (x,y)) 
                                            else False) $ ltmAxioms ltm5
    let ltm6 = if Set.null neg3 then ltm5 else ltmDifference ltm5 neg3
    let negative = map (\a -> (-1,a)) . Set.toList $ (Set.unions [neg,neg2,neg3,inconsistent])
    let positive = map (\a -> ( 1,a)) . Set.toList $ Set.filter (\p -> p `ltmNotmember` ltm1) pos
    let shared = [a | (i,a) <- (positive ++ negative), (a `elem` (map snd negative)) && (a `elem` (map snd positive))]
    
    let changes = [(i,a) | (i,a) <- (negative ++ positive), not (a `elem` shared) ]
    let rem' = Set.toList $ Set.unions [neg,neg2,neg3,inconsistent]
    return $! (ltm6,changes,rem')

-- for Language, the rhs must be a string
rhsIsTag (Axiom (_,_,_,_,_,(_,_,Var _))) = True
rhsIsTag _ = False

lhsIsVar (Axiom (_,_,_,_,_,(Var _,_,_))) = True
lhsIsVar _ = False

lhsIsFuncVar (Axiom (_,_,_,_,_,(Unary _ (Var _),_,_))) = True
lhsIsFuncVar _ = False

lhsIsSame (Axiom (_,_,_,_,_,(x,_,_))) (Axiom (_,_,_,_,_,(p,_,_))) = x == p
-----------------------

---------------------- Priority functions -------------------------------------
deltaSmallest :: [Axiom] -> [([Axiom],Int,Int)] -> [([Axiom],Int,Int)]
deltaSmallest _ [] = []
deltaSmallest _ [x] = [x]
deltaSmallest _ deltas = 
    let minSize = minimum [len | (_,_,len)  <- deltas]
    in  [(ax,perf,len) | (ax,perf,len) <- deltas, len == minSize]

deltaMaxVarTokens :: [Axiom] -> [([Axiom],Int,Int)] -> [([Axiom],Int,Int)]
deltaMaxVarTokens _ [] = []
deltaMaxVarTokens _ [x] = [x]
deltaMaxVarTokens _ deltas = 
    let deltas' = [(ax,perf,len,sum (map countVars ax)) | (ax,perf,len)  <- deltas]
        maxVarCount = maximum [varCount | (ax,perf,len,varCount) <- deltas']
    in [(ax,perf,len) | (ax,perf,len,vars) <- deltas', vars == maxVarCount]

deltaMinVarTypes :: [Axiom] -> [([Axiom],Int,Int)] -> [([Axiom],Int,Int)]
deltaMinVarTypes _ [] = []
deltaMinVarTypes _ [x] = [x]
deltaMinVarTypes _ deltas =
    let deltas' = [(ax,perf,len,sum (map countVarsUnique ax)) | (ax,perf,len)  <- deltas]
        maxVarCount = maximum [varCount | (ax,perf,len,varCount) <- deltas']
    in [(ax,perf,len) | (ax,perf,len,vars) <- deltas', vars == maxVarCount]

preference = 
         preferUseful `och` preferSmallFact `och` preferSmallest `och` preferMaxUtility `och` preferMaxVarTokens `och` preferMinVarTypes
        --preferSmallest `och` preferMaxVarTokens `och` preferMinVarTypes

preferUseful :: (Delta,Bool,Int) -> (Delta,Bool,Int) -> Ordering
preferUseful (_,b1,_) (_,b2,_) = compare b2 b1

preferMaxUtility :: (Delta,Bool,Int) -> (Delta,Bool,Int) -> Ordering
preferMaxUtility (_,_,x) (_,_,y) = compare y x

preferSmallFact :: (Delta,Bool,Int) -> (Delta,Bool,Int) -> Ordering
preferSmallFact ((x,_),_,_) ((y,_),_,_) | not (Set.null x || Set.null y)
        = compare (and . Set.toList $ Set.map isSmallFact y)
                  (and . Set.toList $ Set.map isSmallFact x)
preferSmallFact _ _ = EQ

preferSmallest :: (Delta,Bool,Int) -> (Delta,Bool,Int) -> Ordering
preferSmallest ((x,_),_,_) ((y,_),_,_) | not (Set.null x || Set.null y) = compare (sum . Set.toList $ Set.map size x) (sum . Set.toList $ Set.map size y)
preferSmallest _ _ = EQ

preferMaxVarTokens :: (Delta,Bool,Int) -> (Delta,Bool,Int) -> Ordering
preferMaxVarTokens ((x,_),_,_) ((y,_),_,_) | not (Set.null x || Set.null y)
        = compare (Down . length $ concatMap getVarsAx $ Set.toList x) (Down . length $ concatMap getVarsAx $ Set.toList y)
preferMaxVarTokens _ _ = EQ

preferMinVarTypes :: (Delta,Bool,Int) -> (Delta,Bool,Int) -> Ordering
preferMinVarTypes ((x,_),_,_) ((y,_),_,_) | not (Set.null x || Set.null y)
        = compare (length . nub' $ concatMap getVarsAx $ Set.toList x) (length . nub' $ concatMap getVarsAx $ Set.toList y)
preferMinVarTypes _ _ = EQ

och :: (a -> a -> Ordering) 
        -> (a -> a -> Ordering)
        -> a -> a -> Ordering
och f1 f2 x y = if result1 == EQ then f2 x y else result1
    where result1 = f1 x y

performance :: Int -> Int 
            -> Set Concept -> LTM -> Set Rewarding
            -> [Item] -> [Item] -> Axiom
            -> Delta -> IO (Maybe Delta,Bool,Int,Int)
--performance width depth concepts ltm rew negEx posEx d@(Nothing,Nothing) = return (Nothing,0,0)
performance width depth concepts ltm rew negEx posEx posAx d@(posFunc,negFunc) = do
    let newLtm = foldl insertInLTM (ltmDifference (ltmDifference ltm negFunc) (Set.singleton posAx)) $ Set.toList posFunc
    let ans = map (\(Item a b v) ->
                        let solution = findSolution concepts newLtm rew width depth (a,b)
                            len = length solution
                            result = (not . null) solution 
                            useful = any (\ax -> Set.member ax posFunc) [ax | (_,Just ax,_) <- solution]
                        in (result,useful,v,len))
               $ posEx ++ negEx
    let util = sum [v | (True,_,v,_) <- ans]
    let compSize = sum [x | (_,_,v,x) <- ans, v >= 0]
    let ansPos = [x | (x,_,v,_) <- ans, v >= 0]
    let ansNeg = [x | (x,_,v,_) <- ans, v < 0]
    let useful = or [u | (_,u,v,_) <- ans, v >= 0]
    if or ansNeg
    then return (Nothing,useful,util,compSize)
    else do
        if null ansPos || and ansPos
        then return $ (Just d,useful,util,compSize)
        else return $ (Nothing,useful,util,compSize)

generateMixedAxioms :: UTCTime -> Set Concept -> [Axiom]
generateMixedAxioms time concepts' =
    let v = makeV "x"
        concepts = Set.toList concepts'
        consts = [e | C (0,_,_,_,_,e@(Root _)) <- concepts]
        unary  = [e | C (1,_,_,_,_,e@(Root _)) <- concepts]
        binary = [e | C (2,_,_,_,_,e@(Root _)) <- concepts]
        exps1 = [Axiom (0,1,False,time,time,(exp,Bi,c)) | i <- [2..4], c <- consts, exp <- generateExps i [v,c] unary binary]
        exps2 = [Axiom (0,1,False,time,time,(exp,Bi,v)) | i <- [2..4], c <- consts, exp <- generateExps i [v,c] unary binary]
        exps = nub' . filter isMixed $ exps1 ++ exps2
    in  exps

generateAlgebraic :: UTCTime -> [Concept] -> [Axiom]
generateAlgebraic time concepts = 
    let vars = [makeV [v] | v <- "xyz"]
        unary  = nub' [e | C (arit,_,_,_,_,e@(Root f)) <- concepts, arit==1]
        binary = nub' [e | C (arit,_,_,_,_,e@(Root f)) <- concepts, arit==2]
        exps' = [(i,generateExps i vars unary binary) | i <- [1..5]]
        exps = nub' $ filter isAlgebraic $
                        [Axiom (0,1,False,time,time,(x,Bi,y))
                                     | i <- [1..5],
                                       j <- [1..5],
                                       x <- fromMaybe [] (lookup i exps'),
                                       y <- fromMaybe [] (lookup j exps')]
    in  exps

-- generate recursive axioms
-- one base case from IP
-- one recursive case of the form
--      f(big) ->> ... f(small) ...
--   where, f(small) has size 0, and size small < size big
generateFuncsRec :: LTM -> Width -> Depth -> Set String -> UTCTime -> Set Concept -> Axiom -> [Axiom]
generateFuncsRec ltm width depth special time concepts' base@(Axiom (_,_,_,_,_,(t@(Unary f c),dir,t'))) = 
    let concepts = Set.toList concepts'
        d = 6
        vars = [makeV [c] | c <- "xyz"]
        units = nub' $ vars ++ [exp | C (arit,_,_,_,_,exp) <- concepts, arit==0, size exp == 1]
        binary = [exp | C (arit,_,_,_,_,exp) <- concepts, arit==2]
        lhs = Unary f (replaceConstsWithVars vars c)
        lhsVars = getVarsSet' lhs
        small' = [z | j <- [1..3],
                      z <- generateExps j units [] binary,
                      containsVar z,
                      sort (nub' $ getVars z) == sort (getVars z), -- every variable only once
                      all (\x -> Set.member x lhsVars) (getVars z) -- pure
                    ]
        small =     filter (\x -> not . fst $ findAnswerDecl Set.empty ltm Set.empty width depth (x,lhs))
                    . filter isRecursiveRhs
                    . filter (/=lhs)
                    . map (Unary f)
                    $ small'
        result = filter (/= base)
                 . nub'
                 . filter isPure
                 $ [Axiom (0,1,False,time,time,(lhs,Bi,rhs))
                      | rhs <- concat [generateExpsRec i small units [] binary | i <- [0..(d - (size lhs))]],
                               -- ++ generateExps 1 units [] binary,
                        not (containsExp rhs lhs),
                        containsVar rhs,
                        isRecursiveRhs rhs
                        ]
    in -- trace ("result: " ++ unlines (map (show . axPair) result)
              -- "\nsmall': " ++ unlines (map show small')
              -- ++ "\nsmall: " ++ unlines (map show small)
              -- ++ "\nspecial: " ++ unlines (map show special)
              -- ++ "\nunits: " ++ unlines (map show units)
              -- ++ "\nbinary: " ++ unlines (map show binary)
              -- ++ "\nlhs: " ++ show lhs
       --       ++ "\nrhs: " ++ unlines (map show [generateExpsRec i small units [] binary | i <- [0..(d - (size lhs))]])
             -- ) $
            result
generateFuncsRec _ _ _ _ _ _ _ = []

isRecursiveRhs (Unary _ (Var _)) = True
isRecursiveRhs (Unary _ (Binary _ (Var _) (Root _))) = True
isRecursiveRhs (Binary _ a (Root _)) = isRecursiveRhs a
isRecursiveRhs _ = False
-- generate abstractions of given axioms
-- e.g. for 1+(2+3), it returns x+(2+3), x+(y+z), etc.
generateFuncsAbs :: UTCTime -> [Axiom] -> [Axiom]
generateFuncsAbs _ [] = []
generateFuncsAbs time axioms = 
    let vars = [makeV [c] | c <- "xyz"]
        exps = nub' $
               [Axiom (0,1,False,time,time,((foldl (\x' (var',sub') -> replaceAllSubExp2 x' var' sub') x v),dir,(foldl (\x' (v',s') -> replaceAllSubExp2 x' v' s') y v))) -- replace sub with v in ip
                  | (Axiom (_,_,_,_,_,(x,dir,y))) <- axioms,
                    sub <- subsequences (nub' (getSubExp x ++ getSubExp y)),
                    notnull sub,
                    var <- subsequences vars,
                    notnull var,
                    length var == length sub,
                    -- not (sub `elem` vars),
                    let v = zip var sub
               ]
    in filter (containsVar . axLhs) exps
    --in filter (\(Axiom x y _) -> notnull [x | x@(Var _) <- getSubExp x]) exps

-- generate facts
generateFacts :: UTCTime -> Int -> [Concept] -> [Axiom]
generateFacts _ _ [] = []
generateFacts _ len _ | len < 3 || len > 6 = []
generateFacts time 3 concepts = 
    let consts = nub' [exp | C (arit,_,freq,_,_,exp) <- concepts, arit==0]
        unary  = nub' [exp | C (arit,_,freq,_,_,Root exp) <- concepts, arit==1]
        facts  = nub' [Axiom (0,1,False,time,time,((makeU u c),Bi,d)) | c <- consts, u <- unary, d <- consts]
    in filter isFact facts
generateFacts time 4 concepts = 
    let consts = nub' [e | C (arit,_,freq,_,_,e) <- concepts, arit==0]
        unary  = nub' [e | C (arit,_,freq,_,_,Root e) <- concepts, arit==1]
        binary = nub' [e | C (arit,_,freq,_,_,Root e) <- concepts, arit==2]
        factsB = nub' [Axiom (0,1,False,time,time,((makeB b c d),Bi,e))
                        | c <- consts,  d <- consts, b <- binary, e <- consts]
        factsU = nub' [Axiom (0,1,False,time,time,((makeU u1 c),Bi,(makeU u2 d)))
                        | c <- consts, u1 <- unary, d <- consts, u2 <- unary]
    in filter isFact $ factsB ++ factsU
generateFacts time 5 concepts = 
    let consts = nub' [e | C (arit,_,freq,_,_,e) <- concepts, arit==0]
        unary  = nub' [e | C (arit,_,freq,_,_,Root e) <- concepts, arit==1]
        binary = nub' [e | C (arit,_,freq,_,_,Root e) <- concepts, arit==2]
        facts = nub' [Axiom (0,1,False,time,time,((makeB b c d),Bi,(makeU u e)))
                        | b <- binary, u <- unary,
                          c <- consts,  d <- consts, e <- consts]
    in filter isFact facts
generateFacts time 6 concepts = 
    let consts = nub' [e | C (arit,_,freq,_,_,e) <- concepts, arit==0]
        binary = nub' [e | C (arit,_,freq,_,_,Root e) <- concepts, arit==2]
        facts = nub' [Axiom (0,1,False,time,time,((makeB b1 c d),Bi,(makeB b2 e f)))
                        | b1 <- binary, b2 <- binary,
                          c <- consts,  d <- consts,
                          e <- consts,  f <- consts]
    in filter isFact facts

generateRelevant :: UTCTime -> [Concept] -> [Axiom]
generateRelevant _ [] = []
generateRelevant time concepts = 
    let vars   = [makeV [v] | v <- "zyx"]
        consts = nub' [makeR e | C (arit,_,freq,_,_,Root e) <- concepts, arit==0]
        -- unary  = nub' [e | (arit,freq,_,_,(Root e)) <- concepts, arit==1]
        binary = nub' [e | C (arit,_,freq,_,_,Root e) <- concepts, arit==2]
        relevant = nub' $ concat
                    [[Axiom (0,1,False,time,time,((makeB b v1 v2),Bi,c)),
                      Axiom (0,1,False,time,time,((makeB b v1 c),Bi,v2)),
                      Axiom (0,1,False,time,time,((makeB b c v2),Bi,v1))]
                        | c <- consts, b <- binary,
                          v1 <- vars, v2 <- vars]
    in relevant
        
-- generate all axioms of given size
generateFuncsAll :: UTCTime -> [Concept] -> Int -> [Item] -> [Axiom]
generateFuncsAll _ _  len _   | len < 2 = []
generateFuncsAll time concepts len pos =
    let variables = "zyx"
        parts = [lhs | (Item lhs _ _) <- pos] ++ [rhs | (Item _ rhs _) <- pos]
        units = nub' $ [x | x <- (concatMap getSubExp parts), size x == 1]
                      ++ [makeV [c] | c <- variables]
                      ++ [exp | C (arit,_,freq,_,_,exp) <- concepts, arit==0]
                                -- size exp == 1]
        unary  = nub' [exp | C (arit,_,freq,_,_,exp) <- concepts, arit==1] -- ,size exp == 1]
                    -- ++ [HsVar x | (HsApp (HsVar x) _) <- parts]
        binary = nub' [exp | C (arit,_,freq,_,_,exp) <- concepts, arit==2] -- ,size exp == 1]
                    -- ++ [HsVar x | (HsInfixApp _ (HsQVarOp x) _) <- parts]
        exps = [ (i, nub' (generateExps i units unary binary)) | i <- [1..(len-1)] ]
        result = concat
                 [ [Axiom (0,1,False,time,time,(p,Bi,q)), Axiom (0,1,False,time,time,(q,Bi,p))]
                      | i <- [1 .. (len `div` 2)],
                        q <- fromJust (lookup i exps),
                        p <- fromJust (lookup (len - i) exps),
                        p /= q,
                        not (size p == 1 && size q == 1)
                  ]
    in  nub' result

generateExpsRec :: Int -> [Exp] -> [Exp] -> [Exp] -> [Exp] -> [Exp]
generateExpsRec len _  _     _  _ | len < 0 = []
generateExpsRec 0   fs _     _  _  = fs
generateExpsRec 1   fs units f1 _  = [makeU x f | Root x <- f1, f <- fs] ++ units
generateExpsRec 2   fs units _  f2
        = concat [[makeB op f x,makeB op x f]
                        | f <- fs,
                          Root op <- f2,
                          x <- units]
generateExpsRec 3   fs units f1 f2
    =   let exps2f = [makeU x f | Root x <- f1, f <- fs]
            exps2  = units
            exps1  = generateExpsRec 2 fs units f1 f2
        in concat
            [[makeB op x y, makeB op y x]
                | x <- exps2f,
                  y <- exps2,
                  Root op <- f2]
            ++ [makeU op x
                    | Root op <- f1,
                      x <- exps1]
generateExpsRec len fs units f1 f2
    =   let exps2f = generateExpsRec (len-2) fs units f1 f2
            exps2 = generateExpsRec (len-2) [] units f1 f2
            exps1 = generateExpsRec (len-1) fs units f1 f2
        in concat
            [[makeB op x y, makeB op y x]
                | x <- exps2f,
                  y <- exps2,
                  Root op <- f2]
            ++ [makeU op x
                    | Root op <- f1,
                      x <- exps1]

generateExps :: Int -> [Exp] -> [Exp] -> [Exp] -> [Exp]
generateExps len _ _ _ | len < 1 = []
generateExps 1 units _ _ = units
generateExps 2 units funcs1 _ = [makeU x y | Root x <- funcs1, y <- units]
generateExps len units funcs1 funcs2
    = let exps2 = generateExps (len-2) units funcs1 funcs2
          exps1 = generateExps (len-1) units funcs1 funcs2
      in [makeB op x y
            | (Root op) <- funcs2,
              i <- [1..(len-2)],
              x <- generateExps i units funcs1 funcs2,
              y <- generateExps (len-1-i) units funcs1 funcs2
              ]
         ++ [makeU op arg
              | (Root op) <- funcs1,
                arg <- exps1]

-- get free variables, those that occur in lhs but not in rhs
freeVars :: Axiom -> [Exp]
freeVars f@(Axiom (_,_,_,_,_,(t,_,t'))) =
    let rhsvars = getVars t
        lhsvars = getVars t'
    in map makeR $ nub' [v | v <- lhsvars, not (v `elem` rhsvars)]

generate :: Gen a -> IO a
generate g = do
    values <- sample' g
    return $ head values


filterP          :: (a -> IO Bool) -> [a] -> IO [a]
filterP _ []     =  return []
filterP p (x:xs) =  do
    vb <- newEmptyMVar
    flg <- p x
    forkIO (filterP p xs >>= putMVar vb)
    ys <- takeMVar vb
    return (if flg then x:ys else ys)

shuffle :: [a] -> IO [a]
shuffle xs = do
        ar <- newArray n xs
        forM [1..n] $ \i -> do
            j <- randomRIO (i,n)
            vi <- readArray ar i
            vj <- readArray ar j
            writeArray ar j vi
            return vj
  where
    n = length xs
    newArray :: Int -> [a] -> IO (IOArray Int a)
    newArray n xs =  newListArray (1,n) xs

partitionM :: (a -> IO Bool) -> [a] -> IO ([a],[a])
partitionM p xs = do
        (left,right) <- foldM (select p) ([],[]) xs
        return (reverse left, reverse right)

select :: (a -> IO Bool) -> ([a], [a]) -> a -> IO ([a], [a])
select p ~(ts,fs) x =
    do  result <- p x
        if result
        then return (x:ts,fs)
        else return (ts, x:fs)

    
{-                
printAgent :: Agent -> IO String
printAgent (Agent (filename,comments) (width,depth,axiom,(redun,consis,mode,iter)) (axioms,concepts,graph,_,_)) = do
    let s1 = if take 2 (strip comments) == "{-"
             then comments ++ "-}\n"
             else ""
    time <- getCurrentTime
    let s2 = s1 ++ "(A,0,0," ++ show time ++ "," ++ show time ++ ",(\\v Width)," ++ show width ++ ")\n"
    let s3 = s2 ++ "(A,0,0," ++ show time ++ "," ++ show time ++ ",(\\v Depth)," ++ show depth ++ ")\n"
    let s4 = s3 ++ "(A,0,0," ++ show time ++ "," ++ show time ++ ",(\\v LtmSize)," ++ show axiom ++ ")\n"
    let s5 = s4 ++ "(A,0,0," ++ show time ++ "," ++ show time ++ ",(\\v Redundancy)," ++ show redun ++ ")\n"
    let s6 = s5 ++ "(A,0,0," ++ show time ++ "," ++ show time ++ ",(\\v Consistency)," ++ show consis ++ ")\n"
    let s7 = s6 ++ "(A,0,0," ++ show time ++ "," ++ show time ++ ",(\\v Mode)," ++ show mode ++ ")\n"
    let s8 = s7 ++ "(A,0,0," ++ show time ++ "," ++ show time ++ ",(\\v Iterations)," ++ show iter ++ ")\n"
    let s9 = s8 ++ (unlines . map show $ Set.toList axioms)
    let s10 = s9 ++ (unlines $ map show $ Set.toList concepts)
    let s11 = s10 ++ (unlines $ map show $ getEdges graph)
    return s11

--  OLD UNUSED CODE

chooseBestDelta :: [Axiom] -> [(Delta,Int,Int)] -> Maybe Axiom
chooseBestDelta _ [] = Nothing
chooseBestDelta _ [(x,_,_)] = Just x
chooseBestDelta lx deltas =
    let deltas' = [(ax,perf,len,countVars ax) | (ax,perf,len)  <- deltas]
        maxVarCount = maximum [varCount | (ax,perf,len,varCount) <- deltas']
        deltas1 = [(ax,perf,len) | x@(ax,perf,len,vars) <- deltas', vars == maxVarCount]
    in
    if length deltas1 == 1
        then Just $ head [x | (x,_,_) <- deltas1]
        else let deltas2 = [(ax,perf,len,1) | (ax,perf,len)  <- deltas1]
                 maxArrowCount = maximum [arrows | (ax,perf,len,arrows) <- deltas2]
                 deltas3 = [(ax,perf,len) | x@(ax,perf,len,arrows) <- deltas2, arrows == maxArrowCount]
             in if length deltas3 == 1
                  then Just $ head [x | (x,_,_) <- deltas3]
                  else let dx = [ax | (ax,_,_) <- deltas1]
                           ax = [(x,y) | (Axiom x@(Var _) y@(Var _) _) <- lx ++ dx]
                           types = findTypeHierarchy ax
                           deltas4 = deltas3
                       in  if length deltas4 == trace (show $ length deltas4) 1
                            then Just $ head [x | (x,_,_) <- deltas4]
                            else
                              let minCompSize = minimum [x | (_,_,x) <- deltas4]
                                  deltas5 = [(x,y,z) | (x,y,z) <- deltas4, z == minCompSize]
                              in if length deltas5 == 1
                                    then Just $ head [x | (x,_,_) <- deltas5]
                                    else if null deltas5
                                            then Just $ head [x | (x,_,_) <- sortBy (compare `on` (show)) deltas4]
                                            else Just $ head [x | (x,_,_) <- sortBy (compare `on` (show)) deltas5]

findTypeHierarchy :: Eq a => [(a,a)] -> [a]
findTypeHierarchy [] = []
findTypeHierarchy ax = 
    let t = nub' ax
        t' = nub' $ concat [[x,y] | (x,y) <- t ]
        sortFunc x y = (case lookup x t of
                    Nothing -> GT
                    Just y' -> if y == y' then LT else sortFunc y' y)
        result = reverse $ sortBy sortFunc t'
    in  result

generateMixedPlus :: [Concept] -> [Axiom] -> [Axiom]
generateMixedPlus concepts axioms = 
    let maxSize = 8
        vars = [Var [v] | v <- "xyz"]
        special = nub' [Root c | ax <- axioms, isMixed ax, (Root c) <- getSubExpAx ax]
        units = vars ++ special
        unary  = nub' [Root f | C (arit,_,_,_,_,Root f) <- concepts, arit==1]
        binary = nub' [Root f | C (arit,_,_,_,_,Root f) <- concepts, arit==2]
        exps' = [(i,concat [generateExps i (c:vars) unary binary | c <- special])
                                | i <- [1..(maxSize - 4)]]
        exps = nub' $ filter isMixedPlus $
                        [Axiom x y 0 | siz <- [3..maxSize],
                                       i <- [1..(siz-1)],
                                       x <- fromMaybe [] (lookup i exps'),
                                       y <- fromMaybe [] (lookup (siz-i) exps')]
    in exps
-}



{-
main2 :: IO ()
main2 = do
  args' <- getArgs
  hSetBuffering stdin NoBuffering
  if null args' || (take 1 $ head args') /= "-"
  then printMessage
  else do
  let ((_:command):args) = args'
  case command of
    "create" -> if null args then printMessage else createAgent True (head args) 8 10 200 >> return () 
    "show" -> do
        if null args
        then printMessage
        else do
        agent' <- parseAgent (head args)
        if isLeft agent'
        then error $ fromLeft agent'
        else do
            let (Just agent@(Agent comm (width,depth,axiom,(redun,consis,mode,iter)) (axioms,concepts,graph,pats,rew,_))) = snd $ fromRight agent'
            putStrLn $ "Width = " ++ show width
            putStrLn $ "Depth = " ++ show depth
            putStrLn $ "LtmSize = " ++ show axiom
            putStrLn $ "Redundancy = " ++ show redun
            putStrLn $ "Consistency = " ++ show consis
            putStrLn $ "Mode = " ++ show mode
            putStrLn $ "Training iterations = " ++ show iter
            putStrLn $ "Axioms: " ++ show (size axioms)
            putStrLn $ "Graph: " ++ show (Map.size graph)
            putStrLn $ "Concepts: " ++ show (Set.size concepts)
            putStrLn $ "Shapes: " ++ show (Set.size pats)
            putStrLn $ "Rewarding symbols: " ++ show (Set.size rew)
    "manual" -> do
        if length args < 2
        then printMessage
        else do
        let (agentfile:ipfile:argss) = args
        let test = (take 1 argss) == ["-test"]
        let verbose = True
        agent' <- parseAgent agentfile
        if isNothing agent'
        then do
            putStrLn $ "Error reading agent."
            return ()
        else do
        let (Just agent@(Agent _ (width, depth, int, redun) _)) = agent'
        fileExists <- doesFileExist ipfile
        item <- if fileExists
                   then do  iptext <- readFileSafe ipfile utf8
                            let lins  = filter (\(x:_) -> x == '(')
                                        . filter (not . null) . map strip 
                                        . lines $ iptext
                            let items = map fromJust . filter isJust
                                        . map (\x -> readMaybe x :: Maybe Item)
                                        $ lins
                            if null items
                            then error $ "No item found in the IP file." ++ head lins
                            else if length items == 1
                                    then return (head items)
                                    else do putStrLn "More than one items found in the IP file."
                                            putStrLn $ "Considering only the first one: " ++ show (head items)
                                            return (head items)
                   else do  let item' = maybeRead ipfile :: Maybe Item
                            if isJust item'
                            then return $ fromJust item'
                            else error "Item cannot be read / IP-file does not exist. Aborting..."                            
        putStrLn $ "Item: " ++ show item
        putStrLn $ "Width: " ++ show width
        putStrLn $ "Depth: " ++ show depth
        (newAgent,_,_,_) <- runOnce test verbose agent item
        saveAgent test newAgent
    "auto" -> do
        if length args < 3
        then printMessage
        else do
        let (agentfile:domain:count':argss) = args
        let test = (take 1 argss) == ["-test"]
        let count = case (readMaybe count' :: Maybe Int) of
                        Just n -> if n < 1 then 1 else n 
                        _      -> 1
        agent' <- parseAgent agentfile
        if isNothing agent'
        then putStrLn $ "Error reading agent."
        else do
        let (Just agent@(Agent _ _ (axioms,concepts,graph,_,_,_))) = agent'
        let graphsize = length [e | e@(_,(True,set)) <- Map.toList graph]
        case (map toLower domain) of
            "add"   -> do
                initiateScreen axioms (Set.size concepts) graphsize
                items <- addItems
                (newAgent@(Agent _ _ (axm,_,_,_,_,_)),total,score,_,_) <- runAdd test [] [] 0 0 items agent count
                putStrLn $ "\nScore: " ++ show score ++ " out of " ++ show total
                putStrLn $ "Axioms learned: " ++ show (size axm - size axioms)
                putStrLn $ "Total axioms in memory: " ++ show (size axm)
                saveAgent test newAgent
            "addition" -> do
                initiateScreen axioms (Set.size concepts) graphsize
                (newAgent@(Agent _ _ (axm,_,_,_,_,_)),total,score,_,_) <- runLoop Continuous test 3 additionItem [] [] 0 [] agent count
                putStrLn $ "\nScore: " ++ show score ++ " out of " ++ show total
                putStrLn $ "Axioms learned: " ++ show (size axm - size axioms)
                putStrLn $ "Total axioms in memory: " ++ show (size axm)
                saveAgent test newAgent
            "truth" -> do
                initiateScreen axioms (Set.size concepts) graphsize
                (newAgent@(Agent _ _ (axm,_,_,_,_,_)),total,score,_,_) <- runLoop Continuous test 2 truthItem [] [] 0 [] agent count
                putStrLn $ "\nScore: " ++ show score ++ " out of " ++ show total
                putStrLn $ "Axioms learned: " ++ show (size axm - size axioms)
                putStrLn $ "Total axioms in memory: " ++ show (size axm)
                saveAgent test newAgent
            "logic" -> do
                initiateScreen axioms (Set.size concepts) graphsize
                (newAgent@(Agent _ _ (axm,_,_,_,_,_)),total,score,_,_) <- runLoop Continuous test 2 tautItem [] [] 0 [] agent count
                putStrLn $ "\nScore: " ++ show score ++ " out of " ++ show total
                putStrLn $ "Axioms learned: " ++ show (size axm - size axioms)
                putStrLn $ "Total axioms in memory: " ++ show (size axm)
                saveAgent test newAgent
            "arithmetic" -> do
                initiateScreen axioms (Set.size concepts) graphsize
                (newAgent@(Agent _ _ (axm,_,_,_,_,_)),total,score,_,_) <- runLoop Continuous test 3 arithItem [] [] 0 [] agent count
                putStrLn $ "\nScore: " ++ show score ++ " out of " ++ show total
                putStrLn $ "Axioms learned: " ++ show (size axm - size axioms)
                putStrLn $ "Total axioms in memory: " ++ show (size axm)
                saveAgent test newAgent
            "subtraction"  -> putStrLn $ "Subtraction auto-learning not supported yet."
            "division"  -> putStrLn $ "Division auto-learning not supported yet."
            "english"  -> do
                initiateScreen axioms (Set.size concepts) graphsize
                (newAgent@(Agent _ _ (axm,_,_,_,_,_)),total,score,_,_) <- runLoop Continuous test 3 langItem [] [] 0 [] agent count
                putStrLn $ "\nScore: " ++ show score ++ " out of " ++ show total
                putStrLn $ "Axioms learned: " ++ show (size axm - size axioms)
                putStrLn $ "Total axioms in memory: " ++ show (size axm)
                saveAgent test newAgent
            x       -> putStrLn $ "Unknown domain provided: " ++ x
    "test" -> do
        if length args < 2
        then printMessage
        else do
        let (agentfile:domain:_) = args
        agent' <- parseAgent agentfile
        if isNothing agent'
        then putStrLn $ "Error reading agent."
        else do
        let (Just agent@(Agent _ _ (axioms,_,_,_,_,_))) = agent'
        case (map toLower domain) of
            "logic" -> do
                score <- runTest logicTest agent
                putStrLn $ "\nScore: " ++ show score ++ " solved out of " ++ show (length logicTest)
            x       -> putStrLn $ "Tests for domain " ++ x ++ " not available yet."
    _  -> printMessage

printMessage = do
    p <- getProgName
    putStrLn $ "Usage: "
    putStrLn $ "To create a new agent: "
    putStrLn $ "       " ++ p ++ " -create AgentName.hs"
    putStrLn $ "To show summary of an existing agent: "
    putStrLn $ "       " ++ p ++ " -show AgentFile.hs"
    putStrLn $ "To run an existing agent: "
    putStrLn $ "       " ++ p ++ " -manual AgentFile.hs IPfile/Item [-test]"
    putStrLn $ "To train an agent automatically: "
    putStrLn $ "       " ++ p ++ " -auto AgentFile.hs domain count"
    putStrLn $ "To test an agent automatically: "
    putStrLn $ "       " ++ p ++ " -test AgentFile.hs domain"
    putStrLn $ "    where: AgentFile contains the agent description and memory"
    putStrLn $ "           IPfile contains the examples to learn from"
    putStrLn $ "           domain is one of (addition,arithmetic,truth,logic,english)"
    putStrLn $ "           count is number of iterations for training"
    putStrLn $ "           -test for test mode: disables learning new axioms"

runAdd :: Bool -> [(Int,Axiom)] -> [String] -> Int -> Int -> [Item] -> Agent -> Int -> IO (Agent,Int,Int,[String],[(Int,Axiom)])
runAdd test changes prev total score items agent c | c < 1 || null items = return (agent,total,score,prev,changes)
runAdd test changes prev total score items agent c = do
        keypress <- stdin `ifReadyDo` getChar
        if isJust keypress && (fromJust keypress) == 'x'
        then return (agent,total,score,prev,changes)
        else do
        let item@(Item t t' v) = head items
        let string = show (total+1) ++ ": " ++ normalizeOutput (show t ++ "=" ++ show t') ++ " : " ++ show v
        let (ltm,concepts,graph,_,_,_) = agentMemory agent
        updateScreen changes string prev ltm (Set.size concepts) graph []
        (newAgent,result',newChanges,_) <- runOnce test False agent item
        let addScore = if result' then 1 else 0
        let changes' = newChanges ++ changes
        runAdd test changes' (string : prev) (total+1) (score + addScore) (tail items) newAgent (c-1)

runTest :: [Item] -> Agent -> IO Int
runTest items agent = do
        results' <- P.mapM (\item -> do
                              r@(_,b,_,_) <- runOnce True False agent item
                              putStrLn $ show item ++ ": " ++ show b
                              return r)
                         items
        return $ length [1 | (_,True,_,_) <- results']

runLoop :: Runtime -> Bool -> Int -> (Int -> Gen Item) ->
           [(Int,Axiom)] -> [String] -> Int -> [(Int,Int)] -> Agent -> Int
           -> IO (Agent,Int,Int,[String],[(Int,Axiom)])
runLoop _ _ _ _ changes prev total score agent c | c < 1 = do
        showCursor
        return (agent,total,sum (map snd score),prev,changes)
runLoop runtime' test size itemGenerator changes prev total score agent c = do
    keypress <- stdin `ifReadyDo` getChar
    if keypress == Just 'x'
    then do
        showCursor
        return (agent,total,sum (map snd score),prev,changes)
    else do
    (runtime,ch) <- case runtime' of
                    Stepwise  -> 
                        case keypress of
                            Just 'c' -> return (Continuous,' ')
                            Just _   -> return (Stepwise,' ')
                            Nothing  -> do c <- getChar
                                           case c of
                                            'c' -> return (Continuous,' ')
                                            'x' -> return (Continuous,'x')
                                            _   -> return (Stepwise,' ')
                    Continuous->
                        case keypress of 
                            Just 's' -> return (Stepwise,' ')
                            _        -> return (Continuous,' ')
    if ch == 'x'
    then do
        showCursor
        return (agent,total,sum (map snd score),prev,changes)
    else do
        item@(Item t t' v) <- generate (itemGenerator size)
        let string = show (total+1) ++ ": " ++ normalizeOutput (show t ++ "=" ++ show t') ++ " : " ++ show v
        let (ltm,concepts,graph,_,_,_) = agentMemory agent
        updateScreen changes string prev ltm (Set.size concepts) graph score
        -- test run: score before udpating the theory
        time <- getCurrentTime
        (_,_,_,resultBefore,_,_,_) <- findDelta True False time agent item
        -- actual run: score after updating the theory
        (newAgent,resultAfter,f',_) <- runOnce test False agent item
        let afterScore = boolToInt resultAfter
        let beforeScore = boolToInt resultBefore
        let size' = if resultAfter then size + 1 else if size > 2 then size - 1 else size
        let changes' = f' ++ changes -- if null strings then changes else (strings ++ [(0,"")] ++ changes)
        runLoop runtime test size' itemGenerator changes' (string : prev) (total+1) ((beforeScore,afterScore) : score) newAgent (c-1)
initiateScreen :: LTM -> Int -> Int -> IO ()
initiateScreen ltm' concepts graph = do
    setTitle "Alice"
    let ltmSize = size ltm'
    let ltm = Set.toList $ allAxioms ltm'
    let axioms = reverse $ sortBy (compare `on` axV) $ filter isAxiom ltm
    let smSize = length $ filter isSmallFact ltm
    let otSize = ltmSize - (length axioms) - smSize
    let changes  = map printPos
                   $ take 10 . reverse . sortBy (compare `on` axFirst) $ ltm
    clearScreen
    setCursorPosition 0 0
    setSGR [whiteVivid]
    putStr $ "Observations:"
    setCursorPosition 0 40
    putStr $ "Summary of theory:"
    setSGR [whiteDull]
    setCursorPosition 1 40
    putStr $ "Small closed: " ++ show smSize
    setCursorPosition 2 40
    putStr $ "Large closed: " ++ show otSize
    setCursorPosition 3 40
    putStr $ "Open axioms:  " ++ show (length axioms)
    setCursorPosition 4 40
    putStr $ "Total axioms: " ++ show ltmSize
    setCursorPosition 6 40
    putStr $ "Concepts:     " ++ show concepts
    setCursorPosition 7 40
    putStr $ "Patterns:     " ++ show graph
    setSGR [whiteVivid]
    setCursorPosition 9 40
    putStr $ "Score before: "
    setCursorPosition 10 40
    putStr $ "Score after:  "
    setCursorPosition 12 0
    putStr $ "Closed axioms:"
    setCursorPosition 13 0
    setSGR [SetColor Foreground Vivid Green]
    mapM putStrLn changes
    setSGR [whiteVivid]
    setCursorPosition 12 40
    putStr $ "Open axioms:"
    setSGR [SetColor Foreground Dull Green]
    mapM (\(position,ax) -> do
                setCursorPosition position 41
                putStr $ printAxiom ax)
            $ zip [13..] (take 10 axioms)
    setSGR [whiteVivid]
    setCursorPosition 24 0
    putStr $ "Space: pause, Enter: continue, x+Enter: stop, s: stepwise, c: continue"
    setSGR [whiteDull]
    hideCursor
updateScreen :: [(Int,Axiom)] -> String -> [String] -> LTM -> Int -> Graph Exp -> [(Int,Int)] -> IO ()
updateScreen changes' string prev ltm' concepts graph scores = do
    let ltmSize = size ltm'
    let changesA' = filter (containsVarAx . snd) changes'
    let changesF' = filter (not . containsVarAx . snd) changes'
    let axioms = reverse . sortBy (compare `on` axFirst) . Set.toList $ ltmAxioms ltm'
    let facts  = reverse . sortBy (compare `on` axFirst) . Set.toList $ ltmFacts ltm'
    -- let (axioms,facts) = partition containsVarAx . reverse . sortBy (compare `on` axFirst) $ Set.toList ltm'
    let smSize = length $ filter isSmallFact facts
    let otSize = ltmSize - (length axioms) - smSize
    let changesF  = map (\(i,ax) -> (i,if i<0 then printNeg ax else printPos ax))
                    $ take 10 . nub' $ (changesF' ++ map (\x -> (1,x)) facts)
    let changesA''  = let temp = (changesA' ++ (map (\ax -> (1, ax)) axioms))
                          negative = Set.fromList [a | (i,a) <- changesA', i < 0]
                      in take 10
                         $ nub' [printPos ax | (i,ax) <- temp, i > 0, ax `Set.notMember` negative]
    let changesA = changesA'' ++ take (10 - length changesA'') (repeat (take 40 (repeat ' ')))
    setCursorPosition 1 0
    setSGR [whiteDull]
    mapM (\(i,x) -> do
            setCursorPosition i 0
            putStr $ printItem 40 x)
          $ zip [1..] $ take 10 (string : prev)
    setCursorPosition 1 54
    putStr $ show smSize
    setCursorPosition 2 54
    putStr $ show otSize
    setCursorPosition 3 54
    putStr $ show (length axioms)
    setCursorPosition 4 54
    clearFromCursorToLineEnd 
    putStr $ show ltmSize
    setCursorPosition 6 54
    clearFromCursorToLineEnd 
    putStr $ show concepts
    setCursorPosition 7 54
    clearFromCursorToLineEnd
    let graph' = length [e | e@(_,(Valid,set)) <- Map.toList graph] -- , not (Set.null set)]
    putStr $ (show graph') -- ++ "/" ++ show (Map.size graph)
    when ((not . null) scores) $ do
        setSGR [whiteDull]
        setCursorPosition 10 54
        clearFromCursorToLineEnd
        let scoreA = sum . map snd $ take showScore scores
        let scoreB = sum . map fst $ take showScore scores
        let tot = min showScore (length scores)
        putStr $ show scoreA ++ "/" ++ show tot
        setCursorPosition 9 54
        clearFromCursorToLineEnd
        putStr $ show scoreB ++ "/" ++ show tot
    mapM (\(pos,(i,str)) -> do
                setCursorPosition pos 0
                if i > 0
                    then setSGR [SetColor Foreground Vivid Green]
                    else setSGR [SetColor Foreground Vivid Red]
                putStr str )
            $ zip [13..] changesF
    setSGR [SetColor Foreground Vivid Green]
    mapM (\(pos,str) -> do
                setCursorPosition pos 40
                putStr str
                )
            $ zip [13..22] changesA
    setSGR [whiteDull]

-}
