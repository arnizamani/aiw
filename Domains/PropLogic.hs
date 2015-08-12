module Domains.PropLogic (truthItem,tautItem) where

import Instances
import Parsing
import Data.List
import qualified Data.Map as Map
import Test.QuickCheck

top = "⊤"
bot = "⊥"
neg = "¬"

tautItem :: Int -> Gen Item
tautItem s = do
        size <- frequency [(400,return 2),(400,return 3),
                           (80,return 4),(16,return 5),(2,return 6),(2,return 7),
                           (1,return 8),(1,return 9)]
        viabP <- posViability
        viabN <- negViability
        pos <- oneof [return 1, return (-1)]
        (lhsT',_) <- tautExp size
        let lhsT = varToRoot lhsT'
        (lhsF',_) <- contraExp size
        let lhsF = varToRoot lhsF'
        if pos < 0
        then return $ Item lhsF (Root "⊤") viabN
        else return $ Item lhsT (Root "⊤") viabP

-- random Item for addition facts
logicItem :: Int -> Gen Item
logicItem s = do
        size <- frequency [(400,return 2),(400,return 3),
                           (80,return 4),(16,return 5),(2,return 6),(2,return 7),
                           (1,return 8),(1,return 9)]
        viab <- posViability
        (lhs',rhs') <- logicExp size
        let lhs = varToRoot lhs'
        let rhs = if rhs' then makeR top else makeR bot
        if lhs == rhs
            then logicItem s
            else return $ Item lhs rhs viab

varToRoot :: Exp -> Exp
varToRoot e = case e of
                Var v        -> makeR v
                Root r       -> makeR r
                Unary u e    -> Unary u (varToRoot e)
                Binary b e f -> Binary b (varToRoot e) (varToRoot f)

rootToVar :: Exp -> Exp
rootToVar e = case e of
                Var v        -> makeV v
                Root "P"     -> makeV "P"
                Root "Q"     -> makeV "Q"
                Root "R"     -> makeV "R"
                Root r       -> makeR r
                Unary u e    -> Unary u (rootToVar e)
                Binary b e f -> Binary b (rootToVar e) (rootToVar f)


tautExp :: Int -> Gen (Exp,Bool)
tautExp size = do
    exp <- logicExp' size
    if isTautology exp
    then return (exp,True)
    else tautExp size

contraExp :: Int -> Gen (Exp,Bool)
contraExp size = do
    exp <- logicExp' size
    if isContradiction exp
    then return (exp,False)
    else contraExp size

logicExp :: Int -> Gen (Exp,Bool)
logicExp size = do
    exp <- logicExp' size
    if isTautology exp
    then return (exp,True)
    else if isContradiction exp
            then return (exp,False)
            else logicExp size

logicExp' :: Int -> Gen Exp
logicExp' size | size < 2 = frequency [(10,return $ makeV "P"),(10,return $ makeV "Q"),(10,return $ makeV "R"),(1,return $ makeR top),(1,return $ makeR bot)]
logicExp' 2 = do e <- logicExp' 1
                 return $ makeU neg e
logicExp' size = do
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)]]
    x <- logicExp' (size - d1 - 1)
    y <- logicExp' (size - d2 - 1)
    z <- logicExp' (size - 1)
    op <- operatorTruth
    oneof $ map return [makeB op x y,makeB op y x,makeU neg z]


makeBindings :: [String] -> [[(String,Exp)]]
makeBindings [] = []
makeBindings (s:[]) = [[(s,Root "⊤")],[(s,Root "⊥")]]
makeBindings (s:ss) =
    let s' = makeBindings ss
    in [(s,Root "⊤") : x | x <- s'] ++ [(s,Root "⊥") : x | x <- s']

e = read "(⊥ ∨ P)" :: Exp

isTautology :: Exp -> Bool
isTautology e | null (getVars e) = isTrue e
isTautology e =
    let vars = nub' $ getVars e
        bindings = makeBindings vars
        exps = map (\bind -> replaceAllSubExp e $ Map.fromList bind) bindings
    in all isTrue exps

isContradiction :: Exp -> Bool
isContradiction e | null (getVars e) = not $ isTrue e
isContradiction e =
    let vars = nub' $ getVars e
        bindings = makeBindings vars
        exps = map (\bind -> replaceAllSubExp e $ Map.fromList bind) bindings
    in all (not . isTrue) exps


-- posViability = frequency [(1000,return 1),(100,return 2),(10,return 3),(1,return 4)]
posViability = frequency [((1001 - n * n * n),return n) | n <- [1..10]]
negViability = frequency [(1000,return (-1)),(100,return (-2)),(10,return (-3)),(1,return (-4))]
randomSize = frequency [(900,return 3),(90,return 5),(9,return 7),(1,return 9)] -- (3,90%), (5,31.8%), (7,21.6%), (9,8.0%) total = 91+75+51+19=236

-- random Item for addition facts
truthItem :: Int -> Gen Item
truthItem s = do
        size <- frequency [(400,return 2),(400,return 3),
                           (80,return 4),(16,return 5),(2,return 6),(2,return 7),
                           (1,return 8),(1,return 9)]

        viabP <- posViability
        viabN <- negViability
        pos   <- frequency [(9,return 1),(1,return (-1))]
        lhs <- truthExp size
        let rhsP = if isTrue lhs then Root "⊤" else Root "⊥"
        let rhsN = if isTrue lhs then Root "⊥" else Root "⊤" -- makeR . take 1 . show . not $ isTrue lhs
        if pos < 1
        then do
            return $ Item lhs rhsN viabN
        else do
            if lhs == rhsP
                then truthItem s
                else return $ Item lhs rhsP viabP

truthExp :: Int -> Gen Exp
truthExp size | size < 2 = oneof [(return $ makeR "⊤"),(return $ makeR "⊥")]
truthExp 2 = do e <- truthExp 1
                return $ makeU neg e
truthExp size = do
    (d1,d2) <- oneof $ map return $ [(i,size-1-i) | i <- [1..(size-2)]]
    x <- truthExp (size - d1 - 1)
    y <- truthExp (size - d2 - 1)
    z <- truthExp (size - 1)
    op <- operatorTruth
    oneof $ map return [makeB op x y,makeB op y x,makeU neg z]

isTrue :: Exp -> Bool
isTrue (Root e) | e == top = True
isTrue (Root e) | e == bot = False
isTrue (Unary (Oper op) e) | op == neg = not $ isTrue e
isTrue e = case e of
    (Binary (Oper "∨") e1 e2) -> isTrue e1 || isTrue e2
    (Binary (Oper "∧") e1 e2) -> isTrue e1 && isTrue e2
    (Binary (Oper "→") e1 e2) -> if (isTrue e1) then isTrue e2 else True
    (Binary (Oper "↔") e1 e2) -> isTrue e1 == isTrue e2
    (Var _) -> error "isTrue: Variable in constant expression."
    x       -> error $ "isTrue: Unknown expression " ++ show x

operatorTruth = oneof [(return "∨"),(return "∧"),(return "→"),(return "↔")]
