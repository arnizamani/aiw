-- Module Instances:  basic functions and instances
-- Author: Abdul Rahim Nizamani, ITIT, Gothenburg University, Sweden

module Instances where
import Prelude hiding (catch)
import Control.Exception (catch, IOException)
import System.IO
import Data.Time
import Data.List
import Data.Function (on)
import Data.Maybe (isNothing,isJust,fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import System.Directory
import Debug.Trace
import Data.Ratio
import Data.Time.Calendar

combiner = "#" -- combiner is a special binary operator, with size = 0 and always considered a rewarded symbol

deepRule = ["▶","⊣⊢","=="]
shallowRule = ["▷","⊢","=>"]
negativeRule = ["⊬","▷̸","/>"]

itemPositive = "⊢"
itemNegative = "⊬"

class Size a where
    size :: a -> Int
data Mode = Einstein | Popper deriving Eq

data Truth = Invalid | Satisfiable | Valid
                deriving (Eq,Ord,Show)

data Oper = Oper String | OVar String deriving (Eq,Ord)
 
data Exp = Root String | Var String | Unary Oper Exp | Binary Oper Exp Exp
            deriving (Eq,Ord)

data Item  = Item {lhs :: Lhs, rhs :: Rhs, val :: Int}
data Items = Items {getItems :: [Item]}

type Width = Int
type Depth = Int
type Comments = String

type ID    = Int
type Arity = Int
type Frequency = Int
type Viability = Double
type Rewarded = Int -- 0 for false, 1 for true. Indicates if a symbol appears in rhs
type FirstTime = UTCTime
type LastTime  = UTCTime
type IsFact = Bool

type Substitution = Map String String -- Map variable constant


data Dir = Bi | Uni | Neg deriving (Eq,Ord)

isBi, isUni, isNeg :: Axiom -> Bool
isBi (Axiom (_,_,_,_,_,(_,Bi,_))) = True
isBi _ = False
isUni (Axiom (_,_,_,_,_,(_,Uni,_))) = True
isUni _ = False
isNeg (Axiom (_,_,_,_,_,(_,Neg,_))) = True
isNeg _ = False


instance Show Dir where
    show Bi = head deepRule
    show Uni = head shallowRule
    show Neg = head negativeRule

type Axiom' = (Lhs,Dir,Rhs)

newtype Axiom = Axiom (Viability,Frequency,IsFact,FirstTime,LastTime,Axiom')

axiom' (Axiom (_,_,_,_,_,ax)) = ax

newtype Concept  = C (Arity,Rewarded,Frequency,FirstTime,LastTime,Exp)

isUnitConcept (C (0,_,_,_,_,Root _)) = True
isUnitConcept _ = False

type Vars = Set String
newtype Edge  = Edge (Exp,Exp,Truth,Set [String])

type Weight = (Truth,Set [String])
type Graph a = Map (a,a) Weight

newtype Rewarding = Rew (Arity,String)   -- rewarding symbols, that appear in Rhs
                        deriving (Eq,Ord)
type WM =  Exp
type Lhs = Exp
type Rhs = Exp
type Pattern = Exp

type IPFile = FilePath
type RecentlyRemoved = [Axiom]

type Redundancy = Bool
type Consistency = Bool
type Iterations = Int
type Fact = Axiom

data LTM = Ltm !(Set Fact) !(Set Axiom)

newLtm = Ltm Set.empty Set.empty

ltmAxioms (Ltm _ ax) = ax
ltmFacts (Ltm f _) = f
allAxioms (Ltm fc ax) = Set.union fc ax

biToUni :: LTM -> Exp -> Exp -> LTM
biToUni (Ltm f ax) t t' =
    let fx = [(x, Axiom (a,b,c,d,e,(s,Uni,s'))) | x@(Axiom (a,b,c,d,e,(s,Bi,s'))) <- Set.toList f, 
                                                  s == t', s' == t]
        f' = Set.union (Set.fromList $ map snd fx) $ Set.difference f (Set.fromList $ map fst fx)
        axx = [(x, Axiom (a,b,c,d,e,(s,Uni,s'))) | x@(Axiom (a,b,c,d,e,(s,Bi,s'))) <- Set.toList ax,
                                                   (Axiom (a,b,c,d,e,(t',Bi,t))) `isInstanceOf` x]
        ax' = Set.union (Set.fromList $ map snd axx) $ Set.difference ax (Set.fromList $ map fst axx)
    in Ltm f' ax'

makeLTM :: (Set Axiom) -> LTM
makeLTM axs = 
    let (ax,fc) = Set.partition containsVarAx axs
    in  Ltm fc ax
instance Eq LTM where
    (==) (Ltm a b) (Ltm x y) = (a,b) == (x,y)
instance Size LTM where
    size (Ltm a b) = Set.size a + Set.size b

ltmDifference :: LTM -> (Set Axiom) -> LTM
ltmDifference (Ltm facts axioms) axs =
    let (axAxioms,axFacts) = Set.partition containsVarAx axs
        facts' = Set.difference facts axFacts
        axioms' = Set.difference axioms axAxioms
        axFacts' = Set.fromList . map (\x -> (axLhs x,axRhs x)) $ Set.toList axFacts
    in Ltm facts' axioms'
ltmDelete :: Axiom -> LTM -> LTM
ltmDelete ax (Ltm fc axs) = 
    if containsVarAx ax
    then Ltm fc (Set.delete ax axs)
    else Ltm (Set.delete ax fc) axs
ltmMember :: Axiom -> LTM -> Bool
ltmMember ax (Ltm fc axs) = if containsVarAx ax
                              then Set.member ax axs
                              else Set.member ax fc

ltmNotmember :: Axiom -> LTM -> Bool
ltmNotmember ax (Ltm fc axs) = if containsVarAx ax
                                then Set.notMember ax axs
                                else Set.notMember ax fc

insertInLTM :: LTM -> Axiom -> LTM
insertInLTM (Ltm fc ax) c@(Axiom (viab,freq,isfact,first,last,(lhs,dir,rhs))) | containsVarAx c =
    let index' = Set.lookupIndex c ax
    in if isNothing index'
        then Ltm fc (Set.insert c ax)
        else let index = fromJust index'
                 Axiom (_,_,_,first',_,_) = Set.elemAt index ax
             in Ltm fc (Set.insert (Axiom (viab,freq,isfact,first',last,(lhs,dir,rhs))) ax)  -- replace old axiom with new
insertInLTM (Ltm fc ax) c@(Axiom (viab,freq,isfact,first,last,(lhs,dir,rhs))) = -- c is fact
    let index' = Set.lookupIndex c fc
    in if isNothing index'
        then let fc' = Set.insert c fc
             in Ltm fc' ax
        else let index = fromJust index'
                 Axiom (_,_,_,first',_,_) = Set.elemAt index fc
                 fc' = Set.insert (Axiom (viab,freq,isfact,first',last,(lhs,dir,rhs))) fc
             in Ltm fc' ax -- replace old axiom with new
ltmUpdateViability time decay (Ltm fc ax)
    = Ltm (Set.mapMonotonic (updateViability time decay) fc) (Set.mapMonotonic (updateViability time decay) ax)

type AgentParams = (Width, Depth, Int, (Redundancy, Consistency, Mode, Iterations))
type AgentMemory = (LTM,Set Concept,Graph Pattern,Set Pattern,Set Rewarding,RecentlyRemoved)
data Agent = Agent (FilePath,Comments) AgentParams AgentMemory deriving Eq

makeFalse :: Graph Pattern -> [(Bool,[Axiom])] -> Graph Pattern
makeFalse graph ax = undefined

type Length = Int
type StateD = (Exp,Maybe Axiom,Set Exp)

axV       (Axiom (v,_,_,_,_,_)) = v
axFreq    (Axiom (_,x,_,_,_,_)) = x
axIsFact  (Axiom (_,_,x,_,_,_)) = x
axFirst   (Axiom (_,_,_,x,_,_)) = x
axRecency (Axiom (_,_,_,_,x,_)) = x
axLast    (Axiom (_,_,_,_,x,_)) = x
axLhs     (Axiom (_,_,_,_,_,(l,_,_))) = l
axRhs     (Axiom (_,_,_,_,_,(_,_,r))) = r
axPair    (Axiom (_,_,_,_,_,(l,_,r))) = (l,r)

axIsBi (Axiom (_,_,_,_,_,(_,Bi,_))) = True
axIsBi _ = False

axIsUni (Axiom (_,_,_,_,_,(_,Uni,_))) = True
axIsUni _ = False

arity (C (a,_,_,_,_,_)) = a
cexp  (C (_,_,_,_,_,a)) = a

isRoot (Root _) = True
isRoot _ = False
fromRoot (Root x) = x

agentMemory (Agent _ _ x) = x
getIterations (Agent _ (_,_,_,(_,_,_,x)) _) = x
setIterations (Agent a (b,c,d,(e,f,g,h)) i) iter = (Agent a (b,c,d,(e,f,g,iter)) i)

-------------------------------------------------------------------------------
---------------- CONSTRUCTORS -------- ----------------------------------------
-------------------------------------------------------------------------------
makeR :: String -> Exp
makeR = Root

makeV :: String -> Exp
makeV = Var

makeU :: String -> Exp -> Exp
makeU s e = Unary (Oper s) e

makeB :: String -> Exp -> Exp -> Exp
makeB s e f = Binary (Oper s) e f

makeGraph :: [((Exp,Exp),(Truth,Set [String]))] -> Graph Exp
makeGraph patterns = foldl' (\m (key,(b,set)) -> 
                                    let value = Map.lookup key m
                                    in if isNothing value
                                        then Map.insert key (b,set) m
                                        else let (b',set') = fromJust value
                                             in if b == Valid
                                                 then Map.insert key (Valid,set) m
                                                 else if b' == Valid
                                                      then Map.insert key (Valid,set') m
                                                      else if b==Invalid
                                                           then Map.insert key (b,set) m
                                                           else if b'==Invalid
                                                                then Map.insert key (b',set') m
                                                                else Map.insert key (Satisfiable,Set.union set set') m
                              ) Map.empty patterns
    -- Map.fromList . map (\(Edge (e1,e2,b,set)) -> ((e1,e2),(b,set)))

getEdges :: Graph Exp -> [Edge]
getEdges = map (\((e1,e2),(b,set)) -> Edge (e1,e2,b,set)) . Map.toList

-------------------------------------------------------------------------------
---------------- INSTANCE DECLARATIONS ----------------------------------------
-------------------------------------------------------------------------------

instance Eq Concept where
    (==) = (==) `on` (\c -> (arity c,cexp c))

instance Ord Concept where
    compare = compare `on` (\c -> (arity c,cexp c))

instance Show Oper where
    show (Oper s) = s
    show (OVar "x") = "x"
    show (OVar "y") = "y"
    show (OVar "z") = "z"
    show (OVar s) = "\\" ++ s

instance Eq Axiom where
    (Axiom (_,_,_,_,_,(l1,d1,r1))) == (Axiom (_,_,_,_,_,(l2,d2,r2))) = (d1,l1,r1) == (d2,l2,r2)

instance Ord Axiom where
    compare (Axiom (_,_,_,_,_,(l1,d1,r1))) (Axiom (_,_,_,_,_,(l2,d2,r2))) = compare (d1,l1,r1) (d2,l2,r2)

instance Size Item where
    size (Item x y _) = size x + size y

tsize :: Exp -> Int                 -- number of nodes in tree
tsize (Unary _ x) = 1 + tsize x
tsize (Binary _ x y) = 1 + tsize x + tsize y
tsize _ = 1

instance Size Exp where
    size (Unary a x) = 1 + size x
    size (Binary (Oper o) x y) | o == combiner = size x + size y
    size (Binary a x y) = 1 + size x + size y
    size _ = 1

instance Size Axiom where
    size (Axiom (_,_,_,_,_,(x,_,y))) = size x + size  y

instance Size [a] where
    size xs = length xs

instance Size (Set a) where
    size x = Set.size x

instance Size (Map a b) where
    size x = Map.size x

instance Show Exp where
    show (Root "x") = "(\\x)"
    show (Root "y") = "(\\y)"
    show (Root "z") = "(\\z)"
    show (Root a) = "(" ++ a ++ ")"
    show (Var "x") = "(x)"
    show (Var "y") = "(y)"
    show (Var "z") = "(z)"
    show (Var v) = "(\\v " ++ v ++ ")"
    show (Unary a e) = "(" ++ show a ++ " " ++ showexp e ++ ")"
    show (Binary a e1 e2) = "(" ++ showexp e1 ++ " "  ++ show a ++ " " ++ showexp e2 ++ ")"

showexp :: Exp -> String
showexp (Root "x") = "\\x"
showexp (Root "y") = "\\y"
showexp (Root "z") = "\\z"
showexp (Root a) = a
showexp (Var "x") = "x"
showexp (Var "y") = "y"
showexp (Var "z") = "z"
showexp e = show e

instance Show Item where
    show (Item lhs rhs val) | val >= 0 = show lhs ++ "⊢" ++ show rhs
    show (Item lhs rhs val) = show lhs ++ "⊬" ++ show rhs

instance Show Axiom where
    show (Axiom (v,freq,isfact,start,last,(lhs,dir,rhs))) = 
        "(A," ++ show v
            ++ "," ++ show freq
            ++ "," ++ show isfact
            ++ "," ++ show start
            ++ "," ++ show last
            ++ "," ++ show lhs ++ show dir ++ show rhs
            ++ ")"

instance Show Concept where
    show (C (arity,rew,freq,start,last,exp)) = 
        "(C," ++ show arity
            ++ "," ++ show rew
            ++ "," ++ show freq
            ++ "," ++ show start
            ++ "," ++ show last
            ++ "," ++ show exp
            ++ ")"

instance Show Edge where
    show (Edge (e1,e2,b,set)) = 
        "(E," ++ show e1
              ++ "," ++ show e2
              ++ "," ++ show b
              ++ ",[" ++ concat (intersperse "," (map (\x -> "[" ++ concat (intersperse "," x) ++ "]") (Set.toList set)))
              ++ "])"

isLeft (Left _) = True
isLeft _ = False
getLeft (Left r) = r

isRight (Right _) = True
isRight _ = False
getRight (Right r) = r

updateViability :: UTCTime -> Double -> Axiom -> Axiom
updateViability now d ax@(Axiom (_,n',isfact,first,last,(lhs,dir,rhs))) | first == last
    =   let t_n' = abs (utcToDouble now - utcToDouble first)
            t_n = if t_n' < 1 then 1 else t_n'
            n = fromIntegral n'
            viability = log (n / (1 - d)) - (d * log t_n)
        in if isNaN viability || isInfinite viability
           then error $ "\nbaseLevel: error computing base viability for first==last, tn'=" ++ show t_n' ++ ", "
           else Axiom (viability,n',isfact,first,last,(lhs,dir,rhs))
updateViability now d ax@(Axiom (vprev,n',isfact,first,last,(lhs,dir,rhs)))
    =   let n = fromIntegral n'
            t_n' = abs (utcToDouble now - utcToDouble first)
            t_1' = abs (utcToDouble now - utcToDouble last)
            t_n = if t_n' == 0 then 0.00001 else t_n'
            t_1 = if t_n == t_1' then 0 else t_1'
            term1 = if t_1 == 0.0 then 0.0 else t_1 ** (0 - d)
            tnd = if t_n == 0.0 then 0.0 else t_n ** (1 - d)
            t1d = if t_1 == 0.0 then 0.0 else t_1 ** (1 - d)
            a = (n - 1) * (tnd - t1d)
            b = (1.0 - d) * (t_n - t_1)
            viability = log (term1 + (if b == 0.0 then 0 else a / b))
        in if isNaN viability || isInfinite viability 
            then Axiom (viability,n',isfact,first,last,(lhs,dir,rhs)) -- error $ "\nbaseLevel: error computing base viability, tn=" ++ show t_n' ++ ", t1=" ++ show t_1'
            else Axiom (vprev,n',isfact,first,last,(lhs,dir,rhs))
utcToDouble :: UTCTime -> Double
utcToDouble time =
    let days = fromIntegral . toModifiedJulianDay . utctDay $ time
        -- secs = read (init . show $ utctDayTime time) :: Double
        secs = diffTimeToSeconds $ utctDayTime time
    in  days * 86400 + secs

diffTimeToSeconds :: DiffTime -> Double
diffTimeToSeconds d =
    let r = toRational d
    in fromIntegral (numerator r) / (fromIntegral (denominator r))
    
{-
data E12 = E12
     deriving (Typeable)
instance HasResolution E12 where
    resolution _ = 1000000000000
newtype Fixed a = MkFixed Integer -- ^ /Since: 4.7.0.0/
        deriving (Eq,Ord,Typeable)
newtype DiffTime = MkDiffTime (Fixed E12)
diff = MkDiffTime (MkFixed Integer :: Fixed E12)
-}

findVarBinding :: Axiom -> Axiom -> Maybe [(String,Exp)]
findVarBinding (Axiom (_,_,_,_,_,(f,_,f'))) ax@(Axiom (_,_,_,_,_,(x,_,x'))) =
    let bind1 = expVarBinding x f   -- Maybe [(String,Exp)]
        bind2 = expVarBinding x' f' -- Maybe [(String,Exp)]
    in if isJust bind1 && isJust bind2
        then let bind = fromJust bind1 ++ fromJust bind2 -- -- [(String,Exp)]
             in if (length bind == countVars ax) && (null $ sameVarBinding bind)
                  then Just $ nubBy' fst bind
                  else Nothing
        else Nothing

axiomVarBinding :: Axiom -> Axiom -> Maybe [(String,String)]
axiomVarBinding (Axiom (_,_,_,_,_,(f,_,f'))) ax@(Axiom (_,_,_,_,_,(x,_,x'))) =
    let bind1 = expVarBinding x f   -- Maybe [(String,Exp)]
        bind2 = expVarBinding x' f' -- Maybe [(String,Exp)]
    in if isJust bind1 && isJust bind2
        then let bind = fromJust bind1 ++ fromJust bind2 -- -- [(String,Exp)]
             in if length bind == countVars ax
                    && (null $ sameVarBinding bind)
                    && all isRoot (map snd bind)
                  then Just $ nubBy' fst $ [(a,b) | (a,Root b) <- bind]
                  else Nothing
        else Nothing

isInstanceOf :: Axiom -> Axiom -> Bool
isInstanceOf (Axiom (_,_,_,_,_,(f,_,f'))) ax@(Axiom (_,_,_,_,_,(x,_,x'))) =
    let bind1 = expVarBinding x f   -- Maybe [(String,Exp)]
        bind2 = expVarBinding x' f' -- Maybe [(String,Exp)]
    in if isJust bind1 && isJust bind2
        then let bind = fromJust bind1 ++ fromJust bind2 -- -- [(String,Exp)]
             in length bind == countVars ax 
                && (null $ sameVarBinding bind)
                && all isRoot (map snd bind)
        else False

isInstance :: Axiom -> Axiom -> Bool
isInstance (Axiom (_,_,_,_,_,(f,_,f'))) ax@(Axiom (_,_,_,_,_,(x,_,x'))) =
    let bind1 = expVarBinding x f   -- Maybe [(String,Exp)]
        bind2 = expVarBinding x' f' -- Maybe [(String,Exp)]
    in if isJust bind1 && isJust bind2
        then let bind = fromJust bind1 ++ fromJust bind2 -- -- [(String,Exp)]
             in length bind == countVars ax 
                && (null $ sameVarBinding bind)
        else False

instance' :: Exp -> Exp -> [(String,Exp)]
instance' = undefined

isPure (Axiom (_,_,_,_,_,(t,_,t'))) =
    let lhsvar = nub' $ getVars t
        rhsvar = nub' $ getVars t'
    in null (rhsvar \\ lhsvar)

-- stability of constants and variables: Every constant is unique
isStable ax@(Axiom (_,_,_,_,_,(t,_,t'))) = size t > 1 && t /= t' && isPure ax

isBasicFact :: Set Rewarding -> Axiom -> Bool
isBasicFact rew (Axiom (_,_,_,_,_,ax)) = func rew $ fst' ax
    where
        
        func rew (Unary (Oper op) (Root _)) | Set.member (Rew (1,op)) rew = True
        func rew (Unary (Oper _) (Root _)) = False
        func rew (Binary (Oper op) (Root _) (Root _)) | Set.member (Rew (2,op)) rew = True
        func rew (Binary (Oper _) (Root _) (Root _)) = True
        func _ _ = False

isSmallFact :: Axiom -> Bool
isSmallFact ax@(Axiom (_,_,_,_,_,(t,_,t'))) = isFact ax && size t <= 3

isFact :: Axiom -> Bool
isFact ax@(Axiom (_,_,_,_,_,(t,_,t')))
        =      (not . containsVarAx) ax
            && t /= t'

isAxiom :: Axiom -> Bool
isAxiom = containsVarAx

isMixedPlus :: Axiom -> Bool
isMixedPlus ax@(Axiom (_,_,_,_,_,(t,_,t')))
            =      (not . null $ lhsvar)
                && (isOne . nub' . getConstsAx $ ax)
                && ((sort . nub' $ lhsvar)
                     == (sort . nub' $ rhsvar))
                && size t > 1 
                && t /= t' 
    where
        lhsvar = getVars t
        rhsvar = getVars t'

isMixed :: Axiom -> Bool
isMixed ax@(Axiom (_,_,_,_,_,(t,_,t')))
            =      isOne vars
                && isOne consts
                && notnull lhsvar
                && t /= t'
                && checkRhs t'
        where
            lhsvar = nub' $ getVars t
            rhsvar = nub' $ getVars t'
            vars   = nub' (lhsvar ++ rhsvar)
            consts = nub' . getConstsAx $ ax
            checkRhs (Var _)  = True
            checkRhs (Root _) = True
            checkRhs _        = False

isOne :: [a] -> Bool
isOne [x] = True
isOne _ = False

atMostOne :: [a] -> Bool
atMostOne [] = True
atMostOne [x] = True
atMostOne _ = False

getConstsAx :: Axiom -> [String]
getConstsAx (Axiom (_,_,_,_,_,(x,_,y))) = getConsts x ++ getConsts y

getConsts :: Exp -> [String]
getConsts e = case e of
                Root r       -> [r]
                Unary _ e    -> getConsts e
                Binary _ e f -> getConsts e ++ getConsts f
                _            -> []

getConstsSet :: Axiom -> Set String
getConstsSet (Axiom (_,_,_,_,_,(x,_,y))) = Set.union (getConstsSet' x) (getConstsSet' y)

getConstsSet' :: Exp -> Set String
getConstsSet' e = case e of
                    Root r       -> Set.singleton r
                    Unary _ e    -> getConstsSet' e
                    Binary _ e f -> Set.union (getConstsSet' e) (getConstsSet' f)
                    _            -> Set.empty


getVarsAx :: Axiom -> [String]
getVarsAx (Axiom (_,_,_,_,_,(x,_,y))) = getVars x ++ getVars y

getVars :: Exp -> [String]
getVars e = case e of
                Var v        -> [v]
                Unary (OVar v) e -> v : getVars e
                Unary _ e    -> getVars e
                Binary (OVar v) e f -> v : (getVars e ++ getVars f)
                Binary _ e f -> getVars e ++ getVars f
                _            -> []

getVarsSet :: Axiom -> Set String
getVarsSet (Axiom (_,_,_,_,_,(x,_,y))) = Set.union (getVarsSet' x) (getVarsSet' y)

getVarsSet' :: Exp -> Set String
getVarsSet' e = case e of
                Root _       -> Set.empty
                Var v        -> Set.singleton v
                Unary (OVar v) e' -> Set.insert v (getVarsSet' e')
                Unary _ e    -> getVarsSet' e
                Binary (OVar v) e' f -> Set.insert v (Set.union (getVarsSet' e') (getVarsSet' f))
                Binary _ e' f -> Set.union (getVarsSet' e') (getVarsSet' f)

getUnary :: Exp -> [String]
getUnary e = case e of
                Root _       -> []
                Var _        -> []
                Unary (Oper u) e    -> u : getUnary e
                Unary _ e -> getUnary e
                Binary _ e f -> getUnary e ++ getUnary f

getBinary :: Exp -> [String]
getBinary e = case e of
                Root _       -> []
                Var v        -> []
                Unary _ e    -> getBinary e
                Binary (Oper b) e f -> b : (getBinary e ++ getBinary f)
                Binary _ e f -> (getBinary e ++ getBinary f)
getUnaryBinary :: Exp -> [(Arity,String)]
getUnaryBinary e = case e of
                    Root _       -> []
                    Var _        -> []
                    Unary (Oper u) e    -> (1,u) : getUnaryBinary e
                    Unary _ e -> getUnaryBinary e
                    Binary (Oper b) e f -> (2,b) : (getUnaryBinary e ++ getUnaryBinary f)
                    Binary _ e f -> (getUnaryBinary e ++ getUnaryBinary f)

getSymbolsAx :: Axiom -> [(Arity,String)]
getSymbolsAx (Axiom (_,_,_,_,_,(x,_,y))) = getSymbols x ++ getSymbols y
getSymbols :: Exp -> [(Arity,String)]
getSymbols e = case e of
                    Root r       -> [(0,r)]
                    Var v        -> []  -- [(0,v)]
                    Unary (Oper u) e    -> (1,u) : getSymbols e
                    Unary _ e -> getSymbols e
                    Binary (Oper b) e f -> (2,b) : (getSymbols e ++ getSymbols f)
                    Binary _ e f -> (getSymbols e ++ getSymbols f)

isUnary ax = isUnary' . fst' . axiom' $ ax

isUnary' (Unary _ _) = True
isUnary' _ = False

isUnary'' (Unary (Oper _) _) = True
isUnary'' _ = False

isAlgebraic :: Axiom -> Bool
isAlgebraic ax@(Axiom (_,_,_,_,_,(t,_,t')))
            =      not (containsConstAx ax)
                && (sort lhsvar == sort rhsvar)
                && (sort lhsunr == sort rhsunr)
                && (sort lhsbin == sort rhsbin)
                && size t > 1 
                && size ax <= 7
                && t /= t'
    where
        lhsvar = nub' $ getVars t
        rhsvar = nub' $ getVars t'
        lhsunr = nub' $ getUnary t
        rhsunr = nub' $ getUnary t'
        lhsbin = nub' $ getBinary t
        rhsbin = nub' $ getBinary t'

isAlgebraicAbs :: Axiom -> Bool
isAlgebraicAbs ax@(Axiom (_,_,_,_,_,(t,_,t'))) 
                =      not (containsConstAx ax)
                    && (sort lhsvar == sort rhsvar)
                    && size t > 1 
                    && t /= t'
    where
        lhsvar = nub' $ getVars t
        rhsvar = nub' $ getVars t'

isConservative :: Axiom -> Bool
isConservative ax@(Axiom (_,_,_,_,_,(t,_,t'))) 
          = isAxiom ax && isStable ax
            && and [v `elem` lhs' | v@(Var _) <- rhs']
            && and [e `elem` lhs' | e@(Root _) <- rhs']
            && and [u `elem` [u' | (Unary u' _) <- lhs'] | (Unary u _) <- rhs']
            && and [b `elem` [b' | (Binary b' _ _) <- lhs'] | (Binary b _ _) <- rhs']
    where
        lhs' = getSubExp t
        rhs' = getSubExp t'

varConstBinding :: Exp -> Exp -> Maybe Substitution -- Map String (Root c)
varConstBinding (Root x) (Root y) | x == y = Just Map.empty
varConstBinding (Var v)  (Root s)          = Just $ Map.singleton v s
varConstBinding (Unary (OVar p) p') (Unary (Oper e) e') = 
        let result = varConstBinding p' e'
        in if isNothing result
            then Just $ (Map.singleton p e)
            else Just $ Map.insert p e (fromJust result)
varConstBinding (Unary p p') (Unary e e') | p == e = varConstBinding p' e'
varConstBinding (Binary (OVar op1) p1 p2) (Binary (Oper op2) e1 e2) =
        let result1 = varConstBinding p1 e1
            result2 = varConstBinding p2 e2
        in if (isNothing result1 || isNothing result2)
            then Just $ (Map.singleton op1 op2)
            else let result = mergeSubstitutions (fromJust result1) (fromJust result2)
                 in if isNothing result
                    then Just $ (Map.singleton op1 op2) 
                    else mergeSubstitutions (Map.singleton op1 op2) (fromJust result) 
varConstBinding (Binary op1 p1 p2) (Binary op2 e1 e2)
        | op1 == op2 && isJust result1 && isJust result2
            = mergeSubstitutions (fromJust result1) (fromJust result2)
                where
                    result1 = varConstBinding p1 e1
                    result2 = varConstBinding p2 e2
varConstBinding _ _ = Nothing

mergeSubstitutions :: Substitution -> Substitution -> Maybe Substitution
mergeSubstitutions m1 m2 = merge' m1 (Map.toList m2)
  where
    merge' mp1 []          = Just mp1
    merge' mp1 ((x,y):mp2) = let result = Map.lookup x mp1
                             in if isNothing result
                                then merge' (Map.insert x y mp1) mp2
                                else if (fromJust result == y)
                                     then merge' mp1 mp2
                                     else Nothing

-- Matches left Exp with right Exp
matchExpExp :: Exp -> Exp -> Bool
matchExpExp (Var v)  _        = True
matchExpExp (Root x) (Root y) = x == y
matchExpExp (Unary (OVar p) p') (Unary e e') = matchExpExp p' e'
matchExpExp (Unary p p') (Unary e e') | p == e = matchExpExp p' e'
matchExpExp (Binary (OVar op1) p1 p2) (Binary op2 e1 e2) = matchExpExp p1 e1 && matchExpExp p2 e2
matchExpExp (Binary op1 p1 p2) (Binary op2 e1 e2)
        | op1 == op2 = matchExpExp p1 e1 && matchExpExp p2 e2
matchExpExp _ _ = False

expVarBinding :: Exp -> Exp -> Maybe [(String,Exp)]
expVarBinding (Var v) arg = Just [(v,arg)]
expVarBinding (Root x) (Root y) | x == y = Just []

expVarBinding (Unary (OVar p) p') (Unary (Oper e) e') = 
        let result = expVarBinding p' e'
        in if isNothing result
            then Nothing
            else Just $ (p,(Root e)) : (fromJust result)
expVarBinding (Unary p p') (Unary e e') | p == e = expVarBinding p' e'
-- expVarBinding (palm x hand) (Islamabad capital Pakistan)
expVarBinding (Binary (OVar op1) p1 p2) (Binary (Oper op2) e1 e2) =
        let result1 = expVarBinding p1 e1
            result2 = expVarBinding p2 e2
        in if (isNothing result1 || isNothing result2)
            then Nothing -- Just $ [(op1,Root op2)]
            else Just $ (op1,Root op2) : ((fromJust result1) ++ (fromJust result2)) 
expVarBinding (Binary op1 p1 p2) (Binary op2 e1 e2) | op1 == op2 && isJust result1 && isJust result2
            = Just (fromJust result1 ++ fromJust result2)
            where
                result1 = expVarBinding p1 e1
                result2 = expVarBinding p2 e2

expVarBinding _ _ = Nothing

matchingAxiom func (Axiom (_,_,_,_,_,ax)) = matchExpExp (fst' ax) func

containsVarItem :: Item -> Bool
containsVarItem (Item lhs rhs _) = containsVar lhs || containsVar rhs

containsVar :: Exp -> Bool
containsVar e = case e of
    Var _        -> True
    Root _       -> False
    Unary (OVar _) _ -> True
    Unary _ e    -> containsVar e
    Binary (OVar _) _ _ -> True
    Binary _ e f -> containsVar e || containsVar f

containsVarAx :: Axiom -> Bool
containsVarAx (Axiom (_,_,_,_,_,(x,_,y))) = containsVar x || containsVar y

containsConst :: Exp -> Bool
containsConst e = case e of
                    Var _        -> False
                    Root _       -> True
                    Unary _ e    -> containsConst e
                    Binary _ e f -> containsConst e || containsConst f

containsConstAx :: Axiom -> Bool
containsConstAx (Axiom (_,_,_,_,_,(x,_,y))) = containsConst x || containsConst y

countVarsUnique :: Axiom -> Int
countVarsUnique ax = length $ nub' (getVarsAx ax)

countVars :: Axiom -> Int
countVars (Axiom (_,_,_,_,_,(p,_,q))) = mCountVars' p + mCountVars' q

mCountVars' = countVars' -- memoize countVars'
countVars' (Var _) = 1
countVars' (Root _) = 0
countVars' (Unary (OVar _) e) = 1 + mCountVars' e
countVars' (Unary _ e) = mCountVars' e
countVars' (Binary (OVar _) e1 e2) = 1 + mCountVars' e1 + mCountVars' e2
countVars' (Binary _ e1 e2) = mCountVars' e1 + mCountVars' e2

countConsts :: Axiom -> Int
countConsts (Axiom (_,_,_,_,_,(p,_,q))) = countConsts' p + countConsts' q

countConsts' (Var _) = 0
countConsts' (Root _) = 1
countConsts' (Unary _ e) = countConsts' e
countConsts' (Binary _ e1 e2) = countConsts' e1 + countConsts' e2

-- | Returns multiple bindings for the same variable, if any exist
sameVarBinding :: Eq a => [(String,a)] -> [(String,a)]
sameVarBinding [] = []
--sameVarBinding :: [(HsQName,HsExp)] -> [(HsQName,HsExp)]
sameVarBinding ((name,exp):xs) =
    let xs'' = [(n,e) | (n,e) <- xs, n == name]
        xs'  = [(n,e) | (n,e) <- xs'', e /= exp]
    in if null xs'
            then sameVarBinding xs
            else ((name,exp):xs') ++ sameVarBinding [(n,e) | (n,e) <- xs, n /= name]

getSubExpAx :: Axiom -> [Exp]
getSubExpAx (Axiom (_,_,_,_,_,(x,_,y))) = getSubExp x ++ getSubExp y

-- | returns a list of all subexpressions
getSubExp :: Exp -> [Exp]
getSubExp e = e : case e of
                    Unary _ x    -> getSubExp x
                    Binary _ x y -> getSubExp x ++ getSubExp y
                    _            -> []

replaceConstsWithVars :: [Exp] -> Exp -> Exp
replaceConstsWithVars vars exp = fst $ func vars exp
    where
        func [] e = (e,[])
        func vars e@(Var _) = (e,vars)
        func (x:xs) e@(Root _) = (x,xs)
        func vars (Unary f e) = let (e',vars') = func vars e
                                in (Unary f e',vars')
        func vars (Binary b e f) = let (e',v') = func vars e
                                       (f',vars') = func v' f
                                   in (Binary b e' f',vars')

-- | Replaces an Exp (exp) with an Exp (arg) in the main expression (rhs)
-- replaceExpInExp :: Rhs -> Exp -> Exp -> Exp
-- replaceExpInExp rhs (Var var) arg = replaceAllSubExp rhs var arg
-- replaceExpInExp rhs (Unary s1 e1) (Unary s2 e2) = replaceExpInExp rhs e1 e2
-- replaceExpInExp rhs (Binary s1 p1 p2) (Binary s2 e1 e2)
        -- = replaceExpInExp (replaceExpInExp rhs p1 e1) p2 e2
-- replaceExpInExp rhs _  _   = rhs

-- replaceAllSubExp :: Rhs -> String -> Exp -> Exp
-- replaceAllSubExp rhs v arg = case rhs of
    -- Var v'         -> v == v' ? arg $ rhs
    -- Unary s e      -> makeU s $ replaceAllSubExp e v arg
    -- Binary s e1 e2 -> makeB s (replaceAllSubExp e1 v arg) (replaceAllSubExp e2 v arg)
    -- _              -> rhs

replaceAllSubExp :: Rhs -> Map String Exp -> Exp
replaceAllSubExp rhs bind = case rhs of
    Var v    -> if Map.member v bind then bind Map.! v else rhs
    Unary (OVar v) e -> let s = if Map.member v bind then bind Map.! v else rhs
                        in if isRoot s
                            then Unary (Oper (fromRoot s)) $ replaceAllSubExp e bind
                            else Unary (OVar v) $ replaceAllSubExp e bind
    Unary s e      -> Unary s $ replaceAllSubExp e bind
    Binary (OVar v) e1 e2 -> 
                        let s = if Map.member v bind then bind Map.! v else rhs
                        in if isRoot s
                           then Binary (Oper (fromRoot s)) (replaceAllSubExp e1 bind) (replaceAllSubExp e2 bind)
                           else Binary (OVar v) (replaceAllSubExp e1 bind) (replaceAllSubExp e2 bind)
    Binary s e1 e2 -> Binary s (replaceAllSubExp e1 bind) (replaceAllSubExp e2 bind)
    _              -> rhs

-- replaceAllSubExp2 y'@(Var "x") v@(Var "x") c@(Root "T")
-- replace all instances
replaceAllSubExp2 :: Exp -> Exp -> Exp -> Exp
-- replace every "v" with "arg" in "exp"
replaceAllSubExp2 exp v arg | exp == v = arg
replaceAllSubExp2 exp v arg = case exp of
--    Var v'      ->  v == exp ? arg $ exp
    Unary s e    -> let e' = replaceAllSubExp2 e v arg
                    in Unary s e'
    Binary s e1 e2 ->
                    let e1' = (replaceAllSubExp2 e1 v arg) 
                        e2' = (replaceAllSubExp2 e2 v arg)
                    in Binary s e1' e2'
    _           ->  exp

-- replace only one instance
replaceOneSubExp2 :: Exp -> Exp -> Exp -> Exp
replaceOneSubExp2 exp v arg | exp == arg = v
replaceOneSubExp2 exp v arg = case exp of
--     Var v'         ->  v == exp ? arg $ exp
    Unary s e      -> let e' = replaceOneSubExp2 e v arg
                      in Unary s e'
    Binary s e1 e2 -> let e1' = (replaceOneSubExp2 e1 v arg) 
                      in if e1' /= e1
                          then Binary s e1' e2
                          else 
                            let e2' = (replaceOneSubExp2 e2 v arg)
                            in Binary s e1' e2'
    _              ->  exp

replaceLhsRhsWm :: Exp -> Exp -> Exp -> [Exp] -- replace lhs with rhs in wm
replaceLhsRhsWm lhs rhs wm | wm == lhs
    = [rhs]
replaceLhsRhsWm lhs rhs (Unary u wm)
    = map (Unary u) $ replaceLhsRhsWm lhs rhs wm
replaceLhsRhsWm lhs rhs (Binary b w1 w2)
    =    map (\x -> Binary b x w2) (replaceLhsRhsWm lhs rhs w1)
      ++ map (\x -> Binary b w1 x) (replaceLhsRhsWm lhs rhs w2)
replaceLhsRhsWm _ _ wm = [wm]

containsExp :: WM -> Exp -> Bool
containsExp wm exp | wm == exp = True
containsExp wm exp = case wm of
                        (Unary _ e)    -> containsExp e exp
                        (Binary _ e f) -> containsExp e exp || containsExp f exp
                        _              -> False

notnull = not . null


wschars = " \t\r\n"
strip :: String -> String
strip = lstrip . rstrip
lstrip s = case s of
                  [] -> []
                  (x:xs) -> if elem x wschars
                            then lstrip xs
                            else s
rstrip = reverse . lstrip . reverse

-- Function to simulate if-then-else
if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y

zipIf :: [Bool] -> [a] -> [a] -> [a]
zipIf = zipWith3 if'

infixr 1 ?
(?) :: Bool -> a -> a -> a
(?) = if'


readFileSafe :: FilePath ->  TextEncoding -> IO String
readFileSafe f enc = readFileSafe' f enc
     `catch`
        (\e -> do putStrLn ("Error in reading file " ++ f)
                  putStrLn $ "Exception: " ++ show (e :: IOException)
                  return "")


-- | Read file after checking its existence and permissions
readFileSafe' :: FilePath ->  TextEncoding -> IO String
readFileSafe' f enc = do
       e <- doesFileExist f
       if (not e)
         then do
           putStrLn $ "File " ++ f ++ " does not exist."
           return ""
         else do
           p <- getPermissions f
           if (not (readable p))
             then do
               putStrLn $ "Unable to read file " ++ f ++ "."
               return ""
             else do
               h <- openFile f ReadMode
               hSetEncoding h enc
               text <- hGetContents h
               putStrLn $ "Reading file " ++ show f ++ ", file length= " ++ show (length text)
               hClose h
               return text

nub' :: (Ord a) => [a] -> [a]
nub' = go Set.empty
  where go _ [] = []
        go s (x:xs) | Set.member x s = go s xs
                    | otherwise    = x : go (Set.insert x s) xs

nubBy' :: (Ord b) => (a -> b) -> [a] -> [a]
nubBy' = go Set.empty
  where go _ _ [] = []
        go s f (x:xs) | Set.member x' s = go s f xs
                      | otherwise       = x : go (Set.insert x' s) f xs
            where x' = f x


unlines' [] = []
unlines' [l] = l
unlines' (l:ls) = l ++ '\n' : unlines' ls

printExp :: Exp -> String
printExp (Root s) = "(Root " ++ s ++ ")"
printExp (Var v)  = "(Var " ++ v ++ ")"
printExp (Unary u e) = "(Unary " ++ show u ++ " " ++ show e ++ ")"
printExp (Binary b e1 e2) = "(Binary " ++ show b ++ " " ++ show e1 ++ " " ++ show e2 ++ ")"

fst' (x,_,_) = x
snd' (_,x,_) = x
thd' (_,_,x) = x

getUnaryOper (Unary (Oper f) _) = f

fromLeft (Left x) = x
fromRight (Right x) = x

boolToInt :: Bool -> Int
boolToInt True = 1
boolToInt False = 0

