-------------------------------------------------------------------------------
--   PARSING FUNCTIONS
-------------------------------------------------------------------------------

module Parsing where
import Instances

import Text.ParserCombinators.ReadP
import Data.List
import Data.Word
import Data.Char
import Data.Time
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import System.IO
import Control.Monad (liftM)
import Data.Function (on)
import Debug.Trace

emptyTime = read "2014-08-30 17:05:15.1653868 UTC" :: UTCTime

{-
1 + (1 + 1)

x + (x + x)
x + (x + y)
x + (y + x)
x + (y + y)
x + (y + z)

1 + 1
x + x
x + y

-}


l = read "((1 * 3) + (1 * 4))" :: Exp
r = read "(7)" :: Exp

-- get all term shapes from the set of examples
makeShapes :: (Lhs,Rhs) -> Map Exp (Substitution,Rhs)
makeShapes (exp,rhs) =
    let siz  = size exp
        (consts,clen) = let c = map makeR $ getConsts exp
                            cl = length c
                        in if cl > 3
                            then let set = nub' c
                                 in (set,length set)
                            else (c,cl)
        singles = [(Var v,(Map.singleton v c,Root c))
                                | v <- ["x","y","z"], (Root c) <- consts]
        vars = [[Var [x],Var [y],Var [z]] | x <- "xyz",y <- "xyz",z <- "xyz"]
               --map (map makeV) [["x","x","x"],["x","x","y"],["x","y","x"],["x","y","y"],["x","y","z"]]
        constantsToVars vs cs exp' = [foldl (\e (v,c) -> replaceOneSubExp2 e v c) exp' (zip vs cs),
                                      foldl (\e (v,c) -> replaceAllSubExp2 e c v) exp' (zip vs cs)]
        result = Map.fromList
                    . filter (not . containsConst . fst)
                    $ [(exp',(fromJust bind,rhs))
                            | cs <- permutations consts,
                              vs <- vars,
                              exp' <- constantsToVars vs cs exp,
                              let bind = varConstBinding exp' exp,
                              isJust bind && (not . Map.null) (fromJust bind)]
    in if siz > 7 || clen < 1 || clen > 3
        then Map.fromList singles
        else if Map.null result
                then error $ "makeShapes: empty result " ++ show exp ++ "::" ++ show rhs
                else result

extractConcepts :: UTCTime -> Item -> [Concept]
extractConcepts time (Item lhs _   r) | r < 1
    =    [C (0,0,1,time,time,makeR c) | c <- getConsts lhs]
      ++ [C (1,0,1,time,time,makeR u) | u <- getUnary lhs]
      ++ [C (2,0,1,time,time,makeR b) | b <- getBinary lhs]
extractConcepts time (Item lhs rhs _)
    =    [C (0,0,1,time,time,makeR c) | c <- getConsts lhs]
      ++ [C (1,0,1,time,time,makeR u) | u <- getUnary lhs]
      ++ [C (2,0,1,time,time,makeR b) | b <- getBinary lhs]
      ++ [C (0,1,1,time,time,makeR c) | c <- getConsts rhs]
      ++ [C (1,1,1,time,time,makeR u) | u <- getUnary rhs]
      ++ [C (2,1,1,time,time,makeR b) | b <- getBinary rhs]
insertInConcepts :: Set Concept -> Concept -> Set Concept
insertInConcepts cs c@(C (a,rew,f,_,last',e)) =
    let index' = Set.lookupIndex c cs
    in if isNothing index'
        then Set.insert c cs
        else let index = fromJust index'
                 (C (_,rew',freq,f',_,_)) = Set.elemAt index cs
             in Set.insert (C (a,max rew rew',f+freq,f',last',e)) cs

parseItemsFile :: FilePath -> IO [Item]
parseItemsFile itemsFile = do
        text <- readFileSafe itemsFile utf8
        return [item | (Just item) <- [maybeRead l | l <- map strip (lines text), not (null l), take 1 l == "("] ]
        
isVar (Var _) = True
isVar _       = False
type Error = String
type Warnings = [String]
-- | Read and parse an agent from a file
parseAgent :: FilePath -> IO (Either Error (Warnings,Agent))
parseAgent f = do
        text <- readFileSafe f utf8
        let lines' = filter (not . null . snd) $ zip [1..] (map strip $ lines text)
        if null lines'
        then return $ Left $ "Error: Empty agent file " ++ f ++ "."
        else do
        let com = if (take 2 . snd $ head lines') == "{-"
                  then (takeWhile (\x -> not ("-}" `isSuffixOf` x)) $ map snd lines') ++ ["-}"]
                  else []
        let restLines = 
                   if (take 2 . snd $ head lines') == "{-"
                   then let rest = dropWhile (\(num,line) -> not ("-}" `isSuffixOf` line))  lines'
                        in if null rest then rest else tail rest
                   else lines'
        if null restLines
        then return $ Left $ "Error: Empty agent file " ++ f ++ "."
        else do
        let axiomLines = map (\(n,x) -> (n,maybeRead x :: Maybe Axiom))
                         $ filter (\(n,x) -> take 3 x == "(A," && take 1 (reverse x) == ")") restLines
        if any isNothing (map snd axiomLines)
        then return . Left . head $ ["Error parsing axiom line " ++ show i | (i,Nothing) <- axiomLines]
        else do
        let axioms' = Set.fromList [a | (_,Just a) <- axiomLines]
        let axioms   = Set.filter (\(Axiom (_,_,_,_,_,(x,_,_))) -> not (isVar x)) axioms'
        
        let conceptLines = map (\(n,x) -> (n,maybeRead x))
                           $ filter (\(n,x) -> take 3 x == "(C," && take 1 (reverse x) == ")") restLines
        if any isNothing (map snd conceptLines)
        then return . Left . head $ ["Error parsing concept line " ++ show i | (i,Nothing) <- conceptLines]
        else do
        let concepts = Set.fromList [c | (_,Just c) <- conceptLines]
        let edgeLines = map (\(n,x) -> (n,maybeRead x))
                        $ filter (\(n,x) -> take 3 x == "(E," && take 1 (reverse x) == ")") restLines
        if any isNothing (map snd edgeLines)
        then return . Left . head $ ["Error parsing edge line " ++ show i | (i,Nothing) <- edgeLines]
        else do
        let patterns = [((e1,e2),(b,set)) | (_,Just (Edge (e1,e2,b,set))) <- edgeLines]
        (width,wwarn) <- do
                    let w = getParam "Width" axioms'
                    if w == ""
                    then return (8,"Width parameter not defined. Using default value 8")
                    else do let w' = maybeRead w
                            if isNothing w'
                            then return (8,"Error in width parameter " ++ w ++ ". It should be an integer. Using default value 8") 
                            else return (fromJust w',"")
        (depth,dwarn) <- do 
                    let d = getParam "Depth" axioms'
                    if d == ""
                    then return (10,"Depth parameter not defined. Using default value 10")
                    else do let d' = maybeRead d
                            if isNothing d'
                            then return (10,"Error in depth parameter. It should be an integer. Using default value 10")
                            else return (fromJust d',"")
        (axiom,awarn) <- do
                    let a = getParam "LtmSize" axioms'
                    if a == ""
                    then return (250,"LtmSize parameter not defined. Using default value 250")
                    else do let a' = maybeRead a
                            if isNothing a'
                            then return (250,"Error in LtmSize parameter. It should be an integer. Using default value 250")
                            else return (fromJust a',"")
        (redun,rwarn) <- do
                    let a = getParam "Redundancy" axioms'
                    if a == ""
                    then return (False,"Redundancy parameter not defined. Using default value False")
                    else do let a' = maybeRead a
                            if isNothing a'
                            then return (False,"Error in Redundancy parameter. It should be True or False. Using default value False")
                            else return (fromJust a',"")
        (consis,cwarn) <- do
                     let a = getParam "Consistency" axioms'
                     if a == ""
                     then return (True,"Consistency parameter not defined. Using default value True")
                     else do let a' = maybeRead a
                             if isNothing a'
                             then return (True,"Error in Consistency parameter. It should be True or False. Using default value True")
                             else return (fromJust a',"")
        (mode,mwarn) <- do
                   let a = getParam "Mode" axioms'
                   if a == ""
                   then return (Popper,"Mode parameter not defined. Using default value Popper")
                   else do let a' = maybeRead a
                           if isNothing a'
                           then return (Popper,"Error in Mode parameter. It should be Popper or Einstein. Using default value Popper")
                           else return (fromJust a',"")
        iter  <- do let w = getParam "Iterations" axioms'
                    if w == ""
                    then return 0
                    else do let w' = maybeRead w
                            if isNothing w'
                            then return 0
                            else return $ fromJust w'
        let graph    = makeGraph patterns
        let patt     = Set.fromList
                            $ (concat [[x,y] | ((x,y),_) <- patterns])
                              ++ map Var ["x","y","z"]
        let rew      = Set.fromList [Rew (arity,s) | C (arity,rew,_,_,_,(Root s)) <- Set.toList concepts, rew > 0]
        let warnings = filter (not . null) ["Parsed agent " ++ f,wwarn,dwarn,awarn,rwarn,cwarn,mwarn]
        return $ Right (warnings,
                          Agent (f,unlines com)
                                (width,depth,axiom,(redun,consis,mode,iter))
                                (makeLTM axioms,concepts,graph,patt,rew,[])
                        )

getParam :: String -> Set Axiom -> String
getParam s axioms = let r = [x | (Axiom (0,0,True,_,_,(Var s',Bi,(Root x)))) <- (Set.toList axioms), s == s']
                    in if null r
                        then ""
                        else head r

findInfixIndex :: (Eq a) => [a] -> [a] -> Maybe Int
findInfixIndex needle haystack
    = (\x -> if null x then Nothing else Just (fst $ head x))
      . dropWhile (\(_,x) -> not $ isPrefixOf needle x) 
        $ zip [0..] (tails haystack)

prettyIP :: Item -> String
prettyIP (Item p e v) = show p ++ " = " ++ show e ++ ", " ++ show v

readChar :: ReadP Char
readChar = do
        c <- get
        if c == '\\'
        then get
        else if c `elem` "()[],\" \t\n"
             then pfail 
             else return c
{- readChar :: ReadP Char
readChar = (string "\\(" >> return '(')
           <++ (string "\\)" >> return ')')
           <++ (string "\\[" >> return '[')
           <++ (string "\\]" >> return ']')
           <++ (string "\\\"" >> return '"')
           <++ (string "\\\\" >> return '\\')
           <++ (string "\\," >> return ',')
           <++ readChar' 
readStrU :: String -> ReadP String -- string without quotations, cannot contain space, "(", ")"
readStrU str = do
    s <- look
    if null s || (head s) == ' ' || (head s) == '(' || (head s) == ')'
    then return str
    else do
        c <- readChar
        readStrU $ str ++ [c]
-}
readStrQ :: ReadP String -- quoted string, e.g. "str"
readStrQ = between (char '"') (char '"') (many readChar)

readStr :: ReadP String -- string, with or without quotes
readStr = do
    (str,source) <- gather (readStrQ <++ (many readChar))
    if source `elem` ["x","y","z"] || null source
    then pfail
    else return str

readVarX x = string x >> return (Var x)

readVarV :: ReadP Exp
readVarV = readbracketed $ do
    skipSpaces
    string "\\v"
    satisfy isSpace
    skipSpaces
    v <- readStr
    skipSpaces
    return $ makeV v

readVar :: ReadP Exp
readVar = readVarX "x" <++ readVarX "y" <++ readVarX "z" <++ readVarV

readUnary :: ReadP Exp
readUnary = between (char '(') (char ')') $ do
    skipSpaces
    s <- readOper
    satisfy isSpace
    skipSpaces
    e <- readExp'
    skipSpaces
    return $ Unary s e

readBinary :: ReadP Exp
readBinary = between (char '(') (char ')') $ do
    skipSpaces
    e1 <- readExp'
    satisfy isSpace
    skipSpaces
    s <- readOper
    satisfy isSpace
    skipSpaces
    e2 <- readExp'
    skipSpaces
    return $ Binary s e1 e2

readRoot :: ReadP Exp
readRoot = between (char '(') (char ')') $ do
    skipSpaces
    s <- readStr
    skipSpaces
    return $ makeR s
   
readExp' :: ReadP Exp
readExp' = 
    readVar <++ readBinary <++ readUnary <++ readRoot <++ (readStr >>= return . makeR)

readExp1, readExp2, readExpMain :: ReadP Exp
readExp1 = readbracketed readExp' <++ readExp'
readExp2 = readExp' <++ readbracketed readExp'

readExpMain = 
              (do   e1 <- readExp'          -- read binary without brackets
                    satisfy isSpace
                    skipSpaces
                    s <- readOper
                    satisfy isSpace
                    skipSpaces
                    e2 <- readExp'
                    return $ Binary s e1 e2
                  )
              <++ readBinary                    -- read binary with brackets
              <++ (do   s <- readOper           -- read unary without brackets
                        satisfy isSpace
                        skipSpaces
                        e <- readExp'
                        return $ Unary s e
                    )
              <++ readUnary                     -- read unary with brackets
              <++ readVar                       -- read variable without brackets
              <++ readbracketed readVar         -- read variable with brackets
              <++ (readStr >>= return . makeR)  -- read root without brackets
              <++ readRoot                      -- read root with brackets

readOper :: ReadP Oper
readOper = do
    (char 'x' >> return (OVar "x"))
    <++ (char 'y' >> return (OVar "y"))
    <++ (char 'z' >> return (OVar "z"))
    <++
    (do s <- readStr
        return (Oper s))
readbracketed :: ReadP a -> ReadP a
readbracketed p = do
    do  skipSpaces
        char '('
        result <- p
        skipSpaces
        char ')'
        skipSpaces
        return result
-- (A,-0.9663303236975398,2,True,2015-01-28 11:20:49.5753238 UTC,2015-01-28 11:20:49.6534517 UTC,((1 # 7) + 2),▶,(1 # 9))
readAxiom :: ReadP Axiom
readAxiom = between (string "(A,") (char ')') $ do
    v <- munch1 (/= ',')
    char ','
    f <- readPosInt
    char ',' 
    isfact <- (string "True" >> return True) <++ (string "False" >> return False) -- munch1 (\x -> x /= ',')
    char ','
    first <- munch1 (/= ',')
    char ','
    last <- munch1 (/= ',')
    char ','
    e1 <- readExp1
    dir <- readDir
    e2 <- readExp1 -- (readbracketed (readVarX "x" <++ readVarX "y" <++ readVarX "z")) <++ readExp'
    let first' = maybeRead first
    let last' = maybeRead last
    let v' = maybeRead v
    if isNothing first' || isNothing last' || isNothing v'
    then pfail
    else return $ Axiom (fromJust v',f,isfact,fromJust first',fromJust last',(e1,dir,e2))

instance Read Exp where
    readsPrec _ s = readP_to_S readExpMain s

instance Read Axiom where
    readsPrec _ s = readP_to_S readAxiom s
-- 0,1,4,2015-01-28 10:56:16.9863506 UTC,2015-01-28 10:56:23.3150524 UTC,(-1)
readConcept :: ReadP Concept
readConcept = between (string "(C,") (char ')') $ do
    arity <- readPosInt
    char ','
    rew <- readPosInt
    char ','
    freq <- readPosInt
    char ','
    first <- munch1 (/=',')
    char ','
    last <- munch1 (/=',')
    char ','
    exp <- readExp1
    let first' = maybeRead first
    let last' = maybeRead last
    if isNothing first'
    then pfail
    else do
    if isNothing last'
    then pfail
    else return $ C (arity,rew,freq,fromJust first',fromJust last',exp)

instance Read Concept where
    readsPrec _ s = readP_to_S readConcept $ strip s

readEdge :: ReadP Edge
readEdge = between (string "(E,") (string ")") $ do
    e1 <- readExp1
    char ','
    e2 <- readExp1
    char ','
    b <- readTruth
    char ','
    list <- between (char '[') (char ']') $ sepBy readConstArray (char ',')
    return $ Edge (e1,e2,b,Set.fromList list)
readConstArray :: ReadP [String]
readConstArray = between (char '[') (char ']') (sepBy readStr (char ','))

instance Read Edge where
    readsPrec _ s = readP_to_S readEdge $ strip s

readItems :: ReadP Items
readItems = do 
    items <- sepBy1 readItem (char ',')
    skipSpaces
    eof
    return $ Items items

readItem :: ReadP Item
readItem = do
    skipSpaces
    lhs <- readExpMain
    skipSpaces
    viab <- (string itemPositive >> return 1) <++ (string itemNegative >> return (-1))
    skipSpaces
    rhs <- readExpMain
    skipSpaces
    eof
    return $ Item lhs rhs viab

readPosInt :: ReadP Int
readPosInt = do
    digits <- munch1 isDigit
    return (read digits :: Int)

readNegInt :: ReadP Int
readNegInt = do
    char '-'
    digits <- munch1 isDigit
    return $ 0 - (read digits :: Int)

readInt = readNegInt <++ readPosInt

readDir :: ReadP Dir
readDir = readDirBi <++ readDirUni <++ readDirNeg

readDirBi  = choice (map string deepRule) >> return Bi
readDirUni = choice (map string shallowRule) >> return Uni
readDirNeg = choice (map string negativeRule) >> return Neg

instance Read Dir where
    readsPrec _ s = readP_to_S readDir s

readDouble = readNegDouble <++ readPosDouble
readPosDouble = do
    value <- readDouble' <++ (readPosInt >>= (\r -> return $ fromIntegral r))
    return value
readNegDouble = do
    char '-'
    value <- readDouble' <++ (readPosInt >>= (\r -> return $ fromIntegral r))
    return $ 0 - value

readDouble' = do
    digits1 <- munch1 isDigit
    char '.'
    digits2 <- munch1 isDigit
    return $ (read (digits1 ++ "." ++ digits2) :: Double)
    
instance Read Item where
    readsPrec _ s = readP_to_S readItem $ strip s

instance Read Items where
    readsPrec _ s = readP_to_S readItems $ strip s

readRewarding :: ReadP Rewarding
readRewarding = do
    string "(R,"
    arity <- readInt
    string ","
    symbol <- readStr
    string ")"
    return $ Rew (arity,symbol)

instance Read Rewarding where
    readsPrec _ s = readP_to_S readRewarding $ strip s

instance Show Mode where
    show Popper = "Popper"
    show Einstein = "Einstein"
instance Read Mode where
    readsPrec _ s = readP_to_S readMode $ strip s
    
readMode :: ReadP Mode
readMode = (string "Popper" >> return Popper) <++ (string "Einstein" >> return Einstein)

maybeRead :: Read a => String -> Maybe a
maybeRead = fmap fst . listToMaybe . reads
readMaybe :: Read a => String -> Maybe a
readMaybe = maybeRead

updateRewarding :: Set Rewarding -> Item -> Set Rewarding
updateRewarding s (Item _ y _) = 
    let consts = map (\x -> Rew (0,x)) $ getConsts y
        unary  = map (\x -> Rew (1,x)) $ getUnary y
        binary = map (\x -> Rew (2,x)) $ getBinary y
    in Set.union s $ Set.fromList (consts ++ unary ++ binary)

readTruth :: ReadP Truth
readTruth = (string "Invalid" >> return Invalid) 
            <++ (string "Satisfiable" >> return Satisfiable) 
            <++ (string "Valid" >> return Valid)

instance Read Truth where
    readsPrec _ s = readP_to_S readTruth $ strip s
