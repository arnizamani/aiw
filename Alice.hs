-- Author: Abdul Rahim Nizamani, University of Gothenburg, 2015
-- Licensed under GNU General Public License
-- use ghc option -optl-mwindows to hide command window

module Main where

import Instances
import Parsing
import AliceLib
import Domains
import Domains.Arithmetic
import Domains.PropLogic
import Domains.English
import Domains.XOR

import qualified Data.Function as F
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Char
import Graphics.UI.Gtk
import Graphics.UI.Gtk.Builder
import Data.Maybe
import Data.List
import Control.Monad
import Control.Monad.Trans(liftIO)
import Control.Concurrent.MVar
import Data.Time
import qualified Data.Text as T
import Control.Concurrent (forkIO,takeMVar,newEmptyMVar,putMVar)
import Test.QuickCheck
import System.IO 

data SavedState = Saved | Unsaved deriving Eq 

data LoadedState = Loaded | Free deriving Eq

type ProgramData  = Agent
type ProgramState = (SavedState,ProgramData)

data RunMode  = Auto | Manual deriving Eq

data RunState = Running | Singlestep | Stopped deriving Eq

appName = "Alice in Wonderland"
appVersion = "1.0.0"
appTitle = appName ++ " v" ++ appVersion


main = do
-- new mvars for holding program state
    loadedAgentMvar  <- newEmptyMVar
    currentAgentMvar <- newEmptyMVar
    runState         <- newEmptyMVar
    putMVar runState Stopped
    scoreMvar        <- newEmptyMVar
    putMVar scoreMvar ([] :: [(Int,Int)])
-- start GUI
    initGUI -- must be called before starting a GUI program
    widgetSetDefaultDirection TextDirLtr -- default direction is LTR
    builder <- builderNew
    builderAddFromFile builder "AIW-GUI.glade" -- load glade file (xml)
-- initialize graphical elements, assign event handlers, etc.
    assignEventHandlers builder loadedAgentMvar currentAgentMvar runState scoreMvar
    winMain <- builderGetObject builder castToWindow "windowMain"
    filechooserDomain <- builderGetObject builder castToFileChooserButton "filechooserDomain"
    vboxConsole   <- builderGetObject builder castToVBox "vboxConsole"
    widgetShowAll winMain           -- present main window to the user
    widgetHide filechooserDomain
    widgetHide vboxConsole
    mainGUI                         -- start the main GUI loop to receive events

assignEventHandlers builder loadedAgentMvar currentAgentMvar runState scoreMvar = do
    intitializeWindowMain builder loadedAgentMvar currentAgentMvar scoreMvar
    initiateWindowTrain builder loadedAgentMvar currentAgentMvar runState scoreMvar
    initiateDialogNew builder loadedAgentMvar currentAgentMvar
    initiateDialogOpen builder loadedAgentMvar currentAgentMvar
    initiateFileFilter1 builder
    
initiateFileFilter1 builder = do
    fileFilter1 <- builderGetObject builder castToFileFilter "filefilter1"
    fileFilterAddMimeType fileFilter1 "text/plain"
    fileFilterAddPattern fileFilter1 "*.domain"
intitializeWindowMain builder loadedAgentMvar currentAgentMvar scoreMvar = do
    winMain <- builderGetObject builder castToWindow "windowMain"
    windowSetTitle winMain appTitle
    console <- builderGetObject builder castToTextBuffer "textbufferConsole"
    b1 <- builderGetObject builder castToTextBuffer "textbuffer1"
    b2 <- builderGetObject builder castToTextBuffer "textbuffer2"
    b3 <- builderGetObject builder castToTextBuffer "textbuffer3"
    bAnswer <- builderGetObject builder castToTextBuffer "textbufferAnswer"
    closed <- builderGetObject builder castToLabel "closedAxioms"
    open <- builderGetObject builder castToLabel "openAxioms"
    -- Exit button exits the program, checks for unsaved data
    winMain `on` deleteEvent $ (liftIO (quitProgram loadedAgentMvar currentAgentMvar) >>= return)
    -- quitMenu exits the program, checks for unsaved data
    quitMenu <- builderGetObject builder castToImageMenuItem "imagemenuitemQuit"
    quitMenu `on` menuItemActivated $ (liftIO (quitProgram loadedAgentMvar currentAgentMvar) >> return ())
    -- new agent dialog
    dialogNew <- builderGetObject builder castToWindow "dialogNew"
    newMenu <- builderGetObject builder castToImageMenuItem "imagemenuitemNew"
    newMenu `on` menuItemActivated $ (fileNew dialogNew)
    newTool <- builderGetObject builder castToToolButton "toolbuttonNew"
    onToolButtonClicked newTool $ (fileNew dialogNew)
    -- open agent dialog
    dialogOpen <- builderGetObject builder castToWindow "filechooserDialog"
    openMenu <- builderGetObject builder castToImageMenuItem "imagemenuitemOpen"
    openMenu `on` menuItemActivated $ (fileOpen dialogOpen)
    openTool <- builderGetObject builder castToToolButton "toolbuttonOpen"
    onToolButtonClicked openTool $ (fileOpen dialogOpen)
    -- close agent
    closeMenu <- builderGetObject builder castToImageMenuItem "imagemenuitemClose"
    closeMenu `on` menuItemActivated $ (fileClose builder loadedAgentMvar currentAgentMvar)
    closeTool <- builderGetObject builder castToToolButton "toolbuttonClose"
    onToolButtonClicked closeTool $ (fileClose builder loadedAgentMvar currentAgentMvar)
    -- save agent
    saveMenu <- builderGetObject builder castToImageMenuItem "imagemenuitemSave"
    saveMenu `on` menuItemActivated $ (fileSave loadedAgentMvar currentAgentMvar)
    saveTool <- builderGetObject builder castToToolButton "toolbuttonSave"
    onToolButtonClicked saveTool $ (fileSave loadedAgentMvar currentAgentMvar)
    
    scoreBefor <- builderGetObject builder castToLabel"labelScoreBefore"
    scoreAfter <- builderGetObject builder castToLabel"labelScoreAfter"
    consoleMenu <- builderGetObject builder castToCheckMenuItem "menuitemConsole"
    vboxConsole   <- builderGetObject builder castToVBox "vboxConsole"
    -- show/hide Console box
    consoleMenu `on` checkMenuItemToggled $ do
        checked <- checkMenuItemGetActive consoleMenu
        if checked
        then do widgetShow vboxConsole
        else do widgetHide vboxConsole
    -- show training window
    windowTrain <- builderGetObject builder castToWindow "windowTrain"
    showTrain <- builderGetObject builder castToMenuItem "menuitemShowTraining"
    showTrain `on` menuItemActivated $ (widgetShowAll windowTrain)
    -- center button centers the text in both textviews
    toolCenter <- builderGetObject builder castToToggleToolButton "toolbuttonCenter"
    text1 <- builderGetObject builder castToTextView "textview1"
    text2 <- builderGetObject builder castToTextView "textview2"
    onToolButtonToggled toolCenter $ do
        active <- toggleToolButtonGetActive toolCenter
        if active
        then do textViewSetJustification text1 JustifyCenter
                textViewSetJustification text2 JustifyCenter
        else do textViewSetJustification text1 JustifyLeft
                textViewSetJustification text2 JustifyLeft
    -- show/hide Question box
    showQuestion <- builderGetObject builder castToCheckMenuItem "menuitemQuestion"
    vboxQuestion <- builderGetObject builder castToVBox "vboxQuestion"
    showQuestion `on` checkMenuItemToggled $ do
        checked <- checkMenuItemGetActive showQuestion
        if checked
        then do widgetShow vboxQuestion
        else do widgetHide vboxQuestion
    -- Clear agent
    toolClear <- builderGetObject builder castToToolButton "toolbuttonClear"
    onToolButtonClicked toolClear $ do
        current' <- tryTakeMVar currentAgentMvar
        if isNothing current'
        then printConsole console "Agent not loaded or not free."
        else do
          let (Agent h (w, d, l, (r, c, m, _)) (_,_,_,_,_,_)) = fromJust current'
          let patts = Set.fromList $ map Var ["x","y","z"]
          let new = Agent h (w, d, l, (r, c, m, 0)) (newLtm,Set.empty,Map.empty,patts,Set.empty,[])
          putMVar currentAgentMvar new
          showAgent b1 b2 closed open new
          labelSetText scoreBefor ""
          labelSetText scoreAfter ""
          swapMVar scoreMvar ([] :: [(Int,Int)])
          return ()
    -- Revert to the last saved agent
    toolBack <- builderGetObject builder castToToolButton "toolbuttonBack"
    onToolButtonClicked toolBack $ do
        saved'   <- tryTakeMVar loadedAgentMvar
        current' <- tryTakeMVar currentAgentMvar
        if isNothing saved'
        then printConsole console "No agent loaded."
        else do
          let saved = fromJust saved'
          if isNothing current'
          then do
            printConsole console "Agent not free or not changed."
          else do
          let current = fromJust current'
          if saved == current
          then return ()
          else do
          -- let (Agent h (w, d, l, (r, c, m, _)) (_,_,_,_,_,_)) = fromJust current'
          -- let new = Agent h (w, d, l, (r, c, m, 0)) (newLtm,Set.empty,Map.empty,Set.empty,Set.empty,[])
          -- putMVar currentAgentMvar new
          showAgent b1 b2 closed open saved
          labelSetText scoreBefor ""
          labelSetText scoreAfter ""
          swapMVar scoreMvar ([] :: [(Int,Int)])
          textBufferSetText b3 ""
          textBufferSetText bAnswer ""
          putMVar loadedAgentMvar  saved
          putMVar currentAgentMvar saved
          return ()

fileNew dialogNew = widgetShowAll dialogNew

fileOpen dialogOpen = widgetShowAll dialogOpen
fileSave loadedAgentMvar currentAgentMvar = do
    loaded' <- tryTakeMVar loadedAgentMvar
    if isNothing loaded'
    then return ()
    else do let loaded = fromJust loaded'
            current' <- tryTakeMVar currentAgentMvar
            if isNothing current'
            then putMVar loadedAgentMvar loaded
            else do let current = fromJust current'
                    let areSame = loaded == current
                    if areSame
                    then do putMVar loadedAgentMvar loaded
                            putMVar currentAgentMvar current
                    else do saveAgent False current
                            putMVar loadedAgentMvar current 
                            putMVar currentAgentMvar current 
    
fileClose builder loadedAgentMvar currentAgentMvar = do
    buffer1 <- builderGetObject builder castToTextBuffer "textbuffer1"
    buffer2 <- builderGetObject builder castToTextBuffer "textbuffer2"
    buffer3 <- builderGetObject builder castToTextBuffer "textbuffer3"
    buffer4 <- builderGetObject builder castToTextBuffer "textbuffer4"
    scoreBefor <- builderGetObject builder castToLabel"labelScoreBefore"
    scoreAfter <- builderGetObject builder castToLabel"labelScoreAfter"
    closedAxioms <- builderGetObject builder castToLabel"closedAxioms"
    openAxioms <- builderGetObject builder castToLabel"openAxioms"
    labelStatus1 <- builderGetObject builder castToLabel"labelStatus1"
    labelStatus2 <- builderGetObject builder castToLabel"labelStatus2"
    loaded' <- tryReadMVar loadedAgentMvar
    if isNothing loaded'
    then return ()
    else do
    let loaded = fromJust loaded'
    current' <- tryReadMVar currentAgentMvar
    if isNothing current'
    then do
        return ()
    else do
    let current = fromJust current'
    let areSame = loaded == current
    let clearUI = do -- empty text buffers to clear textviews
            textBufferSetText buffer1 ""
            textBufferSetText buffer2 ""
            textBufferSetText buffer3 ""
            textBufferSetText buffer4 ""
            labelSetText scoreBefor ""
            labelSetText scoreAfter ""
            labelSetText closedAxioms ""
            labelSetText openAxioms ""
            labelSetText labelStatus1 ""
            labelSetText labelStatus2 ""
    if areSame
    then do   -- empty agent mvars
            takeMVar loadedAgentMvar
            takeMVar currentAgentMvar
            clearUI
            return ()
    else do --msgBox <- messageDialogNew Nothing [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsClose ("Please save the agent before closing.")
            --dialogRun msgBox
            msgBox <- messageDialogNew Nothing [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsNone ("Do you want to save the agent before closing it?")
            dialogAddButton msgBox "Cancel" ResponseCancel
            dialogAddButton msgBox "No" ResponseNo
            dialogAddButton msgBox "Yes" ResponseYes
            reply <- dialogRun msgBox
            case reply of
                      ResponseCancel -> do widgetHide msgBox
                                           return True
                      ResponseNo  -> do takeMVar loadedAgentMvar
                                        takeMVar currentAgentMvar
                                        widgetHide msgBox
                                        clearUI
                                        return True
                      ResponseYes -> do
                            fileSave loadedAgentMvar currentAgentMvar
                            takeMVar loadedAgentMvar
                            takeMVar currentAgentMvar
                            widgetHide msgBox
                            clearUI
                            return True
                      _ -> do
                            widgetHide msgBox
                            return True
            return ()

initiateWindowTrain builder loadedAgentMvar currentAgentMvar runState scoreMvar = do
    buffer1 <- builderGetObject builder castToTextBuffer "textbuffer1"
    buffer2 <- builderGetObject builder castToTextBuffer "textbuffer2"
    buffer3 <- builderGetObject builder castToTextBuffer "textbuffer3"
    buffer4 <- builderGetObject builder castToTextBuffer "textbuffer4"
    console <- builderGetObject builder castToTextBuffer "textbufferConsole"
    answer  <- builderGetObject builder castToTextBuffer "textbufferAnswer"
    scoreB  <- builderGetObject builder castToLabel "labelScoreBefore"
    scoreA  <- builderGetObject builder castToLabel "labelScoreAfter"
    closed <- builderGetObject builder castToLabel "closedAxioms"
    open <- builderGetObject builder castToLabel "openAxioms"
    testButton <- builderGetObject builder castToToggleToolButton "toolbuttonTest"
    windowTrain <- builderGetObject builder castToWindow "windowTrain"
    windowTrain `on` deleteEvent $ liftIO (widgetHide windowTrain) >> return True
    -- add domains to the combobox
    comboboxDomains <- builderGetObject builder castToComboBox "comboboxDomains"
    
    let domains = ["Addition","Multiplication","Subtraction","Division",
                   "Arithmetic","Even","Odd","Modulo 3",
                   "XorAddBinary","XorAddDecimal",
                   "XorMulBinary","XorMulDecimal",
                   "LessThan","LessThanEqual",
                   "GreaterThan","GreaterThanEqual",
                   "Truth","Tautology",
                   "English","Other (load file)"]
    liststoreDomains <- comboBoxSetModelText comboboxDomains
    mapM (listStoreAppend liststoreDomains . T.pack) domains
    filechooserDomain <- builderGetObject builder castToFileChooserButton "filechooserDomain"
    comboboxDomains `on` changed $ do
        selected' <- comboBoxGetActive comboboxDomains
        if selected' < 0
        then return ()
        else do
        domain <- listStoreGetValue liststoreDomains (selected') >>= (return . map toLower . T.unpack)
        if "other" `isPrefixOf` domain
        then widgetShow filechooserDomain
        else widgetHide filechooserDomain
        return ()
    toolbuttonStop <- builderGetObject builder castToToolButton "toolbuttonStop"
    onToolButtonClicked toolbuttonStop $ do
        state <- takeMVar runState
        putMVar runState Stopped
    toolbuttonStart <- builderGetObject builder castToToolButton "toolbuttonStart"
    onToolButtonClicked toolbuttonStart $ do
        state <- takeMVar runState
        if state /= Stopped
        then putMVar runState state >> return ()
        else do
        putMVar runState state
        selected' <- comboBoxGetActive comboboxDomains
        if selected' < 0
        then do msgBox <- messageDialogNew (Just windowTrain) 
                                           [DialogModal,DialogDestroyWithParent] 
                                           MessageWarning 
                                           ButtonsClose 
                                           ("No domain selected.")
                response <- dialogRun msgBox
                widgetHide msgBox
                return ()
        else do domain <- listStoreGetValue liststoreDomains (selected') >>= (return . map toLower . T.unpack)
                agent' <- tryTakeMVar currentAgentMvar
                if isNothing agent'
                then do printConsole console $ "Agent not loaded."
                        return ()
                else do
                let agent = fromJust agent'
                testMode <- toggleToolButtonGetActive testButton
                putMVar currentAgentMvar agent
                swapMVar runState Running
                if domain /= "other (load file)"
                then forkIO' $ runIterations Auto testMode 1 (getFunc domain) [] 0 agent 
                                             buffer1 buffer2 buffer3 buffer4 
                                             console answer scoreB scoreA closed open
                                             currentAgentMvar runState scoreMvar windowTrain
                else do
                fchooserDomain <- builderGetObject builder castToFileChooser "filechooserDomain"
                itemsFile' <- fileChooserGetFilename fchooserDomain
                if isNothing itemsFile'
                then do printConsole console $ "No problems file selected."
                        return ()
                else do
                let itemsFile = fromJust itemsFile'
                items <- parseItemsFile itemsFile
                if null items
                then do printConsole console $ "Selected file does not contain any problem."
                        return ()
                else forkIO' $  runFile testMode 1 items [] 0 agent 
                                        buffer1 buffer2 buffer3 buffer4 
                                        console answer scoreB scoreA closed open
                                        currentAgentMvar runState scoreMvar windowTrain
    let readFunc lhs rhs eq' = do
            let eq = if eq' == 0 then "1" else "-1"
            let item = maybeRead ("(" ++ lhs ++ "," ++ rhs ++ "," ++ eq ++ ")") :: Maybe Item
            if isJust item
            then return item
            else do
            let item = maybeRead ("((" ++ lhs ++ ")," ++ rhs ++ "," ++ eq ++ ")") :: Maybe Item
            if isJust item
            then return item
            else do
            let item = maybeRead ("(" ++ lhs ++ ",(" ++ rhs ++ ")," ++ eq ++ ")") :: Maybe Item
            if isJust item
            then return item
            else do
            let item = maybeRead ("((" ++ lhs ++ "),(" ++ rhs ++ ")," ++ eq ++ ")") :: Maybe Item
            return item
    buttonQuestion <- builderGetObject builder castToButton "buttonQuestion"
    entryItems  <- builderGetObject builder castToEntry "entryItems"
    buttonQuestion `on` buttonActivated $ do
        textBufferSetText answer ""
        textItems <- entryGetText entryItems >>= (return . strip)
        if null textItems
        then printConsole console "Please enter a valid item in the boxes."
        else do
        let items' = (maybeRead textItems :: Maybe Items)
        if isNothing items'
        then printConsole console "Cannot parse item. Please provide a valid item."
        else do
        let items = getItems $ fromJust items'
        testMode' <- toggleToolButtonGetActive testButton
        let testMode = testMode' || any containsVarItem items
        agent' <- tryTakeMVar currentAgentMvar
        if isNothing agent'
        then printConsole console "No agent present. Please load an agent."
        else do
        putMVar currentAgentMvar (fromJust agent')
        forkIO' $ do state' <- tryTakeMVar runState
                     if isNothing state'
                     then return ()
                     else do
                     let state = fromJust state'
                     if state == Stopped
                     then do putMVar runState Singlestep
                             if (length items == 1)
                             then runIterations Manual testMode 1 (\_ -> return $ head items) [] 0 (fromJust agent')
                                                  buffer1 buffer2 buffer3 buffer4 
                                                  console answer scoreB scoreA closed open 
                                                  currentAgentMvar runState scoreMvar windowTrain
                             else runMultiItems Manual testMode 3 items [] 0 (fromJust agent')
                                                  buffer1 buffer2 buffer3 buffer4 
                                                  console answer scoreB scoreA closed open 
                                                  currentAgentMvar runState scoreMvar windowTrain
                             swapMVar runState state
                             return ()
                     else putMVar runState state
    toolbuttonStep <- builderGetObject builder castToToolButton "toolbuttonStep"
    onToolButtonClicked toolbuttonStep $ do
        testMode <- toggleToolButtonGetActive testButton
        selected' <- comboBoxGetActive comboboxDomains
        if selected' < 0
        then printConsole console "No domain selected. Please select one of the domains."
        else do 
        domain <- listStoreGetValue liststoreDomains (selected') >>= (return . map toLower . T.unpack)
        agent' <- tryTakeMVar currentAgentMvar
        if isNothing agent'
        then return ()
        else do
        putMVar currentAgentMvar (fromJust agent')
        forkIO' $ do
                state' <- tryTakeMVar runState
                if isNothing state'
                then return ()
                else do 
                let state = fromJust state'
                if  state == Stopped
                then do putMVar runState Singlestep
                        runIterations Manual testMode 1 (getFunc domain) [] 0 (fromJust agent')
                                        buffer1 buffer2 buffer3 buffer4 
                                        console answer scoreB scoreA closed open 
                                        currentAgentMvar runState scoreMvar windowTrain
                        swapMVar runState state
                        return ()
                else do putMVar runState state

runMultiItems Manual True size items prev total agent 
              b1 b2 b3 b4 console answer scoreB scoreA closed open 
              currentAgentMvar runState scoreMvar win = do
        if null items || any (\item -> not (containsVar (lhs item) || containsVar (rhs item))) items
        then printConsole console "Items do not contain variables. Multiple equations can only be solved if they contains variables."
        else do
        let (ltm,_,_,_,_,_) = agentMemory agent
        time <- getCurrentTime
        let vars = length (nub $ concat [getVars t ++ getVars t' | (Item t t' v) <- items, v >= 0])
        let facts = Set.toList $ ltmFacts ltm
        let binds = map (\(Item t t' v) -> 
                                let axiom = Axiom (fromIntegral v,1,True,time,time,(t,Bi,t'))
                                in [b | Just b <- (map (\x -> findVarBinding x axiom) facts)]
                        ) [item | item@(Item _ _ v) <- items, v >= 0]
        let negBinds = map (\(Item t t' v) -> 
                                let axiom = Axiom (fromIntegral v,1,True,time,time,(t,Bi,t'))
                                in [b | Just b <- (map (\x -> findVarBinding x axiom) facts)]
                           ) [item | item@(Item t _ v) <- items, v < 0, not (isVar t)]
        -- let singlePositive = [(var,e) | item@(Item (Var var) e v) <- items, v >= 0]
        let singleNegative = [(var,e) | item@(Item (Var var) e v) <- items, v <  0]
        let intersected = filter (\x -> length x == vars) $
                          if null binds
                          then []
                          else if length binds == 1
                               then filter (\b -> b == (b \\ singleNegative))
                                    -- . filter (\b -> b == (b `union` singlePositive))
                                    $ (head binds) \\ (concat negBinds)
                               else filter (not . null)
                                    . filter (\b -> b == (b \\ singleNegative))
                                    -- . filter (\b -> b == (b `union` singlePositive))
                                    $ (foldl (\b1 b2 -> b1 `mergeS` b2) (head binds) (tail binds))
                                         \\ (concat negBinds)
        --putStrLn $ "singleNegative: " ++ show singleNegative
        --let merged = filter (\b -> b == (b \\ singleNegative))
        --             $ (foldl (\b1 b2 -> b1 `mergeS` b2) (head binds) (tail binds))
        --putStrLn $ "merged: " ++ show merged
        --putStrLn $ "negBinds: " ++ show (concat negBinds)
        
        -- x+y=2, x*y=1
        -- (0,2) (2,0) (1,1)
        --             (1,1)
        -- x     = Circles
        -- (x,y) = (Circles,nucleus)
        score <- takeMVar scoreMvar
        --postGUISync $ do start1 <- textBufferGetStartIter b3
        --                 textBufferInsert b3 start1 $ show item ++ "\n"
        -- printConsole console $ "Item: " ++ show item ++ ": " ++ show resultBefore
        let result = (not $ null intersected) && length (head intersected) == vars
        let score' = if result then 1 else 0
        let newScore = ((score',score') : score)
        putMVar scoreMvar newScore
        -- postGUISync $ showIteration b3 b4 scoreB scoreA c newScore item ""
        postGUISync $ do
            if result
            then textBufferSetText answer $ (unlines (map show items))
                                            ++ (unlines (map (\(s,exp) -> s ++ " = " ++ show exp) $ head intersected))
            else textBufferSetText answer ("No solution found.\n" ++
                                           "items: \n" ++ unlines (map show items) ++
                                           "binds: \n" ++ unlines (map show binds) ++ 
                                           "intersected: \n" ++ unlines (map show intersected)
                                          )

getFunc domain = case domain of
                                "addition" -> additionItem
                                "multiplication" -> multItem
                                "subtraction" -> subtItem
                                "division" -> diviItem
                                "arithmetic" -> arithItem
                                "even"  -> evenItem
                                "odd"   -> oddItem
                                "modulo 3" -> mod3Item
                                "xoraddbinary" -> xorAddBinary
                                "xoradddecimal" -> xorAddDecimal
                                "xormulbinary" -> xorMulBinary
                                "xormuldecimal" -> xorMulDecimal
                                "truth"    -> truthItem
                                "tautology"    -> tautItem
                                "english"  -> langItem
                                "lessthan" -> lessThanItem
                                "lessthanequal" -> lessThanEqualItem
                                "greaterthan" -> greaterThanItem
                                "greaterthanequal" -> greaterThanEqualItem
mergeS :: (Eq a, Eq b) => [[(a,b)]] -> [[(a,b)]] -> [[(a,b)]]
mergeS [] _ = []
mergeS _ [] = []
mergeS xs ys = filter (not . null) $
                [[(x,a) | (x,a) <- x',(y,b) <- y',x == y, a == b]
                 ++ [(x,a) | (x,a) <- x', (lookup x y') == Nothing]
                 ++ [(y,b) | (y,b) <- y', (lookup y x') == Nothing]
                    | x' <- xs,y' <- ys]

        -- binds: [[("x",(Circles))],[("x",(Circles))]]
        --        [[("y",(sun))]]
        --      solution: [[("x",(Circles)),("y",(sun))],[("x",(Circles)),("y",(sun))]]
        -- binds = [[("x",(Circles))],[("x",(Circles))]]
        --         [[("x",(Circles)),("y",(sun))]]
        --      solution: [[("x",(Circles)),("y",(sun))],[("x",(Circles)),("y",(sun))]]
        -- binds = [[("x",(1)),("y",(1))],[("x",(0)),("y",(2))]]
        --         [[("x",(1)),("y",(1))]]
        --      solution: [[("x",(1)),("y",(1))]]

runFile test size items prev total agent 
              b1 b2 b3 b4 console answer scoreB scoreA closed open 
              currentAgentMvar runState scoreMvar win = do
        state <- readMVar runState
        if state == Stopped
        then return ()
        else do
        if null items
        then do swapMVar runState Stopped
                return ()
        else do
        let item@(Item t t' v) = head items
        score <- takeMVar scoreMvar
        let c = if test then getIterations agent else getIterations agent + 1
        postGUISync $ do start1 <- textBufferGetStartIter b3
                         textBufferInsert b3 start1 $ show c ++ ": " ++ show item ++ "\n"
        let string = show (total+1) ++ ": " ++ normalizeOutput (show t ++ "=" ++ show t') ++ " : " ++ show v
        let (ltm,concepts,graph,_,_,_) = agentMemory agent
        -- test run: score before udpating the theory
        time <- getCurrentTime
        (_,_,_,resultBefore,_,_,_) <- findDelta True False time agent item
        -- actual run: score after updating the theory
        (newAgent,resultAfter,f',(computation,_)) <- runOnce test False agent item
        printConsole console $ "Item: " ++ show item ++ ": " ++ show resultAfter
        when (not test) $ swapMVar currentAgentMvar newAgent >> return ()
        let afterScore = boolToInt resultAfter
        let beforeScore = boolToInt resultBefore
        let newScore = ((beforeScore,afterScore) : score)
        putMVar scoreMvar newScore
        let size' = size + 1
        let changes' = [(if a >= 0 then "+ " else "    - ") ++ show lhs ++ show dir ++ show rhs
                            | (a,Axiom (_,_,_,_,_,(lhs,dir,rhs))) <- f']
        let changes'' = if null changes' then changes' else (show c) : changes'
        -- printConsole console $ show item
        postGUISync $ showIteration b4 scoreB scoreA c newScore item $ unlines changes''
        postGUISync $ showAgent b1 b2 closed open newAgent
        textBufferSetText answer ""
        runFile test size' (tail items)
                (string : prev) (total+1) newAgent 
                b1 b2 b3 b4 console answer scoreB scoreA closed open currentAgentMvar runState scoreMvar win

        
runIterations Manual True size itemGenerator prev total agent 
              b1 b2 b3 b4 console answer scoreB scoreA closed open 
              currentAgentMvar runState scoreMvar win = do
        score <- takeMVar scoreMvar
        item@(Item t t' v) <- generate (itemGenerator 1000)
        let c = getIterations agent + 1
        --postGUISync $ do start1 <- textBufferGetStartIter b3
        --                 textBufferInsert b3 start1 $ show c ++ ": " ++ show item ++ "\n"
        time <- getCurrentTime
        (_,_,_,resultBefore,_,_,(_,computation,subst)) <- findDelta True False time agent item
        printConsole console $ "Item: " ++ show item ++ ": " ++ show resultBefore
        let beforeScore = boolToInt resultBefore
        let afterScore = beforeScore
        let newScore = ((beforeScore,afterScore) : score)
        putMVar scoreMvar newScore
        postGUISync $ showIteration b4 scoreB scoreA c newScore item ""
        if (not . null) computation
        then postGUISync $ textBufferSetText answer $ showSolution computation
        else if (not . null) subst
             then postGUISync $ textBufferSetText answer $ unlines (map (\(s,exp) -> s ++ " = " ++ show exp) subst)
             else postGUISync $ textBufferSetText answer "No solution found."

runIterations runMode test size itemGenerator prev total agent 
              b1 b2 b3 b4 console answer scoreB scoreA closed open 
              currentAgentMvar runState scoreMvar win = do
    state <- readMVar runState
    if state == Stopped && runMode == Auto
    then return ()
    else do
        score <- takeMVar scoreMvar
        let c = getIterations agent + 1
        item@(Item t t' v) <- if runMode == Auto then generate (itemGenerator size) else generate (itemGenerator 1000)
        when (not test) $ do
            postGUISync $ do start1 <- textBufferGetStartIter b3
                             textBufferInsert b3 start1 $ show c ++ ": " ++ show item ++ "\n"
        let string = show (total+1) ++ ": " ++ normalizeOutput (show t ++ "=" ++ show t') ++ " : " ++ show v
        let (ltm,concepts,graph,_,_,_) = agentMemory agent
        -- test run: score before udpating the theory
        time <- getCurrentTime
        (_,_,_,resultBefore,_,_,_) <- findDelta True False time agent item
        -- actual run: score after updating the theory
        (newAgent,resultAfter,f',(computation,_)) <- runOnce test False agent item
        printConsole console $ "Item: " ++ show item ++ ": " ++ show resultAfter
        swapMVar currentAgentMvar newAgent
        let afterScore = boolToInt resultAfter
        let beforeScore = boolToInt resultBefore
        let newScore = ((beforeScore,afterScore) : score)
        putMVar scoreMvar newScore
        let size' = size + 1
        let changes' = [(if a >= 0 then "+ " else "    - ") ++ show lhs ++ show dir ++ show rhs
                            | (a,Axiom (_,_,_,_,_,(lhs,dir,rhs))) <- f']
        let changes'' = if null changes' then changes' else (show c) : changes'
        -- printConsole console $ show item
        postGUISync $ showIteration b4 scoreB scoreA c newScore item $ unlines changes''
        postGUISync $ showAgent b1 b2 closed open newAgent
        if runMode == Auto
        then do textBufferSetText answer ""
                runIterations runMode test size' itemGenerator 
                           (string : prev) (total+1) newAgent 
                           b1 b2 b3 b4 console answer scoreB scoreA closed open currentAgentMvar runState scoreMvar win
        else do
            postGUISync $ textBufferSetText answer $ showSolution computation
            return ()

showIteration buffer2 scoreB scoreA num scores item change = do
    let scoreAfter = sum . map snd $ take showScore scores
    let scoreBefor = sum . map fst $ take showScore scores
    let tot = min showScore (fromIntegral $ length scores)

    let newScoreB = show scoreBefor ++ "/" ++ show tot
    oldScoreB <- labelGetText scoreB
    when (oldScoreB /= newScoreB) $ labelSetText scoreB newScoreB

    let newScoreA = show scoreAfter ++ "/" ++ show tot
    oldScoreA <- labelGetText scoreA
    when (oldScoreA /= newScoreA) $ labelSetText scoreA newScoreA
    if (not . null) change
    then do
        start2 <- textBufferGetStartIter buffer2
        textBufferInsert buffer2 start2 change
    else return ()

initiateDialogOpen builder loadedAgentMvar currentAgentMvar = do
    dialogOpen <- builderGetObject builder castToWindow "filechooserDialog"
    textbuffer1 <- builderGetObject builder castToTextBuffer "textbuffer1"
    textbuffer2 <- builderGetObject builder castToTextBuffer "textbuffer2"
    textbuffer3 <- builderGetObject builder castToTextBuffer "textbuffer3"
    textbuffer4 <- builderGetObject builder castToTextBuffer "textbuffer4"
    console <- builderGetObject builder castToTextBuffer "textbufferConsole"
    closedAxioms <- builderGetObject builder castToLabel "closedAxioms"
    openAxioms <- builderGetObject builder castToLabel "openAxioms"
    labelStatus1 <- builderGetObject builder castToLabel "labelStatus1"
    labelStatus2 <- builderGetObject builder castToLabel "labelStatus2"
    scoreBefor <- builderGetObject builder castToLabel"labelScoreBefore"
    scoreAfter <- builderGetObject builder castToLabel"labelScoreAfter"
    let clearUI = do -- empty text buffers to clear textviews
            textBufferSetText textbuffer1 ""
            textBufferSetText textbuffer2 ""
            textBufferSetText textbuffer3 ""
            textBufferSetText textbuffer4 ""
            labelSetText scoreBefor ""
            labelSetText scoreAfter ""
            labelSetText closedAxioms ""
            labelSetText openAxioms ""
            labelSetText labelStatus1 ""
            labelSetText labelStatus2 ""
    dialogOpen `on` deleteEvent $ do
        liftIO (widgetHide dialogOpen)
        return True
    cancelButton <- builderGetObject builder castToButton "buttonOpenCancel"
    cancelButton `on` buttonActivated $ do
        widgetHide dialogOpen
        return ()
    okbutton     <- builderGetObject builder castToButton "buttonOpenOK"
    filechooser  <- builderGetObject builder castToFileChooser "filechooserDialog"
    okbutton `on` buttonActivated $ do
        file <- fileChooserGetFilename filechooser
        if isNothing file
        then do
            msgBox <- messageDialogNew (Just dialogOpen) [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsClose ("No filename chosen.")
            response <- dialogRun msgBox
            widgetHide msgBox
            return ()
        else do
        let filename = fromJust file
        let agentname = reverse . takeWhile (\x -> x/='\\' && x/='/') $ reverse filename
        agent' <- parseAgent filename
        if isLeft agent'
        then do
                msgBox <- messageDialogNew (Just dialogOpen) [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsClose (fromLeft agent')
                let button = msgBox
                dialogRun msgBox
                widgetHide msgBox
                return ()
        else do
        let (warnings,agent@(Agent comm (width,depth,axiom,_) (axioms,concepts,graph,pats,rew,_))) = fromRight agent'
        let status = "W:" ++ show width ++ " | D:" ++ show depth ++ " | L:" ++ show axiom
        printConsole console $ "Parsed agent successfully."
        mapM (printConsole console) warnings
        loaded <- tryTakeMVar loadedAgentMvar
        printConsole console $ "loaded = " ++ show (isJust loaded)
        current <- tryTakeMVar currentAgentMvar
        printConsole console $ "current = " ++ show (isJust current)
        if isNothing loaded
        then do putMVar loadedAgentMvar agent
                putMVar currentAgentMvar agent
                printConsole console $ "Loaded agent into loadedAgentMVar"
                clearUI
                labelSetText labelStatus1 agentname
                labelSetText labelStatus2 status
                widgetHide dialogOpen
                showAgent textbuffer1 textbuffer2 closedAxioms openAxioms agent
                return ()
        else if isNothing current
                then do putMVar loadedAgentMvar agent
                        putMVar currentAgentMvar agent
                        printConsole console $ "Loaded agent into currentAgentMVar"
                        clearUI
                        labelSetText labelStatus1 agentname
                        labelSetText labelStatus2 status
                        widgetHide dialogOpen
                        showAgent textbuffer1 textbuffer2 closedAxioms openAxioms agent
                        return ()
                else if loaded == current
                        then do
                            putMVar loadedAgentMvar agent
                            putMVar currentAgentMvar agent
                            -- takeMVar currentAgentMvar
                            clearUI
                            labelSetText labelStatus1 agentname
                            labelSetText labelStatus2 status
                            widgetHide dialogOpen
                            showAgent textbuffer1 textbuffer2 closedAxioms openAxioms agent
                            return ()
                        else do
                            widgetHide dialogOpen
                            msgBox <- messageDialogNew (Just dialogOpen) [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsClose ("Cannot open agent. An unsaved agent is currently loaded.")
                            dialogRun msgBox
                            widgetHide msgBox
                            return ()
showAgent buffer1 buffer2 closedAxioms openAxioms
          agent@(Agent comm (width,depth,axiom,_) (axioms,concepts,graph,pats,rew,rem)) = do
    let axs = filter (not . axIsFact) . Set.toList $ Set.union (ltmAxioms axioms) (ltmFacts axioms)
    let facts = filter axIsFact . Set.toList $ ltmFacts axioms
    let newText1 = unlines [show x ++ show d ++ show y | (Axiom (_,_,_,_,_,(x,d,y))) <- sort facts]
    let newText2 = unlines [show x ++ show d ++ show y | (Axiom (_,_,_,_,_,(x,d,y))) <- sort axs]
    start1 <- textBufferGetStartIter buffer1
    end1   <- textBufferGetEndIter buffer1
    oldText1 <- textBufferGetText buffer1 start1 end1 True
    start2 <- textBufferGetStartIter buffer2
    end2   <- textBufferGetEndIter buffer2
    oldText2 <- textBufferGetText buffer2 start2 end2 True
    when (newText1 /= oldText1) $ textBufferSetText buffer1 newText1
    when (newText2 /= oldText2) $ textBufferSetText buffer2 newText2
    oldClosed <- labelGetText closedAxioms
    oldOpen   <- labelGetText openAxioms
    let newClosed = show (length facts)
    let newOpen   = show (length axs)
    when (oldClosed /= newClosed) $ labelSetText closedAxioms newClosed
    when (oldOpen /= newOpen) $ labelSetText openAxioms newOpen    
    
initiateDialogNew builder loadedAgentMvar currentAgentMvar = do
    dialogNew <- builderGetObject builder castToWindow "dialogNew"
    dialogNew `on` deleteEvent $ do
        liftIO (widgetHide dialogNew)
        return True
    cancelButton <- builderGetObject builder castToButton "buttonNewCancel"
    cancelButton `on` buttonActivated $ do
        widgetHide dialogNew
        return ()
    okButton <- builderGetObject builder castToButton "buttonNewOK"
    entry1 <- builderGetObject builder castToEntry "entry1"
    entry2 <- builderGetObject builder castToEntry "entry2"
    entry3 <- builderGetObject builder castToEntry "entry3"
    entry4 <- builderGetObject builder castToEntry "entry4"
    okButton `on` buttonActivated $ do
            name'    <- entryGetText entry1 >>= return . strip
            wmsize'  <- entryGetText entry2 >>= return . strip
            clen'    <- entryGetText entry3 >>= return . strip
            ltmsize' <- entryGetText entry4 >>= return . strip
            widgetHide dialogNew
            if name' == ""
            then do
                msgBox <- messageDialogNew (Just dialogNew) [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsClose ("Agent name is empty.")
                dialogRun msgBox
                return ()
            else do
            let name = if take 6 (reverse name') == (reverse ".agent") then name' else name' ++ ".agent"
            if null wmsize' || any (not . isDigit) wmsize'
            then do
                msgBox <- messageDialogNew (Just dialogNew) [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsClose ("Working memory size should be a positive integer.")
                dialogRun msgBox
                return ()
            else do
            let wmsize = read wmsize' :: Int
            if null clen' || any (not . isDigit) clen'
            then do
                msgBox <- messageDialogNew (Just dialogNew) [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsClose ("Computation length should be a positive integer.")
                dialogRun msgBox
                return ()
            else do
            let clen = read clen' :: Int
            if null ltmsize' || any (not . isDigit) ltmsize'
            then do
                msgBox <- messageDialogNew (Just dialogNew) [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsClose ("Long term memory capacity should be a positive integer.")
                dialogRun msgBox
                return ()
            else do
            let ltmsize = read ltmsize' :: Int
            result <- createAgent name wmsize clen ltmsize
            if result
            then widgetHide dialogNew >> return ()
            else do
                msgBox <- messageDialogNew (Just dialogNew) [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsClose ("File " ++ name ++ " already exists. Choose a different name.")
                dialogRun msgBox
                return ()

-- quitProgram :: MVar Agent -> MVar Agent -> IO Bool
quitProgram loadedAgentMvar currentAgentMvar = do
    loaded <- tryTakeMVar loadedAgentMvar
    current <- tryTakeMVar currentAgentMvar
    if isNothing loaded
    then mainQuit >> return True
    else if isNothing current
          then do msgBox <- messageDialogNew Nothing [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsClose ("Training in process. Please stop the process before closing.")
                  reply <- dialogRun msgBox
                  if reply == ResponseClose
                  then widgetHide msgBox
                  else widgetHide msgBox
                  putMVar loadedAgentMvar (fromJust loaded)
                  putMVar currentAgentMvar (fromJust current)
                  return True
          else if loaded == current
               then mainQuit >> return True
               else do
                    msgBox <- messageDialogNew Nothing [DialogModal,DialogDestroyWithParent] MessageWarning ButtonsNone ("Do you want to save the agent before quitting?")
                    dialogAddButton msgBox "Cancel" ResponseCancel
                    dialogAddButton msgBox "No" ResponseNo
                    dialogAddButton msgBox "Yes" ResponseYes
                    reply <- dialogRun msgBox
                    case reply of
                      ResponseCancel -> do
                            putMVar loadedAgentMvar (fromJust loaded)
                            putMVar currentAgentMvar (fromJust current)
                            widgetHide msgBox
                            return True
                      ResponseNo  -> widgetHide msgBox >> mainQuit >> return True
                      ResponseYes -> do
                            putMVar loadedAgentMvar (fromJust loaded)
                            putMVar currentAgentMvar (fromJust current)
                            fileSave loadedAgentMvar currentAgentMvar
                            widgetHide msgBox
                            mainQuit
                            return True
                      _ -> do
                            putMVar loadedAgentMvar (fromJust loaded)
                            putMVar currentAgentMvar (fromJust current)
                            widgetHide msgBox
                            return True
                      

forkIO' x = forkIO x >> return ()

printConsole console str = postGUIAsync  $ do
    start   <- textBufferGetStartIter console
    textBufferInsert console start $ str ++ "\n"


