{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE GADTs #-}

-- | This module contains functions to launch 'LIO' computations from
-- within the 'IO' monad.  These functions are not useful from within
-- 'LIO' code (but not harmful either, since their types are in the
-- 'IO' monad).
--
-- This module is intended to be imported into your Main module, for
-- use in invoking 'LIO' code.  The functions are also available via
-- "LIO" and "LIO.Core", but those modules will clutter your namespace
-- with symbols you don't need in the 'IO' monad.
module LIO.RunCPS (LIOState(..), runLIO, tryLIO, evalLIO, privInit) where

import safe Control.Exception
import safe qualified Control.Concurrent as IO
import safe qualified Control.Exception as IO
import safe Data.IORef
import safe Data.Unique
import safe Control.Monad
import safe qualified Data.Map as Map
import safe Control.Monad.Cont

import safe LIO.Label
import safe LIO.Error
import safe Data.Typeable
import safe LIO.Exception (throwLIO)
import LIO.TCB.MLabel (MLabel(..))
import LIO.TCB

-- | Execute an 'LIO' action, returning its result and the final label
-- state as a pair.  Note that it returns a pair whether or not the
-- 'LIO' action throws an exception.  Forcing the result value will
-- re-throw the exception, but the label state will always be valid.
--
-- See also 'evalLIO'.
runLIO :: Label l => LIO l a -> LIOState l -> IO (a, LIOState l)
runLIO lio s0 = do
  sp <- newIORef s0
  a <- runContT (runLIO' sp lio) return
  s1 <- readIORef sp
  return (a, s1)

runLIO' :: Label l => IORef (LIOState l) -> LIO l a -> ContT a IO a
runLIO' ioRef lio = case lio of
    -- * Label operations
    GetLabel      -> runLIO' ioRef $ lioLabel `liftM` getLIOStateTCB
    SetLabel l    -> runLIO' ioRef $
      WithContext "setLabel" $ do
        GuardAlloc l
        ModifyLIOStateTCB $ \s -> s { lioLabel = l }

    SetLabelP p l  -> runLIO' ioRef $
      WithContext "setLabelP" $ do
        GuardAllocP p l
        ModifyLIOStateTCB $ \s -> s { lioLabel = l }

    -- * Clearance operations
    GetClearance   -> runLIO' ioRef $ lioClearance `liftM` getLIOStateTCB

    SetClearance cnew -> runLIO' ioRef $ do
      LIOState { lioLabel = l, lioClearance = c } <- getLIOStateTCB
      unless (canFlowTo l cnew && canFlowTo cnew c) $
        labelError "setClearance" [cnew]
      PutLIOStateTCB $ LIOState l cnew

    SetClearanceP p cnew -> runLIO' ioRef $ do
      LIOState l c <- getLIOStateTCB
      unless (canFlowTo l cnew && canFlowToP p cnew c) $
        labelErrorP "setClearanceP" p [cnew]
      putLIOStateTCB $ LIOState l cnew

    ScopeClearance action -> do
      LIOState _ c <- liftIO $ readIORef ioRef
      ea <- liftIO $ IO.try $ runLIO' ioRef action
      LIOState l _ <- liftIO $ readIORef ioRef
      liftIO $ writeIORef ioRef (LIOState l c)
      if l `canFlowTo` c
        then either (IO.throwIO :: SomeException -> IO a) return ea
        else IO.throwIO LabelError { lerrContext = []
                                  , lerrFailure = "scopeClearance"
                                  , lerrCurLabel = l
                                  , lerrCurClearance = c
                                  , lerrPrivs = []
                                  , lerrLabels = [] }

    WithClearance c lio' -> runLIO' ioRef $
      ScopeClearance $ SetClearance c >> lio'

    WithClearanceP p c lio' -> runLIO' ioRef $
      ScopeClearance $ SetClearanceP p c >> lio'

    -- * Guard operations
    GuardAlloc newl -> runLIO' ioRef $ do
      LIOState { lioLabel = l, lioClearance = c } <- getLIOStateTCB
      unless (canFlowTo l newl && canFlowTo newl c) $
        labelError "guardAllocP" [newl]

    GuardAllocP p newl -> runLIO' ioRef $ do
      LIOState { lioLabel = l, lioClearance = c } <- getLIOStateTCB
      unless (canFlowToP p l newl && canFlowTo newl c) $
        labelErrorP "guardAllocP" p [newl]

    GuardWrite newl -> runLIO' ioRef $
      WithContext "guardWrite" $ do
        GuardAlloc newl
        Taint newl

    GuardWriteP p newl-> runLIO' ioRef $
      withContext "guardWriteP" $ do
        GuardAllocP p newl
        TaintP p newl

    -- * Taint operations
    Taint newl -> runLIO' ioRef $ do
      LIOState { lioLabel = l, lioClearance = c } <- getLIOStateTCB
      let l' = l `lub` newl
      unless (l' `canFlowTo` c) $ labelError "taint" [newl]
      ModifyLIOStateTCB $ \s -> s { lioLabel = l' }

    TaintP p newl -> runLIO' ioRef $ do
      LIOState { lioLabel = l, lioClearance = c } <- getLIOStateTCB
      let l' = l `lub` downgradeP p newl
      unless (l' `canFlowTo` c) $ labelErrorP "taintP" p [newl]
      modifyLIOStateTCB $ \s -> s { lioLabel = l' }

    -- * Monadic operations
    Return a -> return a
    Bind ma k -> do
      a <- runLIO' ioRef ma
      runLIO' ioRef $ k a
    Fail s -> fail s

    -- * State modifiers
    GetLIOStateTCB -> readIORef ioRef
    PutLIOStateTCB s -> writeIORef ioRef s
    ModifyLIOStateTCB f -> do
      s <- readIORef ioRef
      writeIORef ioRef (f s)

    -- * IO Lifting
    IOTCB a -> a

    -- * Exception handling
    Catch lio' h -> do
      let io = runLIO' ioRef lio'
      io `IO.catch` \e -> runLIO' ioRef (safeh e)
      where
        uncatchableType = typeOf (undefined :: UncatchableTCB)
        safeh e@(SomeException einner) = do
          when (typeOf einner == uncatchableType) $ throwLIO e
          LIOState l c <- getLIOStateTCB
          unless (l `canFlowTo` c) $ throwLIO e
          maybe (throwLIO e) h $ fromException e

    -- * Error contexts
    WithContext ctx lio' ->
      runLIO' ioRef lio' `IO.catch` \e ->
      IO.throwIO $ annotate ctx (e :: AnyLabelError)

    -- * Concurrency operations
    ForkLIO lio' -> runLIO' ioRef $ do
      s <- getLIOStateTCB
      ioTCB $ void $ IO.forkIO $ do
        ((), _) <- runLIO lio' s
        return ()

    LForkP p l action -> runLIO' ioRef $ do
      withContext "lForkP" $ GuardAllocP p l
      mv <- ioTCB IO.newEmptyMVar
      st <- ioTCB $ newIORef LResEmpty
      s0 <- getLIOStateTCB
      tid <- ioTCB $ IO.mask $ \unmask -> IO.forkIO $ do
        sp <- newIORef s0
        ea <- IO.try $ unmask $ runLIO' sp action
        LIOState lEnd _ <- readIORef sp
        writeIORef st $ case ea of
          _ | not (lEnd `canFlowTo` l) -> LResLabelTooHigh lEnd
          Left e                       -> LResResult $ IO.throw $ makeCatchable e
          Right a                      -> LResResult a
        IO.putMVar mv ()
      return $ LabeledResultTCB tid l mv st

    LWaitP p (LabeledResultTCB _ l mv st) -> runLIO' ioRef $
      withContext "lWaitP" (TaintP p l) >> go
      where go = ioTCB (readIORef st) >>= check
            check LResEmpty = ioTCB (IO.readMVar mv) >> go
            check (LResResult a) = return $! a
            check (LResLabelTooHigh lnew) = do
              modifyLIOStateTCB $ \s -> s {
                lioLabel = downgradeP p lnew `lub` lioLabel s }
              throwLIO ResultExceedsLabel {
                  relContext = []
                , relLocation = "lWaitP"
                , relDeclaredLabel = l
                , relActualLabel = Just lnew }

    TryLWaitP p (LabeledResultTCB _ rl _ st) -> runLIO' ioRef $
      withContext "trylWaitP" (TaintP p rl) >> ioTCB (readIORef st) >>= check
      where check LResEmpty = return Nothing
            check (LResResult a) = return . Just $! a
            check (LResLabelTooHigh lnew) = do
              curl <- GetLabel
              if canFlowToP p lnew curl
                then throwLIO ResultExceedsLabel {
                        relContext = []
                      , relLocation = "trylWaitP"
                      , relDeclaredLabel = rl
                      , relActualLabel = Just lnew }
                else return Nothing

    TimedLWaitP p lr@(LabeledResultTCB t rl mvb _) to -> runLIO' ioRef $
      withContext "timedlWaitP" (do GuardWriteP p rl
                                    TryLWaitP p lr >>= go)
      where go (Just a) = return a
            go Nothing = do
              mvk <- ioTCB IO.newEmptyMVar
              tk <- ioTCB $ IO.forkIO $ IO.finally (IO.threadDelay to) $ do
                IO.putMVar mvk ()
                IO.throwTo t (UncatchableTCB IO.ThreadKilled)
              ioTCB $ IO.readMVar mvb
              TryLWaitP p lr >>= maybe
                (ioTCB (IO.takeMVar mvk) >> throwLIO failure)
                (\a -> ioTCB (IO.killThread tk) >> return a)
            failure = ResultExceedsLabel { relContext = []
                                        , relLocation = "timedWaitP"
                                        , relDeclaredLabel = rl
                                        , relActualLabel = Nothing }

    -- * Label operations
    WithMLabelP p (MLabelTCB ll r mv _) action -> do
      runLIO' ioRef (TaintP p ll) 
      tid <- IO.myThreadId
      u <- newUnique
      let check lnew = do
            LIOState { lioLabel = lcur, lioClearance = ccur } <- readIORef ioRef
            if canFlowToP p lcur lnew && canFlowToP p lnew lcur
              then return True
              else do IO.throwTo tid LabelError {
                          lerrContext = []
                        , lerrFailure = "withMLabelP label changed"
                        , lerrCurLabel = lcur
                        , lerrCurClearance = ccur
                        , lerrPrivs = [GenericPrivDesc $ privDesc p]
                        , lerrLabels = [lnew]
                        }
                      return False
          enter = IO.modifyMVar_ mv $ \m -> do
            void $ readIORef r >>= check
            return $ Map.insert u check m
          exit = IO.modifyMVar_ mv $ return . Map.delete u
      IO.bracket_ enter exit $ runLIO' ioRef action 

    ModifyMLabelP p (MLabelTCB ll r mv pl) fn -> runLIO' ioRef $ 
      withContext "modifyMLabelP" $ do
        GuardWriteP p ll
        ioTCB $ IO.modifyMVar_ mv $ \m -> do
          lold <- readIORef r
          lnew <- runLIO' ioRef $ fn lold
          () <- runLIO' ioRef $ mlabelPolicy pl p lold lnew
          writeIORef r lnew
          Map.fromList `fmap` filterM (($ lnew) . snd) (Map.assocs m) 


-- | A variant of 'runLIO' that returns results in 'Right' and
-- exceptions in 'Left', much like the standard library 'try'
-- function.
tryLIO :: Label l => LIO l a -> LIOState l -> IO (Either SomeException a, LIOState l)
tryLIO lio s0 = runLIO lio s0 >>= tryit
  where tryit (a, s) = do
          ea <- try (evaluate a)
          return (ea, s)


-- | Given an 'LIO' computation and some initial state, return an IO
-- action which, when executed, will perform the IFC-safe LIO
-- computation.
--
-- Because untrusted code cannot execute 'IO' computations, this function
-- should only be useful within trusted code.  No harm is done from
-- exposing the @evalLIO@ symbol to untrusted code.  (In general,
-- untrusted code is free to produce 'IO' computations, but it cannot
-- execute them.)
--
-- Unlike 'runLIO', this function throws an exception if the
-- underlying 'LIO' action terminates with an exception.
evalLIO :: Label l => LIO l a -> LIOState l -> IO a
evalLIO lio s = do
  (a, _) <- runLIO lio s
  return $! a

-- | Initialize some privileges (within the 'IO' monad) that can be
-- passed to 'LIO' computations run with 'runLIO' or 'evalLIO'.  This
-- is a pure function, but the result is encapsulated in 'IO' to
-- make the return value inaccessible from 'LIO' computations.
--
-- Note the same effect can be achieved using the 'PrivTCB'
-- constructor, but 'PrivTCB' is easier to misuse and is only available by
-- importing "LIO.TCB".
privInit :: (SpeaksFor p) => p -> IO (Priv p)
privInit p | isPriv p  = fail "privInit called on Priv object"
           | otherwise = return $ PrivTCB p
