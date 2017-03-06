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
module LIO.Run (LIOState(..), runLIO, tryLIO, evalLIO, privInit) where

import safe Control.Exception
import safe qualified Control.Exception as IO
import safe Data.IORef
import safe Control.Monad

import safe LIO.Label
import LIO.TCB
import safe LIO.Error
import safe Data.Typeable
import safe LIO.Exception (throwLIO)

-- | Execute an 'LIO' action, returning its result and the final label
-- state as a pair.  Note that it returns a pair whether or not the
-- 'LIO' action throws an exception.  Forcing the result value will
-- re-throw the exception, but the label state will always be valid.
--
-- See also 'evalLIO'.
runLIO :: Label l => LIO l a -> LIOState l -> IO (a, LIOState l)
runLIO lio s0 = do
  sp <- newIORef s0
  a  <- runLIO' sp lio `IO.catch` \e -> return $ throw $ makeCatchable e
  s1 <- readIORef sp
  return (a, s1)
  
runLIO' :: Label l => IORef (LIOState l) -> LIO l a -> IO a  
runLIO' ioRef lio =  case lio of
    GetLabel      -> runLIO' ioRef $ lioLabel `liftM` getLIOStateTCB
    SetLabel l    -> runLIO' ioRef $
      WithContext "setLabel" $ do
        GuardAlloc l
        ModifyLIOStateTCB $ \s -> s { lioLabel = l }
    SetLabelP p l  -> runLIO' ioRef $
      WithContext "setLabelP" $ do
        GuardAllocP p l
        ModifyLIOStateTCB $ \s -> s { lioLabel = l }
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
      LIOState _ c <- readIORef ioRef
      ea <- IO.try $ runLIO' ioRef action
      LIOState l _ <- readIORef ioRef
      writeIORef ioRef (LIOState l c)
      if l `canFlowTo` c
        then either (IO.throwIO :: SomeException -> IO a) return ea
        else IO.throwIO LabelError { lerrContext = []
                                  , lerrFailure = "scopeClearance"
                                  , lerrCurLabel = l
                                  , lerrCurClearance = c
                                  , lerrPrivs = []
                                  , lerrLabels = [] }
    WithClearance c lio -> runLIO' ioRef $
      ScopeClearance $ SetClearance c >> lio
    WithClearanceP p c lio -> runLIO' ioRef $
      ScopeClearance $ SetClearanceP p c >> lio
    GuardAlloc newl -> runLIO' ioRef $ do
      LIOState { lioLabel = l, lioClearance = c } <- getLIOStateTCB
      unless (canFlowTo l newl && canFlowTo newl c) $
        labelError "guardAllocP" [newl]
    GuardAllocP p newl -> runLIO' ioRef $ do
      LIOState { lioLabel = l, lioClearance = c } <- getLIOStateTCB
      unless (canFlowToP p l newl && canFlowTo newl c) $
        labelErrorP "guardAllocP" p [newl]
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
    GuardWrite newl -> runLIO' ioRef $
      WithContext "guardWrite" $ do
        GuardAlloc newl
        Taint newl
    GuardWriteP p newl-> runLIO' ioRef $
      withContext "guardWriteP" $ do
        GuardAllocP p newl
        TaintP p newl
    Return a -> return a
    Bind _ _ -> undefined
    Fail s -> fail s
    GetLIOStateTCB -> readIORef ioRef
    PutLIOStateTCB s -> writeIORef ioRef s
    ModifyLIOStateTCB f -> do
      s <- readIORef ioRef
      writeIORef ioRef (f s)
    IOTCB a -> a
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
    WithContext ctx lio ->
      runLIO' ioRef lio `IO.catch` \e ->
      IO.throwIO $ annotate ctx (e :: AnyLabelError)
    ForkLIO _ -> undefined
    LForkP _ _ _ -> undefined
    LWaitP _ _ -> undefined
    TryLWaitP _ _ -> undefined
    TimedLWaitP _ _ _ -> undefined
    WithMLabelP _ _ _ -> undefined
    ModifyMLabelP _ _ _ -> undefined


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
