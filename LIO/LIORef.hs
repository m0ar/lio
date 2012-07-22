{-# LANGUAGE Trustworthy #-}

-- |This module exports the safe subset of the "LIO.LIORef.TCB" module.
-- It is important that untrusted code be limited to this subset; information
-- flow can easily be violated if the TCB functions are exported.
module LIO.LIORef (
    LIORef
  -- * Basic Functions
  -- ** Create labeled 'IORef's
  , newLIORef, newLIORefP
  -- ** Read 'LIORef's
  , readLIORef, readLIORefP
  -- ** Write 'LIORef's
  , writeLIORef, writeLIORefP
  -- ** Modify 'LIORef's
  , modifyLIORef, modifyLIORefP
  , atomicModifyLIORef, atomicModifyLIORefP
  ) where

import LIO
import LIO.LIORef.TCB

--
-- Create labeled 'IORef's
--

-- | To create a new reference the label of the reference must be
-- below the thread's current clearance and above the current label.
-- If this is the case, the reference is built.
newLIORef :: Label l
          => l                  -- ^ Label of reference
          -> a                  -- ^ Initial value
          -> LIO l (LIORef l a) -- ^ Mutable reference
newLIORef = newLIORefP NoPrivs

-- | Same as 'newLIORef' except @newLIORefP@ takes a set of
-- privileges which are accounted for in comparing the label of
-- the reference to the current label and clearance.
newLIORefP :: Priv l p => p -> l -> a -> LIO l (LIORef l a)
newLIORefP p l a = do
  guardAllocP p l
  newLIORefTCB l a

--
-- Read 'LIORef's
--

-- | Read the value of a labeled refernce. A read succeeds only if the
-- label of the reference is below the current clearance. Moreover,
-- the current label is raised to the join of the current label and
-- the reference label. To avoid failures use 'labelOfLIORef' to check
-- that a read will suceed.
readLIORef :: Label l => LIORef l a -> LIO l a
readLIORef = readLIORefP NoPrivs

-- | Same as 'readLIORef' except @readLIORefP@ takes a privilege object
-- which is used when the current label is raised.
readLIORefP :: Priv l p => p -> LIORef l a -> LIO l a
readLIORefP p lr = do
  taintP p $! labelOf lr
  readLIORefTCB lr

--
-- Write 'LIORef's
--

-- | Write a new value into a labeled reference. A write succeeds if
-- the current label can-flow-to the label of the reference, and the
-- label of the reference can-flow-to the current clearance.
writeLIORef :: Priv l p => LIORef l a -> a -> LIO l ()
writeLIORef = writeLIORefP NoPrivs

-- | Same as 'writeLIORef' except @writeLIORefP@ takes a set of
-- privileges which are accounted for in comparing the label of
-- the reference to the current label and clearance.
writeLIORefP :: Priv l p => p -> LIORef l a -> a -> LIO l ()
writeLIORefP p lr a = do
  guardAllocP p $! labelOf lr 
  writeLIORefTCB lr a

--
-- Modify 'LIORef's
--

-- | Mutate the contents of a labeled reference. For the mutation to
-- succeed it must be that the current label can-flow-to the label of
-- the reference, and the label of the reference can-flow-to the
-- current clearance. Note that because a modifer is provided, the
-- reference contents are not observable by the outer computation and
-- so it is not required that the current label be raised.
modifyLIORef :: Label l
             =>  LIORef l a            -- ^ Labeled reference
             -> (a -> a)               -- ^ Modifier
             -> LIO l ()
modifyLIORef = modifyLIORefP NoPrivs

-- | Same as 'modifyLIORef' except @modifyLIORefP@ takes a set of
-- privileges which are accounted for in comparing the label of
-- the reference to the current label and clearance.
modifyLIORefP :: Priv l p =>  p -> LIORef l a -> (a -> a) -> LIO l ()
modifyLIORefP p lr f = do
  guardAllocP p $! labelOf lr 
  modifyLIORefTCB lr f

-- | Atomically modifies the contents of an 'LIORef'. It is required
-- that the label of the reference be above the current label, but
-- below the current clearance. 
atomicModifyLIORef :: Label l => LIORef l a -> (a -> (a, b)) -> LIO l b
atomicModifyLIORef = atomicModifyLIORefP NoPrivs

-- | Same as 'atomicModifyLIORef' except @atomicModifyLIORefP@ takes
-- a set of privileges which are accounted for in label comparisons.
atomicModifyLIORefP :: Priv l p => p -> LIORef l a -> (a -> (a, b)) -> LIO l b
atomicModifyLIORefP p lr f = do
  guardAllocP p $! labelOf lr 
  atomicModifyLIORefTCB lr f
