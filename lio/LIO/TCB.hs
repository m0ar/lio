{-# LANGUAGE Unsafe #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

{- | 

This module exports symbols that must be accessible only to trusted
code.  By convention, the names of such symbols always end
\"@...TCB@\" (short for \"trusted computing base\").  In many cases, a
type is safe to export while its constructor is not.  Hence, only the
constructor ends \"@TCB@\", while the type is re-exported to safe code
(without constructors) from "LIO.Core".

Security rests on the fact that untrusted code must be compiled with
@-XSafe@.  Because this module is flagged unsafe, it cannot be
imported from safe modules.

-}

module LIO.TCB (
  -- * LIO monad
    LIOState(..), LIO(..)
  -- ** Accessing internal state
  , getLIOStateTCB, putLIOStateTCB, modifyLIOStateTCB
  -- * Executing IO actions
  , ioTCB
  -- * Privileged constructors
  , Priv(..), Labeled(..), LabelOf(..)
  -- * Uncatchable exception type
  , UncatchableTCB(..), makeCatchable
  -- * Trusted 'Show'
  , ShowTCB(..)
  -- * 'LabeledResult's
  , LabeledResult(..), LResStatus(..)
  -- * MLabelPolicy
  , MLabelPolicy(..)
  ) where

import safe Control.Applicative ()
import safe Control.Exception (Exception(..), SomeException(..))
import safe qualified Control.Concurrent as IO
import safe Control.Monad
import safe Data.Monoid ()
import safe Data.IORef
import safe Data.Typeable
import safe LIO.Label
import LIO.Priv (Priv(..))
import LIO.TCB.MLabel (MLabel(..))

--
-- LIO Monad
--

-- | Internal state of an 'LIO' computation.
data LIOState l = LIOState { lioLabel     :: !l -- ^ Current label.
                           , lioClearance :: !l -- ^ Current clearance.
                           } deriving (Eq, Show, Read)

-- | The @LIO@ monad is a wrapper around 'IO' that keeps track of a
-- /current label/ and /current clearance/.  Safe code cannot execute
-- arbitrary 'IO' actions from the 'LIO' monad.  However, trusted
-- runtime functions can use 'ioTCB' to perform 'IO' actions (which
-- they should only do after appropriately checking labels).
data LIO l a where 
  -- * Label operations
  GetLabel                   :: LIO l l
  SetLabel                   :: l -> LIO l ()
  SetLabelP                  :: PrivDesc l p => Priv p -> l -> LIO l ()
  
  -- * Clearance operations
  GetClearance               :: LIO l l
  SetClearance               :: l -> LIO l ()
  SetClearanceP              :: PrivDesc l p => Priv p -> l -> LIO l ()
  ScopeClearance             :: LIO l a -> LIO l a
  WithClearance              :: l -> LIO l a -> LIO l a
  WithClearanceP             :: PrivDesc l p => Priv p -> l -> LIO l a -> LIO l a
  
  -- * Guard operations
  GuardAlloc                 :: l -> LIO l ()
  GuardAllocP                :: PrivDesc l p => Priv p -> l -> LIO l ()
  GuardWrite                 :: l -> LIO l ()
  GuardWriteP                :: PrivDesc l p => Priv p -> l -> LIO l ()
  
  -- * Taint operations
  Taint                      :: l -> LIO l ()
  TaintP                     :: PrivDesc l p => Priv p -> l -> LIO l ()
  
  -- * Monadic operations
  Return                     :: a -> LIO l a
  Bind                       :: LIO l a -> (a -> LIO l b) -> LIO l b
  Fail                       :: String -> LIO l a

  -- * State modifiers
  GetLIOStateTCB             :: LIO l (LIOState l)
  PutLIOStateTCB             :: LIOState l -> LIO l ()
  ModifyLIOStateTCB          :: (LIOState l -> LIOState l) -> LIO l ()

  -- * IO lifting
  IOTCB                      :: IO a -> LIO l a

  -- * Exception handling
  Catch                      :: (Label l, Exception e) => LIO l a -> (e -> LIO l a) -> LIO l a

  -- * Errors
  WithContext                :: String -> LIO l a -> LIO l a

  -- * Concurrency operators
  ForkLIO                    :: LIO l () -> LIO l ()
  LForkP                     :: PrivDesc l p => Priv p -> l -> LIO l a -> LIO l (LabeledResult l a)
  LWaitP                     :: PrivDesc l p => Priv p -> LabeledResult l a -> LIO l a
  TryLWaitP                  :: PrivDesc l p => Priv p -> LabeledResult l a -> LIO l (Maybe a)
  TimedLWaitP                :: PrivDesc l p => Priv p -> LabeledResult l a -> Int -> LIO l a

  -- * Label operations
  WithMLabelP                :: PrivDesc l p => Priv p -> MLabel policy l -> LIO l a -> LIO l a
  ModifyMLabelP              :: (PrivDesc l p, MLabelPolicy policy l) => Priv p -> MLabel policy l -> (l -> LIO l l) -> LIO l ()
  
  deriving (Typeable)

instance Monad (LIO l) where
  {-# INLINE return #-}
  return = Return
  {-# INLINE (>>=) #-}
  (>>=) = Bind
  fail = Fail

instance Functor (LIO l) where
  fmap f l =  l >>= (return . f)
-- fmap typically isn't inlined, so we don't inline our definition,
-- but we do define it in terms of >>= and return (which are inlined)

instance Applicative (LIO l) where
  {-# INLINE pure #-}
  pure = return
  {-# INLINE (<*>) #-}
  (<*>) = ap

--
-- Internal state
--

-- | Get internal state. This function is not actually unsafe, but
-- to avoid future security bugs we leave all direct access to the
-- internal state to trusted code.
getLIOStateTCB :: LIO l (LIOState l)
{-# INLINE getLIOStateTCB #-}
getLIOStateTCB = GetLIOStateTCB 

-- | Set internal state.
putLIOStateTCB :: LIOState l -> LIO l ()
{-# INLINE putLIOStateTCB #-}
putLIOStateTCB = PutLIOStateTCB 

-- | Update the internal state given some function.
modifyLIOStateTCB :: (LIOState l -> LIOState l) -> LIO l ()
{-# INLINE modifyLIOStateTCB #-}
modifyLIOStateTCB = ModifyLIOStateTCB

--
-- Executing IO actions
--

-- | Lifts an 'IO' computation into the 'LIO' monad.  This function is
-- dangerous and should only be called after appropriate checks ensure
-- the 'IO' computation will not violate IFC policy.
ioTCB :: IO a -> LIO l a
{-# INLINE ioTCB #-}
ioTCB = IOTCB 

--
-- Exception handling
--

-- | An uncatchable exception hierarchy is used to terminate an
-- untrusted thread.  Wrap the uncatchable exception in
-- 'UncatchableTCB' before throwing it to the thread.  'runLIO' will
-- subsequently unwrap the 'UncatchableTCB' constructor.
--
-- Note this can be circumvented by 'IO.mapException', which should be
-- made unsafe. In the interim, auditing untrusted code for this is
-- necessary.
data UncatchableTCB = forall e. (Exception e) =>
                      UncatchableTCB e deriving (Typeable)

instance Show UncatchableTCB where
  showsPrec p (UncatchableTCB e) = showsPrec p e

instance Exception UncatchableTCB where
  toException = SomeException
  fromException (SomeException e) = cast e

-- | Simple utility function that strips 'UncatchableTCB' from around an
-- exception.
makeCatchable :: SomeException -> SomeException
makeCatchable e@(SomeException einner) =
  case cast einner of Just (UncatchableTCB enew) -> SomeException enew
                      Nothing                    -> e

--
-- Pure labeled values
--

-- | @Labeled l a@ is a value that associates a label of type @l@ with
-- a pure value of type @a@. Labeled values allow users to label data
-- with a label other than the current label.  Note that 'Labeled' is
-- an instance of 'LabelOf', which means that only the /contents/ of a
-- labeled value (the type @t@) is kept secret, not the label.  Of
-- course, if you have a @Labeled@ within a @Labeled@, then the label
-- on the inner value will be protected by the outer label.
data Labeled l t = LabeledTCB !l t deriving Typeable
-- Note: t cannot be strict if we want things like lFmap.

-- | Trusted 'Show' instance.
instance (Show l, Show a) => ShowTCB (Labeled l a) where
    showTCB (LabeledTCB l a) = show a ++ " {" ++ show l ++ "}"

-- | Generic class used to get the type of labeled objects. For,
-- instance, if you wish to associate a label with a pure value (as in
-- "LIO.Labeled"), you may create a data type:
-- 
-- > data LVal l a = LValTCB l a
-- 
-- Then, you may wish to allow untrusted code to read the label of any
-- @LVal@s but not necessarily the actual value. To do so, simply
-- provide an instance for @LabelOf@:
-- 
-- > instance LabelOf LVal where
-- >   labelOf (LValTCB l a) = l
class LabelOf t where
  -- | Get the label of a labeled value or object.  Note the label
  -- must be the second to last type constructor argument.
  labelOf :: t l a -> l

instance LabelOf Labeled where
  {-# INLINE labelOf #-}
  labelOf (LabeledTCB l _) = l

--
-- Trusted 'Show'
--

-- | It would be a security issue to make certain objects members of
-- the 'Show' class.  Nonetheless it is useful to be able to examine
-- such objects when debugging.  The 'showTCB' method can be used to
-- examine such objects.
class ShowTCB a where
  showTCB :: a -> String


--
-- LabeledResult
--

-- | Status of a 'LabeledResult'.
data LResStatus l a = LResEmpty
                    | LResLabelTooHigh !l
                    | LResResult a
                      deriving (Show)

-- | A @LabeledResult@ encapsulates a future result from a computation
-- spawned by 'lFork' or 'lForkP'.  See "LIO.Concurrent" for a
-- description of the concurrency abstractions of LIO.
data LabeledResult l a = LabeledResultTCB {
    lresThreadIdTCB :: !IO.ThreadId
    -- ^ Thread executing the computation
  , lresLabelTCB :: !l
    -- ^ Label of the tresult
  , lresBlockTCB :: !(IO.MVar ())
    -- ^ This 'MVar' is empty until such point as 'lresStatusTCB' is
    -- no longer 'LResEmpty'.  Hence, calling 'readMVar' on this field
    -- allows one to wait for the thread to terminate.
  , lresStatusTCB :: !(IORef (LResStatus l a))
    -- ^ Result (when it is ready), or the label at which the thread
    -- terminated, if that label could not flow to 'lresLabelTCB'.
  }

instance LabelOf LabeledResult where
  labelOf = lresLabelTCB

-- | Class of policies for when it is permissible to update an
-- 'MLabel'.
class MLabelPolicy policy l where
  mlabelPolicy :: (PrivDesc l p) => policy -> p -> l -> l -> LIO l ()
