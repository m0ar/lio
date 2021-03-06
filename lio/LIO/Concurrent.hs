{-# LANGUAGE Trustworthy #-}
{- |

This module provides concurrency abstractions for 'LIO'.  The most
basic function, 'forkLIO', spawns a computation in a new light-weight
thread (analogous to 'forkIO').

'lFork' spawns a forked thread that returns a result other threads can
wait for (using 'lWait').  The label of such a thread's result must be
specified at the time the thread is spawned with 'lFork'.  Should the
'lFork'ed thread terminate with its current label be above the
specified result label, 'lWait' will throw an exception of type
'ResultExceedsLabel' in any thread waiting for the result.

Learing that a spawned thread has terminated by catching a
'ResultExceedsLabel' may cause the label of the waiting thread to
rise, possibly above the current clearance (in which case the
exception cannot be caught).  As an alternative, 'timedlWait'
unconditionally kills a spawned thread if it has not terminated at an
observable label within a certain time period.  'timedlWait' is
guaranteed both to terminate and not to throw exceptions that cannot
be caught at the current label.

-}
module LIO.Concurrent (
  -- * Forking simple threads
    forkLIO
  -- * Forking threads that return results
  , LabeledResult
  , lFork, lForkP
  -- * Waiting on threads
  , ResultExceedsLabel(..)
  , lWait, lWaitP
  , trylWait, trylWaitP
  , timedlWait, timedlWaitP
  -- * Labeled MVars
  , module LIO.Concurrent.LMVar
  ) where

import safe LIO.Concurrent.LMVar
import safe LIO.Core
import safe LIO.Error
import safe LIO.Label
import LIO.TCB


--
-- Fork
--

-- | Execute an 'LIO' computation in a new lightweight thread.
forkLIO :: LIO l () -> LIO l ()
forkLIO = ForkLIO

-- | Labeled fork. @lFork@ allows one to invoke computations that
-- would otherwise raise the current label, but without actually
-- raising the label. The computation is executed in a separate thread
-- and writes its result into a labeled result (whose label is
-- supplied). To observe the result of the computation, or if the
-- computation has terminated, one will have to call 'lWait' and
-- raise the current label. Of couse,  this can be postponed until the
-- result is needed.
--
-- @lFork@ takes a label, which corresponds to the label of the
-- result.  It is required that this label be between the current
-- label and clearance as enforced by a call to 'guardAlloc'.
-- Moreover, the supplied computation must not terminate with its
-- label above the result label; doing so will result in an exception
-- being thrown in the thread reading the result.
-- 
-- Note that @lFork@ immediately returns a 'LabeledResult', which is
-- essentially a \"future\", or \"promise\". This prevents
-- timing/termination attacks in which the duration of the forked
-- computation affects the duration of the @lFork@.
-- 
-- To guarantee that the computation has completed, it is important that
-- some thread actually touch the future, i.e., perform an 'lWait'.
lFork :: Label l
      => l                -- ^ Label of result
      -> LIO l a          -- ^ Computation to execute in separate thread
      -> LIO l (LabeledResult l a) -- ^ Labeled result
lFork = lForkP noPrivs

-- | Same as 'lFork', but the supplied set of priviliges are accounted
-- for when performing label comparisons.
lForkP :: PrivDesc l p =>
          Priv p -> l -> LIO l a -> LIO l (LabeledResult l a)
lForkP = LForkP


--
-- Wait
--

-- | Given a 'LabeledResult' (a future), @lWait@ returns the unwrapped
-- result (blocks, if necessary). For @lWait@ to succeed, the label of
-- the result must be above the current label and below the current
-- clearance. Moreover, before block-reading, @lWait@ raises the current
-- label to the join of the current label and label of result.  An
-- exception is thrown by the underlying 'taint' if this is not the
-- case.  Additionally, if the thread terminates with an exception (for
-- example if it violates clearance), the exception is rethrown by
-- @lWait@. Similarly, if the thread reads values above the result label,
-- an exception is thrown in place of the result.
lWait :: Label l => LabeledResult l a -> LIO l a
lWait = lWaitP noPrivs

-- | Same as 'lWait', but uses priviliges in label checks and raises.
lWaitP :: PrivDesc l p => Priv p -> LabeledResult l a -> LIO l a
lWaitP = LWaitP


-- | Same as 'lWait', but does not block waiting for result.
trylWait :: Label l => LabeledResult l a -> LIO l (Maybe a)
trylWait = trylWaitP noPrivs

-- | Same as 'trylWait', but uses priviliges in label checks and raises.
trylWaitP :: PrivDesc l p => Priv p -> LabeledResult l a -> LIO l (Maybe a)
trylWaitP = TryLWaitP 


-- | Like 'lWait', with two differences.  First, a timeout is
-- specified and the thread is unconditionally killed after this
-- timeout (if it has not yet returned a value).  Second, if the
-- thread's result exceeds what the calling thread can observe,
-- @timedlWait@ consumes the whole timeout and throws a
-- 'ResultExceedsLabel' exception you can catch (i.e., it never raises
-- the label above the clearance).
--
-- Because this function can alter the result by killing a thread, it
-- requires the label of the 'LabeledResult' to be both readable and
-- writable at the current label.
timedlWait :: Label l => LabeledResult l a -> Int -> LIO l a
timedlWait = timedlWaitP noPrivs

-- | A version of 'timedlWait' that takes privileges.  The privileges
-- are used both to downgrade the result (if necessary), and to try
-- catching any 'ResultExceedsLabel' before the timeout period (if
-- possible).
timedlWaitP :: PrivDesc l p => Priv p -> LabeledResult l a -> Int -> LIO l a
timedlWaitP = TimedLWaitP

