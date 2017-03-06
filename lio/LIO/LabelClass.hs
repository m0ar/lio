{-# LANGUAGE Safe #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}


module LIO.LabelClass (
  -- * Labels
  -- $Labels
    Label(..)
  ) where

import safe Data.Monoid ()
import safe Data.Typeable
-- This file is probably temporary

{- $Labels

Labels are a way of describing who can observe and modify data.
Labels are governed by a partial order, generally pronounced \"can
flow to.\"  In LIO, we write this relation ``canFlowTo``.  In the
literature, it is usually written &#8849;.

At a high level, the purpose of this whole library is to ensure that
data labeled @l1@ may affect data labeled @l2@ only if @l1
``canFlowTo`` l2@.  The 'LIO' monad (see "LIO.Core") ensures this by
keeping track of a /current label/ of the executing thread (accessible
via the 'getLabel' function).  Code may attempt to perform various IO
or memory operations on labeled data.  Touching data may change the
current label and will throw an exception in the event that an
operation would violate information flow restrictions.

The specific invariant maintained by 'LIO' is, first, that labels on
all previously observed data must flow to a thread's current label.
Second, the current label must flow to the labels of any future
objects the thread will be allowed to modify.  Hence, after a thread
with current label @lcur@ observes data labeled @l1@, it must hold
that @l1 ``canFlowTo`` lcur@.  If the thread is later permitted to
modify an object labeled @l2@, it must hold that @lcur ``canFlowTo``
l2@.  By transitivity of the ``canFlowTo`` relation, it holds that @l1
``canFlowTo`` l2@.

-}

-- | This class defines the operations necessary to make a label into
-- a lattice (see <http://en.wikipedia.org/wiki/Lattice_(order)>).
-- 'canFlowTo' partially orders labels.
-- 'lub' and 'glb' compute the least upper bound and greatest lower
-- bound of two labels, respectively.
class (Eq l, Show l, Read l, Typeable l) => Label l where
  -- | Compute the /least upper bound/, or join, of two labels.  When
  -- data carrying two different labels is mixed together in a
  -- document, the @lub@ of the two labels is the lowest safe value
  -- with which to label the result.
  --
  -- More formally, for any two labels @l1@ and @l2@, if @ljoin = l1
  -- \`lub` l2@, it must be that:
  --
  -- * @L_1 ``canFlowTo`` ljoin@,
  --
  -- * @L_2 ``canFlowTo`` ljoin@, and
  --
  -- * There is no label @l /= ljoin@ such that @l1 ``canFlowTo`` l@,
  --   @l2 ``canFlowTo`` l@, and @l ``canFlowTo`` ljoin@.  In other
  --   words @ljoin@ is the least element to which both @l1@ and @l2@
  --   can flow.
  --
  -- When used infix, has fixity:
  --
  -- > infixl 5 `lub`
  lub :: l -> l -> l

  -- | /Greatest lower bound/, or meet, of two labels. For any two
  -- labels @l1@ and @l2@, if @lmeet = l1 \`glb` l2@, it must be
  -- that:
  --
  -- * @lmeet ``canFlowTo`` l1@,
  --
  -- * @lmeet ``canFlowTo`` l2@, and
  --
  -- * There is no label @l /= lmeet@ such that @l ``canFlowTo`` l1@,
  --   @l ``canFlowTo`` l2@, and @lmeet ``canFlowTo`` l@.  In other
  --   words @lmeet@ is the greatest element flowing to both @l1@ and
  --   @l2@.
  --
  -- When used infix, has fixity:
  --
  -- > infixl 5 `glb`
  glb :: l -> l -> l

  -- | /Can-flow-to/ relation (&#8849;). An entity labeled @l1@ should
  -- be allowed to affect an entity @l2@ only if @l1 \`canFlowTo`
  -- l2@. This relation on labels is at least a partial order (see
  -- <https://en.wikipedia.org/wiki/Partially_ordered_set>), and must
  -- satisfy the following laws:
  --
  -- * Reflexivity: @l1 \`canFlowTo` l1@ for any @l1@.
  --
  -- * Antisymmetry: If @l1 \`canFlowTo` l2@ and
  --   @l2 \`canFlowTo` l1@ then @l1 = l2@.
  --
  -- * Transitivity: If @l1 \`canFlowTo` l2@ and
  --   @l2 \`canFlowTo` l3@ then @l1 \`canFlowTo` l3@.
  --
  -- When used infix, has fixity:
  --
  -- > infix 4 `canFlowTo`
  canFlowTo :: l -> l -> Bool


infixl 5 `lub`, `glb`
infix 4 `canFlowTo`