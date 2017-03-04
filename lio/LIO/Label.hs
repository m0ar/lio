{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}


module LIO.Label (
  -- * Labels
  -- $Labels
    Label(..)
  -- * Privileges
  -- $Privileges
  , SpeaksFor(..), PrivDesc(..)
  , Priv, privDesc
  -- ** Internal functions
  , isPriv
  -- * Empty privileges
  , NoPrivs(..), noPrivs
  ) where

import safe Data.Monoid ()
import safe Data.Typeable

import LIO.TCB
import LIO.LabelClass

{- $Privileges 

Privileges are objects the possesion of which allows code to bypass
certain label protections.  An instance of class 'PrivDesc' describes
a pre-order (see <http://en.wikipedia.org/wiki/Preorder>) among labels
in which certain unequal labels become equivalent.  A 'Priv' object
containing a 'PrivDesc' instance allows code to make those unequal
labels equivalent for the purposes of many library functions.
Effectively, a 'PrivDesc' instance /describes/ privileges, while a
'Priv' object /embodies/ them.

Any code is free to construct 'PrivDesc' values describing arbitrarily
powerful privileges.  Security is enforced by preventing safe code
from accessing the constructor for 'Priv' (called 'PrivTCB').  Safe
code can construct arbitrary privileges from the 'IO' monad (using
'privInit' in "LIO.Run#v:privInit"), but cannot do so from the 'LIO'
monad.  Starting from existing privileges, safe code can also
'delegate' lesser privileges (see "LIO.Delegate#v:delegate").

Privileges allow you to behave as if @l1 ``canFlowTo`` l2@ even when
that is not the case, but only for certain pairs of labels @l1@ and
@l2@; which pairs depends on the specific privileges.  The process of
allowing data labeled @l1@ to infulence data labeled @l2@ when @(l1
``canFlowTo`` l2) == False@ is known as /downgrading/.

The core privilege function is 'canFlowToP', which performs a more
permissive can-flow-to check by exercising particular privileges (in
the literature this relation is commonly written @&#8849;&#8346;@ for
privileges @p@).  Most core 'LIO' functions have variants ending @...P@
that take a privilege argument to act in a more permissive way.

By convention, all 'PrivDesc' instances should also be instances of
'Monoid', allowing privileges to be combined with 'mappend', though
there is no superclass to enforce this.

-}


-- | Turns privileges into a powerless description of the privileges
-- by unwrapping the 'Priv' newtype.
privDesc :: Priv a -> a
{-# INLINE privDesc #-}
privDesc (PrivTCB a) = a

-- | Uses dynamic typing to return 'True' iff the type of the argument
-- is @'Priv' a@ (for any @a@).  Mostly useful to prevent users from
-- accidentally wrapping 'Priv' objects inside other 'Priv' objects or
-- accidentally including real privileges in an exception.
isPriv :: (Typeable p) => p -> Bool
isPriv p = typeRepTyCon (typeOf p) == privcon
  where privcon = typeRepTyCon $ typeOf noPrivs

-- | Every privilege type must be an instance of 'SpeaksFor', which is
-- a partial order specifying when one privilege value is at least as
-- powerful as another.  If @'canFlowToP' p1 l1 l2@ and @p2
-- `speaksFor` p1@, then it should also be true that @'canFlowToP' p2
-- l1 l2@.
--
-- As a partial order, 'SpeaksFor' should obey the reflexivity,
-- antisymmetry and transitivity laws.  However, if you do not wish to
-- allow delegation of a particular privilege type, you can define
-- @'speaksFor' _ _ = False@ (which violates the reflexivity law, but
-- is reasonable when you don't want the partial order).
class (Typeable p, Show p) => SpeaksFor p where
  -- | @speaksFor p1 p2@ returns 'True' iff @p1@ subsumes all the
  -- privileges of @p2@.  In other words, it is safe for 'delegate' to
  -- hand out @p2@ to a caller who already has @p1@.
  --
  -- Has fixity:
  --
  -- > infix 4 `speaksFor`
  speaksFor :: p -> p -> Bool

infix 4 `speaksFor`

-- | This class represents privilege descriptions, which define a
-- pre-order on labels in which distinct labels become equivalent.
-- The pre-oder implied by a privilege description is specified by the
-- method 'canFlowToP'.  In addition, this this class defines a method
-- 'downgradeP', which is important for finding least labels
-- satisfying a privilege equivalence.
--
-- Minimal complete definition: 'downgradeP'.
--
-- (The 'downgradeP' requirement represents the fact that a generic
-- 'canFlowToP' can be implemented efficiently in terms of
-- 'downgradeP', but not vice-versa.)
class (Label l, SpeaksFor p) => PrivDesc l p where
-- Note: SpeaksFor is a superclass for security reasons.  Were it not
-- a superclass, then if a label format ever failed to define
-- SpeaksFor, or defined it in a different module from the PrivDesc
-- instance, then an attacker could produce an vacuous instance that
-- allows all delegation.

    -- | Privileges are described in terms of a pre-order on labels in
    -- which sets of distinct labels become equivalent.  @downgradeP p
    -- l@ returns the lowest of all labels equivalent to @l@ under
    -- privilege description @p@.
    --
    -- Less formally, @downgradeP p l@ returns a label representing
    -- the furthest you can downgrade data labeled @l@ given
    -- privileges described by @p@.
    downgradeP :: p     -- ^ Privilege description
                  -> l  -- ^ Label to downgrade
                  -> l  -- ^ Lowest label equivelent to input

    -- | @canFlowToP p l1 l2@ determines whether @p@ describes
    -- sufficient privileges to observe data labeled @l1@ and
    -- subsequently write it to an object labeled @l2@.  The function
    -- returns 'True' if and only if either @canFlowTo l1 l2@ or @l1
    -- and l2@ are equivalent under @p@.
    --
    -- The default definition is:
    --
    -- > canFlowToP p l1 l2 = downgradeP p l1 `canFlowTo` l2
    -- 
    -- @canFlowToP@ is a method rather than a function so that it can
    -- be optimized in label-specific ways.  However, custom
    -- definitions should behave identically to the default.
    canFlowToP :: p -> l -> l -> Bool
    canFlowToP p l1 l2 = downgradeP p l1 `canFlowTo` l2

instance (SpeaksFor p) => SpeaksFor (Priv p) where
  {-# INLINE speaksFor #-}
  speaksFor p1 p2 = privDesc p1 `speaksFor` privDesc p2

instance (PrivDesc l p) => PrivDesc l (Priv p) where
  {-# INLINE downgradeP #-}
  downgradeP = downgradeP . privDesc
  {-# INLINE canFlowToP #-}
  canFlowToP = canFlowToP . privDesc

--
-- NoPrivs
--

-- | Generic 'PrivDesc' used to denote the lack of privileges.  Works
-- with any 'Label' type.  This is only a privilege description; a
-- more useful symbol is 'noPrivs', which actually embodies the
-- @NoPrivs@ privilege.
data NoPrivs = NoPrivs deriving (Show, Read, Typeable)

instance SpeaksFor NoPrivs where speaksFor _ _ = True

-- | 'downgradeP' 'NoPrivs' is the identify function.  Hence
-- 'canFlowToP' 'NoPrivs' is the same as 'canFlowTo'.
instance Label l => PrivDesc l NoPrivs where downgradeP _ l = l

instance Monoid NoPrivs where
  mempty      = NoPrivs
  mappend _ _ = NoPrivs

-- | 'Priv' object corresponding to 'NoPrivs'.
noPrivs :: Priv NoPrivs
noPrivs = PrivTCB NoPrivs

