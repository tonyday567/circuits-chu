{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The Chu construction over a monoidal base category.
--
-- A Chu object is a polarity pair @A⁺@ and @A⁻@ together with a pairing
-- @A⁺ ⊗ A⁻ → ⊥@ into a dualising object.  A Chu morphism is an adjoint pair
-- satisfying the equation
--
-- > e_B (f⁺ a, d) = e_A (a, f⁻ d)
--
-- This is the only genuinely star-autonomous, non-compact structure in the
-- library: proper ⊗ vs ⅋, proper additives, a real negation, and an internal
-- hom that is not just @A⊥ ⊗ B@.  Promoting it to a base arrow makes the
-- linear-logic distinctions measurable for the first time.
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Circuit.Chu
  ( -- * Dualising semiring
    ChuSemiring (..),

    -- * Chu objects and morphisms
    ChuObj (..),
    PointedChuObj (..),
    ChuMorphism (..),
    Chu (..),
    ChuPosType,
    ChuNegType,

    negateChu,
    idChu,
    composeChu,

    -- * Adjoint law
    chuLaw,
    chuLawAt,

    -- * Delivery pairing
    deliversToSemiring,
    deliveryMatrix,

    -- * Tensor and par over Set
    ChuTensorNeg (..),
    ChuParPos (..),
    tensorChuObj,
    parChuObj,
    lolliChuObj,
    withChuObj,
    oplusChuObj,
    topChuObj,
    zeroChuObj,
    proj1Chu,
    proj2Chu,
    inj1Chu,
    inj2Chu,
    unitTopChu,
    unitZeroChu,
    pairChu,
    copairChu,
    withTopLChu,
    withTopLInvChu,
    withTopRChu,
    withTopRInvChu,
    zeroPlusLChu,
    zeroPlusLInvChu,
    zeroPlusRChu,
    zeroPlusRInvChu,
    evalChu,
    tensorChu,
    parChu,
    chuUnitObj,
    chuBottomObj,
    chuTensorNegs,
    chuParPoss,
    chuSeparated,
    chuExtensional,
    leftUnitorChu,
    leftUnitorChuInv,
    rightUnitorChu,
    rightUnitorChuInv,
    assocChu,
    assocChuInv,
    slideChu,

    -- * Embedding from 'Circuit.Ends'
    endsAsChu,
    lawfulDimapEnds,

    -- * Object-indexed Chu category (SepChu / OChu)
    ChuObject (..),
    ChuSeparated,
    ChuExtensional,
    ChuPosNonEmpty,
    ChuNegNonEmpty,
    OChu (..),
    SepChu,

    -- * OChu constrained combinators (evidence at use sites)
    parOChu,
    unitlOChu,
    unitlOChu',
    unitrOChu,
    unitrOChu',
    swapOChu,
    parPOChu,
    unitlPOChu,
    unitlPOChu',
    unitrPOChu,
    unitrPOChu',
    evalOChu,
    curryOChu,
    uncurryOChu,
    discardEOChu,
    derelictOChu,
    introduceOChu,
    mergeEOChu,
    zeroEOChu,
    copyTOChu,
    discardTOChu,
    plusTOChu,
    zeroTOChu,

    ChuOUnit (..),
    ChuOTensor (..),
    ChuONeg (..),
    ChuOWith (..),
    ChuOPlus (..),
    ChuOPar (..),
    ChuOTop (..),
    ChuOZero (..),
    ChuTwo (..),
    ChuThree (..),
    ChuDouble01 (..),
    ChuDelivery (..),
    ChuAny (..),
    swapChu,
    dnUnitChu,
    dnCounitChu,
    ChuOLolli (..),
    curryChu,
    uncurryChu,
    chuFunctionals,
    bangChuObj,
    whyNotChuObj,
    copyBangChu,
    discardBangChu,
    mergeBangChu,
    zeroBangChu,
    derelictChu,
    zeroWhyNotChu,
    introduceChu,
    digChu,
    promoteChu,
    mergeWhyNotParChu,
    zeroWhyNotParChu,
    leftUnitorParChu,
    leftUnitorParChuInv,
    rightUnitorParChu,
    rightUnitorParChuInv,
    assocParChu,
    assocParChuInv,
    swapParChu,
    ChuOBang (..),
    ChuOWhyNot (..),
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..))
import Circuit.Dagger (CopyT (..), DiscardT (..), MergeT (..), ZeroT (..))
import Circuit.Ends (Ends (..), In (..), Out (..), close, companion, conjoint)
import Circuit.Tensor (Action (..), BangCopy (..), BangWeaken (..), Bot, Exponential (..), Lolli (..), Par (..), Tensor (..), Unit, WhyNotIntro (..), WhyNotMonoid (..))
import Data.Kind (Type)
import Data.Monoid (Any (..))
import Data.Proxy (Proxy (..))
import Data.Type.Bool (If)
import Data.Traversable (sequenceA)
import Data.Void (Void, absurd)
import Prelude hiding (curry, id, uncurry, (.))
import qualified Prelude as Pre

-- ---------------------------------------------------------------------------
-- Minimal semiring
-- ---------------------------------------------------------------------------

-- | A semiring, kept local to this module so the delivery instance does not
-- pull in an external numeric prelude.
class ChuSemiring r where
  sZero :: r
  sOne :: r
  sPlus :: r -> r -> r
  sTimes :: r -> r -> r

instance ChuSemiring Bool where
  sZero = False
  sOne = True
  sPlus = (||)
  sTimes = (&&)

instance ChuSemiring Double where
  sZero = 0
  sOne = 1
  sPlus = (+)
  sTimes = (*)

instance ChuSemiring Integer where
  sZero = 0
  sOne = 1
  sPlus = (+)
  sTimes = (*)

-- ---------------------------------------------------------------------------
-- Chu objects
-- ---------------------------------------------------------------------------

-- | An object of @Chu(C, ⊥)@.
--
-- * @a@ is the positive carrier.
-- * @b@ is the negative carrier.
-- * @chuPair@ is the pairing @a ⊗ b → r@ into the dualising object.
newtype ChuObj t r arr a b = ChuObj
  { -- | Pairing into the dualising object.
    chuPair :: arr (t a b) r
  }

-- | A pointed Chu object: a 'ChuObj' together with a chosen point pair.
--
-- This is the separate wrapper used by 'endsAsChu' to retain the positive
-- and negative points that witness a self-dual channel.
data PointedChuObj t r arr a b = PointedChuObj
  { -- | Underlying Chu object.
    pointedObj :: ChuObj t r arr a b,
    -- | Positive point.
    pointedPos :: a,
    -- | Negative point.
    pointedNeg :: b
  }

-- | Negation swaps the carriers via the symmetric braiding.
--
-- Involution is definitional for a symmetric braiding:
-- @swap . swap = id@.
negateChu ::
  (Action t arr) =>
  ChuObj t r arr a b ->
  ChuObj t r arr b a
negateChu (ChuObj e) = ChuObj (e . swap)
{-# INLINE negateChu #-}

-- ---------------------------------------------------------------------------
-- Chu morphisms
-- ---------------------------------------------------------------------------

-- | A Chu morphism @A → B@ is a pair of base arrows:
--
-- * @chuForward :: arr a c@ runs forward from @A⁺@ to @B⁺@.
-- * @chuBackward :: arr d b@ runs backward from @B⁻@ to @A⁻@.
data ChuMorphism t r arr a b c d = ChuMorphism
  { -- | Forward component.
    chuForward :: arr a c,
    -- | Backward component.
    chuBackward :: arr d b
  }

-- | Identity Chu morphism.
idChu ::
  (Category arr) =>
  ChuMorphism t r arr a b a b
idChu = ChuMorphism id id
{-# INLINE idChu #-}

-- | Sequential composition of Chu morphisms.
--
-- Forward components compose covariantly; backward components compose
-- contravariantly.
composeChu ::
  (Category arr) =>
  ChuMorphism t r arr c d e f ->
  ChuMorphism t r arr a b c d ->
  ChuMorphism t r arr a b e f
composeChu (ChuMorphism f2 g2) (ChuMorphism f1 g1) =
  ChuMorphism (f2 . f1) (g1 . g2)

-- ---------------------------------------------------------------------------
-- Chu as a base arrow
-- ---------------------------------------------------------------------------

-- | Closed type family giving the positive carrier of a Chu object tag.
--
-- Every object of @Chu(C, ⊥)@ is ultimately a 'ChuObj'; this family exposes
-- the positive carrier so that identity and composition can be typed
-- uniformly without a separate type class.
type family ChuPosType a :: Type where
  ChuPosType (ChuObj t r arr p n) = p
  ChuPosType (ChuOUnit r) = ()
  ChuPosType (ChuOTensor r a b) = (ChuPosType a, ChuPosType b)
  ChuPosType (ChuONeg r a) = ChuNegType a
  ChuPosType ChuTwo = Bool
  ChuPosType ChuThree = Maybe Bool
  ChuPosType ChuDouble01 = Bool
  ChuPosType ChuDelivery = Bool
  ChuPosType ChuAny = Any
  ChuPosType (ChuOLolli r a b) = ChuParPos (ChuNegType a) (ChuPosType a) (ChuPosType b) (ChuNegType b)
  ChuPosType (ChuOWith r a b) = (ChuPosType a, ChuPosType b)
  ChuPosType (ChuOPlus r a b) = Either (ChuPosType a) (ChuPosType b)
  ChuPosType (ChuOPar r a b) = ChuParPos (ChuPosType a) (ChuNegType a) (ChuPosType b) (ChuNegType b)
  ChuPosType (ChuOTop r) = ()
  ChuPosType (ChuOZero r) = Void
  ChuPosType (ChuOBang r a) = ChuPosType a
  ChuPosType (ChuOWhyNot r a) = ChuNegType a -> r

-- | Closed type family giving the negative carrier of a Chu object tag.
--
-- See 'ChuPosType' for motivation; this is the dual side.
type family ChuNegType a :: Type where
  ChuNegType (ChuObj t r arr p n) = n
  ChuNegType (ChuOUnit r) = r
  ChuNegType (ChuOTensor r a b) = ChuTensorNeg (ChuPosType a) (ChuNegType a) (ChuPosType b) (ChuNegType b)
  ChuNegType (ChuONeg r a) = ChuPosType a
  ChuNegType ChuTwo = Bool
  ChuNegType ChuThree = Maybe Bool
  ChuNegType ChuDouble01 = Bool
  ChuNegType ChuDelivery = Bool
  ChuNegType ChuAny = Any
  ChuNegType (ChuOLolli r a b) = (ChuPosType a, ChuNegType b)
  ChuNegType (ChuOWith r a b) = Either (ChuNegType a) (ChuNegType b)
  ChuNegType (ChuOPlus r a b) = (ChuNegType a, ChuNegType b)
  ChuNegType (ChuOPar r a b) = (ChuNegType a, ChuNegType b)
  ChuNegType (ChuOTop r) = Void
  ChuNegType (ChuOZero r) = ()
  ChuNegType (ChuOBang r a) = ChuPosType a -> r
  ChuNegType (ChuOWhyNot r a) = ChuNegType a

-- | @Chu t r arr@ is the Chu construction as a base arrow.  Objects are
-- 'ChuObj's; morphisms are adjoint pairs wrapped by the 'Chu' constructor.
newtype Chu (t :: Type -> Type -> Type) (r :: Type) (arr :: Type -> Type -> Type) (a :: Type) (b :: Type) where
  Chu ::
    ChuMorphism t r arr (ChuPosType a) (ChuNegType a) (ChuPosType b) (ChuNegType b) ->
    Chu t r arr a b

instance (Category arr) => Category (Chu t r arr) where
  id :: forall a. Chu t r arr a a
  id = Chu (idChu :: ChuMorphism t r arr (ChuPosType a) (ChuNegType a) (ChuPosType a) (ChuNegType a))

  (.) ::
    forall a b c.
    Chu t r arr b c ->
    Chu t r arr a b ->
    Chu t r arr a c
  Chu g . Chu f = Chu (composeChu g f)

-- | The adjoint law for @arr = (->)@ and the cartesian tensor.
--
-- A pair @(f⁺, f⁻)@ is a Chu morphism exactly when
-- @e_B (f⁺ a, d) = e_A (a, f⁻ d)@ for all @a@ and @d@.
chuLaw ::
  (Eq r) =>
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuMorphism (,) r (->) a b c d ->
  a ->
  d ->
  Bool
chuLaw src tgt (ChuMorphism f g) a d =
  chuPair tgt (f a, d) == chuPair src (a, g d)
{-# INLINE chuLaw #-}

-- | Pointwise adjoint law for @arr = (->)@.
--
-- When the dualising object @r@ does not have an 'Eq' instance (e.g. it is
-- itself a function), supply a probe @k :: r -> s@ with 'Eq' @s@.
chuLawAt ::
  (Eq s) =>
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuMorphism (,) r (->) a b c d ->
  a ->
  d ->
  (r -> s) ->
  Bool
chuLawAt src tgt (ChuMorphism f g) a d k =
  k (chuPair tgt (f a, d)) == k (chuPair src (a, g d))
{-# INLINE chuLawAt #-}

-- ---------------------------------------------------------------------------
-- Delivery pairing
-- ---------------------------------------------------------------------------

-- | Named-recipient delivery predicate over an arbitrary semiring.
--
-- A post whose recipient list contains @who@ delivers with 'sOne';
-- an empty list delivers to no one with 'sZero'.
deliversToSemiring ::
  (ChuSemiring r, Eq a) =>
  -- | Recipients on the post.
  [a] ->
  -- | Recipient name.
  a ->
  r
deliversToSemiring recipients who
  | null recipients = sZero
  | who `elem` recipients = sOne
  | otherwise = sZero

-- | Delivery matrix for a fixed list of posts and a roster of agents.
--
-- Rows are posts (in the order given), columns are agents (in the order
-- given), and entry @(p, a)@ is the delivery weight of post @p@ to agent @a@.
deliveryMatrix ::
  (ChuSemiring r, Eq col) =>
  -- | Agents (column labels).
  [col] ->
  -- | Recipient lists for each post (row labels are implicit).
  [[col]] ->
  [[r]]
deliveryMatrix agents recipients =
  [map (deliversToSemiring recips) agents | recips <- recipients]

-- ===========================================================================
-- Tensor and par structure over Set (arr = (->), t = (,))
-- ===========================================================================
--
-- The Chu construction Chu(Set, K) is *-autonomous on the full subcategory of
-- separated extensional objects.  The operations below are defined for
-- arbitrary Chu objects, but the unit laws hold only when the objects are
-- separated and extensional.  See Barr, "The separated extensional Chu
-- category" (TAC 1998).

-- | Negative part of the Chu tensor @A ⊗ B@.
--
-- A value @(f, g)@ lives here when @e_A(a, g(b)) = e_B(b, f(a))@ for all
-- @a ∈ A⁺@, @b ∈ B⁺@.
data ChuTensorNeg a b c d = ChuTensorNeg
  { -- | @A⁺ -> B⁻@
    ctnForward :: a -> d,
    -- | @B⁺ -> A⁻@
    ctnBackward :: c -> b
  }

-- | Positive part of the Chu par @A ⅋ B@.
--
-- A value @(f, g)@ lives here when @e_A(g(d), a) = e_B(f(a), d)@ for all
-- @a ∈ A⁻@, @d ∈ B⁻@.
data ChuParPos a b c d = ChuParPos
  { -- | @A⁻ -> C⁺@
    cppForward :: b -> c,
    -- | @D⁻ -> A⁺@
    cppBackward :: d -> a
  }

-- | Tensor product of Chu objects over @Set@.
tensorChuObj ::
  (Eq r) =>
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuObj (,) r (->) (a, c) (ChuTensorNeg a b c d)
tensorChuObj (ChuObj r) (ChuObj s) =
  ChuObj $
    \((x, y), ChuTensorNeg f g) ->
      let lhs = r (x, g y)
          rhs = s (y, f x)
       in if lhs == rhs then lhs else error "tensorChuObj: ChuTensorNeg violates bilinear law"

-- | Par product of Chu objects over @Set@.
parChuObj ::
  (Eq r) =>
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuObj (,) r (->) (ChuParPos a b c d) (b, d)
parChuObj (ChuObj r) (ChuObj s) =
  ChuObj $
    \(ChuParPos f g, (x, y)) ->
      let lhs = r (g y, x)
          rhs = s (f x, y)
       in if lhs == rhs then lhs else error "parChuObj: ChuParPos violates bilinear law"

-- | Linear implication @A ⊸ B = A⊥ ⅋ B@ over @Set@.
--
-- The positive carrier is the set of Chu morphisms @A → B@, packaged as
-- 'ChuParPos' after negating @A@.
lolliChuObj ::
  (Eq r) =>
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuObj (,) r (->) (ChuParPos b a c d) (a, d)
lolliChuObj a b = parChuObj (negateChu a) b

-- | Additive conjunction @A & B@ over @Set@.
--
-- Positive carrier is @A⁺ × B⁺@; negative carrier is the disjoint union
-- @A⁻ + B⁻@.
withChuObj ::
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuObj (,) r (->) (a, c) (Either b d)
withChuObj (ChuObj eA) (ChuObj eB) =
  ChuObj $
    \((x, y), q) -> case q of
      Left b -> eA (x, b)
      Right d -> eB (y, d)

-- | Additive disjunction @A ⊕ B@ over @Set@.
--
-- Positive carrier is the disjoint union @A⁺ + B⁺@; negative carrier is
-- @A⁻ × B⁻@.
oplusChuObj ::
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuObj (,) r (->) (Either a c) (b, d)
oplusChuObj (ChuObj eA) (ChuObj eB) =
  ChuObj $
    \(q, (x, y)) -> case q of
      Left a -> eA (a, x)
      Right c -> eB (c, y)

-- | Additive unit @⊤@ over @Set@.
--
-- Positive carrier is the terminal object @1@; negative carrier is the
-- initial object @0@.
topChuObj :: ChuObj (,) r (->) () Void
topChuObj = ChuObj (\((), v) -> absurd v)

-- | Additive unit @0@ over @Set@.
--
-- Positive carrier is the initial object @0@; negative carrier is the
-- terminal object @1@.
zeroChuObj :: ChuObj (,) r (->) Void ()
zeroChuObj = ChuObj (\(v, ()) -> absurd v)

-- | First projection @A & B → A@.
proj1Chu ::
  ChuMorphism (,) r (->) (a, c) (Either b d) a b
proj1Chu = ChuMorphism fst Left
{-# INLINE proj1Chu #-}

-- | Second projection @A & B → B@.
proj2Chu ::
  ChuMorphism (,) r (->) (a, c) (Either b d) c d
proj2Chu = ChuMorphism snd Right
{-# INLINE proj2Chu #-}

-- | Left injection @A → A ⊕ B@.
inj1Chu ::
  ChuMorphism (,) r (->) a b (Either a c) (b, d)
inj1Chu = ChuMorphism Left fst
{-# INLINE inj1Chu #-}

-- | Right injection @A → A ⊕ B@.
inj2Chu ::
  ChuMorphism (,) r (->) c d (Either a c) (b, d)
inj2Chu = ChuMorphism Right snd
{-# INLINE inj2Chu #-}

-- | Unique morphism @A → ⊤@.
unitTopChu ::
  ChuMorphism (,) r (->) a b () Void
unitTopChu = ChuMorphism (const ()) absurd
{-# INLINE unitTopChu #-}

-- | Unique morphism @0 → A@.
unitZeroChu ::
  ChuMorphism (,) r (->) Void () a b
unitZeroChu = ChuMorphism absurd (const ())
{-# INLINE unitZeroChu #-}

-- | Pairing of morphisms into the additive conjunction.
--
-- Universal property of @A & B@: given @f : C → A@ and @g : C → B@, produce
-- @⟨f,g⟩ : C → A & B@.
pairChu ::
  ChuMorphism (,) r (->) c d a b ->
  ChuMorphism (,) r (->) c d e f ->
  ChuMorphism (,) r (->) c d (a, e) (Either b f)
pairChu (ChuMorphism fPos fNeg) (ChuMorphism gPos gNeg) =
  ChuMorphism (\c -> (fPos c, gPos c)) (either fNeg gNeg)
{-# INLINE pairChu #-}

-- | Copairing of morphisms out of the additive disjunction.
--
-- Universal property of @A ⊕ B@: given @f : A → C@ and @g : B → C@, produce
-- @[f,g] : A ⊕ B → C@.
copairChu ::
  ChuMorphism (,) r (->) a b c d ->
  ChuMorphism (,) r (->) e f c d ->
  ChuMorphism (,) r (->) (Either a e) (b, f) c d
copairChu (ChuMorphism fPos fNeg) (ChuMorphism gPos gNeg) =
  ChuMorphism (either fPos gPos) (\d -> (fNeg d, gNeg d))
{-# INLINE copairChu #-}

-- | Right unit isomorphism @A → A & ⊤@.
withTopRChu ::
  ChuMorphism (,) r (->) a b (a, ()) (Either b Void)
withTopRChu = ChuMorphism (\a -> (a, ())) (either id absurd)
{-# INLINE withTopRChu #-}

-- | Inverse of 'withTopRChu'.
withTopRInvChu ::
  ChuMorphism (,) r (->) (a, ()) (Either b Void) a b
withTopRInvChu = ChuMorphism fst Left
{-# INLINE withTopRInvChu #-}

-- | Left unit isomorphism @A → ⊤ & A@.
withTopLChu ::
  ChuMorphism (,) r (->) a b ((), a) (Either Void b)
withTopLChu = ChuMorphism (\a -> ((), a)) (either absurd id)
{-# INLINE withTopLChu #-}

-- | Inverse of 'withTopLChu'.
withTopLInvChu ::
  ChuMorphism (,) r (->) ((), a) (Either Void b) a b
withTopLInvChu = ChuMorphism snd Right
{-# INLINE withTopLInvChu #-}

-- | Left unit isomorphism @A → 0 ⊕ A@.
zeroPlusLChu ::
  ChuMorphism (,) r (->) a b (Either Void a) ((), b)
zeroPlusLChu = ChuMorphism Right (\(_, n) -> n)
{-# INLINE zeroPlusLChu #-}

-- | Inverse of 'zeroPlusLChu'.
zeroPlusLInvChu ::
  ChuMorphism (,) r (->) (Either Void a) ((), b) a b
zeroPlusLInvChu = ChuMorphism (either absurd id) (\n -> ((), n))
{-# INLINE zeroPlusLInvChu #-}

-- | Right unit isomorphism @A → A ⊕ 0@.
zeroPlusRChu ::
  ChuMorphism (,) r (->) a b (Either a Void) (b, ())
zeroPlusRChu = ChuMorphism Left (\(n, _) -> n)
{-# INLINE zeroPlusRChu #-}

-- | Inverse of 'zeroPlusRChu'.
zeroPlusRInvChu ::
  ChuMorphism (,) r (->) (Either a Void) (b, ()) a b
zeroPlusRInvChu = ChuMorphism (either id absurd) (\n -> (n, ()))
{-# INLINE zeroPlusRInvChu #-}

-- | Evaluation counit @A ⊗ (A ⊸ B) → B@ over @Set@.
--
-- Forward applies the Chu morphism stored in the implication object.
-- Backward pairs the argument with its own positive point, recovering the
-- adjoint condition.
evalChu ::
  ChuObj (,) r (->) a b ->
  ChuObj (,) r (->) c d ->
  ChuMorphism (,) r (->) (a, ChuParPos b a c d) (ChuTensorNeg a b (ChuParPos b a c d) (a, d)) c d
evalChu _ _ =
  ChuMorphism
    (\(x, m) -> cppForward m x)
    (\d -> ChuTensorNeg (\x -> (x, d)) (\m -> cppBackward m d))

-- | Tensor of two Chu morphisms.
tensorChu ::
  ChuMorphism (,) r (->) a b c d ->
  ChuMorphism (,) r (->) e f g h ->
  ChuMorphism (,) r (->) (a, e) (ChuTensorNeg a b e f) (c, g) (ChuTensorNeg c d g h)
tensorChu (ChuMorphism fPos fNeg) (ChuMorphism gPos gNeg) =
  ChuMorphism
    (\(x, y) -> (fPos x, gPos y))
    (\(ChuTensorNeg h k) -> ChuTensorNeg (gNeg . h . fPos) (fNeg . k . gPos))

-- | Par of two Chu morphisms.
parChu ::
  ChuMorphism (,) r (->) a b c d ->
  ChuMorphism (,) r (->) e f g h ->
  ChuMorphism (,) r (->) (ChuParPos a b e f) (b, f) (ChuParPos c d g h) (d, h)
parChu (ChuMorphism fPos fNeg) (ChuMorphism gPos gNeg) =
  ChuMorphism
    (\(ChuParPos h k) -> ChuParPos (gPos . h . fNeg) (fPos . k . gNeg))
    (\(x, y) -> (fNeg x, gNeg y))

-- | Unit object @I = (1, K)@ with pairing @snd@.
chuUnitObj :: ChuObj (,) r (->) () r
chuUnitObj = ChuObj snd

-- | Bottom object @⊥ = (K, 1)@, dual of the unit.
chuBottomObj :: ChuObj (,) r (->) r ()
chuBottomObj = ChuObj (\(k, ()) -> k)

-- | Left unitor @λ_A : I ⊗ A → A@ over @Set@.
--
-- Forward drops the unit; backward maps a negative point @b@ to the unique
-- Chu tensor negative with @f() = b@ and @g a = e(a, b)@.
leftUnitorChu ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) ((), a) (ChuTensorNeg () r a b) a b
leftUnitorChu (ChuObj e) =
  ChuMorphism snd (\b -> ChuTensorNeg (const b) (\a -> e (a, b)))

-- | Inverse of the left unitor.
leftUnitorChuInv ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) a b ((), a) (ChuTensorNeg () r a b)
leftUnitorChuInv _ = ChuMorphism ((),) (\(ChuTensorNeg f _) -> f ())

-- | Right unitor @ρ_A : A ⊗ I → A@ over @Set@.
rightUnitorChu ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) (a, ()) (ChuTensorNeg a b () r) a b
rightUnitorChu (ChuObj e) =
  ChuMorphism fst (\b -> ChuTensorNeg (\a -> e (a, b)) (const b))

-- | Inverse of the right unitor.
rightUnitorChuInv ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) a b (a, ()) (ChuTensorNeg a b () r)
rightUnitorChuInv _ = ChuMorphism (\a -> (a, ())) (\(ChuTensorNeg _ g) -> g ())

-- | Associator @(A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)@ over @Set@.
--
-- Positives reassociate as pairs.  Negatives reassociate the adjoint
-- pairs: a negative of @A ⊗ (B ⊗ C)@ is sent to a negative of
-- @(A ⊗ B) ⊗ C@ by unpacking the inner 'ChuTensorNeg'.
assocChu ::
  ChuMorphism
    (,)
    r
    (->)
    ((a, c), e)
    (ChuTensorNeg (a, c) (ChuTensorNeg a b c d) e f)
    (a, (c, e))
    (ChuTensorNeg a b (c, e) (ChuTensorNeg c d e f))
assocChu =
  ChuMorphism
    (\((x, y), z) -> (x, (y, z)))
    ( \(ChuTensorNeg h k) ->
        ChuTensorNeg
          (\(x, y) -> ctnForward (h x) y)
          (\z -> ChuTensorNeg (\x -> ctnBackward (h x) z) (\y -> k (y, z)))
    )
{-# INLINE assocChu #-}

-- | Inverse associator @A ⊗ (B ⊗ C) → (A ⊗ B) ⊗ C@ over @Set@.
assocChuInv ::
  ChuMorphism
    (,)
    r
    (->)
    (a, (c, e))
    (ChuTensorNeg a b (c, e) (ChuTensorNeg c d e f))
    ((a, c), e)
    (ChuTensorNeg (a, c) (ChuTensorNeg a b c d) e f)
assocChuInv =
  ChuMorphism
    (\(x, (y, z)) -> ((x, y), z))
    ( \(ChuTensorNeg f g) ->
        ChuTensorNeg
          (\x -> ChuTensorNeg (\y -> f (x, y)) (\z -> ctnForward (g z) x))
          (\(y, z) -> ctnBackward (g z) y)
    )
{-# INLINE assocChuInv #-}

-- | Slide @A ⊗ (B ⊗ C) → B ⊗ (A ⊗ C)@ over @Set@.
--
-- This is the Channel 'slide', derived as @assoc . par swap id . assoc'@
-- and written directly so the instance does not have to manufacture
-- intermediate object constraints.
slideChu ::
  ChuMorphism
    (,)
    r
    (->)
    (a, (c, e))
    (ChuTensorNeg a b (c, e) (ChuTensorNeg c d e f))
    (c, (a, e))
    (ChuTensorNeg c d (a, e) (ChuTensorNeg a b e f))
slideChu =
  ChuMorphism
    (\(x, (y, z)) -> (y, (x, z)))
    ( \(ChuTensorNeg h' k') ->
        ChuTensorNeg
          (\x -> ChuTensorNeg (\y -> ctnForward (h' y) x) (\z -> k' (x, z)))
          (\(y, z) -> ctnBackward (h' y) z)
    )
{-# INLINE slideChu #-}

-- | Enumerate all 'ChuTensorNeg' values for finite carriers.
chuTensorNegs ::
  forall r a b.
  (Eq r, Eq (ChuPosType a), Eq (ChuPosType b), ChuObject r a, ChuObject r b) =>
  Proxy a ->
  Proxy b ->
  [ChuTensorNeg (ChuPosType a) (ChuNegType a) (ChuPosType b) (ChuNegType b)]
chuTensorNegs _ _ =
  let as = chuPosAll @r @a
      bs = chuNegAll @r @a
      cs = chuPosAll @r @b
      ds = chuNegAll @r @b
      r = chuPair (chuObject @r @a)
      s = chuPair (chuObject @r @b)
   in [ ChuTensorNeg f g
        | f <- functions as ds,
          g <- functions cs bs,
          all (\(a, c) -> r (a, g c) == s (c, f a)) (cartesian as cs)
        ]

-- | Enumerate all 'ChuParPos' values for finite carriers.
chuParPoss ::
  forall r a b.
  (Eq r, Eq (ChuNegType a), Eq (ChuNegType b), ChuObject r a, ChuObject r b) =>
  Proxy a ->
  Proxy b ->
  [ChuParPos (ChuPosType a) (ChuNegType a) (ChuPosType b) (ChuNegType b)]
chuParPoss _ _ =
  let as = chuPosAll @r @a
      bs = chuNegAll @r @a
      cs = chuPosAll @r @b
      ds = chuNegAll @r @b
      r = chuPair (chuObject @r @a)
      s = chuPair (chuObject @r @b)
   in [ ChuParPos f g
        | f <- functions bs cs,
          g <- functions ds as,
          all (\(b, d) -> r (g d, b) == s (f b, d)) (cartesian bs ds)
        ]

-- | All functions from a finite domain to a finite codomain.
--
-- The domain list is assumed to be an exhaustive enumeration of the type;
-- supplying an incomplete list makes the returned functions silently wrong
-- rather than loudly partial. The empty-domain case returns a bottom so that
-- the list type remains useful, but callers should avoid reaching it.
functions :: (Eq a) => [a] -> [b] -> [a -> b]
functions [] _ = [const (error "functions: empty domain")]
functions domain codomain = map (listToFunction domain) (sequenceA (replicate (length domain) codomain))

listToFunction :: (Eq a) => [a] -> [b] -> a -> b
listToFunction domain values x = fromJust (lookup x (zip domain values))
  where
    fromJust (Just y) = y
    fromJust Nothing = error "listToFunction: input not in domain"

-- | Cartesian product of two lists.
cartesian :: [a] -> [b] -> [(a, b)]
cartesian xs ys = [(x, y) | x <- xs, y <- ys]

-- | A Chu object is /separated/ when the pairing distinguishes every pair of
-- positive points.  Equivalently, the transposed pairing @A⁺ -> (A⁻ ⊸ ⊥)@ is
-- injective.
chuSeparated ::
  forall r a.
  (Eq r, Eq (ChuPosType a), ChuObject r a) =>
  Proxy a ->
  Bool
chuSeparated _ =
  let e = chuPair (chuObject @r @a)
      as = chuPosAll @r @a
      bs = chuNegAll @r @a
   in all
        (\(a1, a2) -> a1 == a2 || any (\b -> e (a1, b) /= e (a2, b)) bs)
        (cartesian as as)

-- | A Chu object is /extensional/ when the pairing distinguishes every pair of
-- negative points.  Equivalently, the pairing @A⁻ -> (A⁺ ⊸ ⊥)@ is injective.
chuExtensional ::
  forall r a.
  (Eq r, Eq (ChuNegType a), ChuObject r a) =>
  Proxy a ->
  Bool
chuExtensional _ =
  let e = chuPair (chuObject @r @a)
      as = chuPosAll @r @a
      bs = chuNegAll @r @a
   in all
        (\(b1, b2) -> b1 == b2 || any (\a -> e (a, b1) /= e (a, b2)) as)
        (cartesian bs bs)

-- ===========================================================================
-- Object-indexed Chu category (OChu / SepChu)
-- ===========================================================================
--
-- The existing 'Chu' category treats any 'ChuObj'-shaped type as an object.
-- That is too unstructured for a 'Tensor' instance: the unit object is not
-- the bare @()@, and structural morphisms such as the unitors need the
-- object's pairing.  'OChu' restricts objects to types that carry a canonical
-- 'ChuObj' value via the 'ChuObject' class, and its 'Ob' further requires
-- separation and extensionality.  That is Barr's separated-extensional
-- subcategory: the room where @A ≅ A⊥⊥@ and the associator pentagon lives.
-- 'SepChu' is a synonym for this reading.

-- | A type-level Chu object: a tag with a canonical 'ChuObj' value and
-- finite carrier enumerations.
--
-- 'chuPosAll' and 'chuNegAll' are used by separation / extensionality oracles
-- and by enumeration of tensor / par negatives.  They default to a runtime
-- error; only objects that actually participate in finite oracles need to
-- supply them.
class ChuObject (r :: Type) a where
  chuObject :: ChuObj (,) r (->) (ChuPosType a) (ChuNegType a)
  chuPosAll :: [ChuPosType a]
  chuPosAll = error "chuPosAll: not defined for this object"
  chuNegAll :: [ChuNegType a]
  chuNegAll = error "chuNegAll: not defined for this object"

-- | Marker: the pairing distinguishes positive points.
--
-- Runtime evidence is available through 'chuSeparated'.  Instances close the
-- constructors we admit ('ChuTwo', 'ChuOUnit', tensor, negation).
class (ChuObject r a) => ChuSeparated r a

-- | Marker: the pairing distinguishes negative points.
--
-- Runtime evidence is available through 'chuExtensional'.  Negation swaps
-- this with 'ChuSeparated'.
class (ChuObject r a) => ChuExtensional r a

-- | Type-level non-emptiness of an object's positive carrier.
--
-- Used to guard additive marker instances: @A & B@ can only be extensional
-- when both @A@ and @B@ have at least one positive point, because the
-- negative carrier is the disjoint union and distinct injections must be
-- separated by a positive pair.
type family ChuPosNonEmpty (a :: Type) :: Bool where
  ChuPosNonEmpty (ChuOUnit r) = 'True
  ChuPosNonEmpty (ChuOTop r) = 'True
  ChuPosNonEmpty (ChuOZero r) = 'False
  ChuPosNonEmpty (ChuOTensor r a b) = If (ChuPosNonEmpty a) (ChuPosNonEmpty b) 'False
  ChuPosNonEmpty (ChuOWith r a b) = If (ChuPosNonEmpty a) (ChuPosNonEmpty b) 'False
  ChuPosNonEmpty (ChuOPlus r a b) = If (ChuPosNonEmpty a) 'True (ChuPosNonEmpty b)
  ChuPosNonEmpty (ChuOPar r a b) = 'True
  ChuPosNonEmpty (ChuONeg r a) = ChuNegNonEmpty a
  ChuPosNonEmpty (ChuOLolli r a b) = 'True
  ChuPosNonEmpty (ChuOBang r a) = ChuPosNonEmpty a
  ChuPosNonEmpty (ChuOWhyNot r a) = 'True
  ChuPosNonEmpty ChuTwo = 'True
  ChuPosNonEmpty ChuThree = 'True
  ChuPosNonEmpty ChuDouble01 = 'True
  ChuPosNonEmpty ChuDelivery = 'True

-- | Type-level non-emptiness of an object's negative carrier.
--
-- Used to guard additive marker instances: @A ⊕ B@ can only be separated
-- when both @A@ and @B@ have at least one negative point, because the
-- positive carrier is the disjoint union and distinct injections must be
-- separated by a negative pair.
type family ChuNegNonEmpty (a :: Type) :: Bool where
  ChuNegNonEmpty (ChuOUnit r) = 'True
  ChuNegNonEmpty (ChuOTop r) = 'False
  ChuNegNonEmpty (ChuOZero r) = 'True
  ChuNegNonEmpty (ChuOTensor r a b) = 'True
  ChuNegNonEmpty (ChuOWith r a b) = If (ChuNegNonEmpty a) 'True (ChuNegNonEmpty b)
  ChuNegNonEmpty (ChuOPlus r a b) = If (ChuNegNonEmpty a) (ChuNegNonEmpty b) 'False
  ChuNegNonEmpty (ChuOPar r a b) = If (ChuNegNonEmpty a) (ChuNegNonEmpty b) 'False
  ChuNegNonEmpty (ChuONeg r a) = ChuPosNonEmpty a
  ChuNegNonEmpty (ChuOLolli r a b) = If (ChuPosNonEmpty a) (ChuNegNonEmpty b) 'False
  ChuNegNonEmpty (ChuOBang r a) = 'True
  ChuNegNonEmpty (ChuOWhyNot r a) = ChuNegNonEmpty a
  ChuNegNonEmpty ChuTwo = 'True
  ChuNegNonEmpty ChuThree = 'True
  ChuNegNonEmpty ChuDouble01 = 'True
  ChuNegNonEmpty ChuDelivery = 'True

-- | Unit object type for 'OChu'.
data ChuOUnit (r :: Type) = ChuOUnit

instance ChuObject r (ChuOUnit r) where
  chuObject = chuUnitObj
  chuPosAll = [()]
  chuNegAll = error "chuNegAll: ChuOUnit negative carrier is the dualising object and is not enumerated"

instance ChuSeparated r (ChuOUnit r)

instance ChuExtensional r (ChuOUnit r)

-- | Tensor object type for 'OChu'.
data ChuOTensor (r :: Type) a b = ChuOTensor

type instance Unit (ChuOTensor r) = ChuOUnit r

instance
  (Eq r, ChuObject r a, ChuObject r b) =>
  ChuObject r (ChuOTensor r a b)
  where
  chuObject = tensorChuObj (chuObject @r @a) (chuObject @r @b)
  chuPosAll = cartesian (chuPosAll @r @a) (chuPosAll @r @b)
  chuNegAll = error "chuNegAll: tensor negative carrier is not enumerated"

instance (Eq r, ChuSeparated r a, ChuSeparated r b) => ChuSeparated r (ChuOTensor r a b)

instance (Eq r, ChuExtensional r a, ChuExtensional r b) => ChuExtensional r (ChuOTensor r a b)

-- | Object-level negation @A⊥@.
--
-- Carriers swap; the pairing is 'negateChu' of the underlying object.
-- Separation and extensionality swap: if @A@ is separated then @A⊥@ is
-- extensional, and conversely.
data ChuONeg (r :: Type) a = ChuONeg

instance (ChuObject r a) => ChuObject r (ChuONeg r a) where
  chuObject = negateChu (chuObject @r @a)
  chuPosAll = chuNegAll @r @a
  chuNegAll = chuPosAll @r @a

instance (ChuExtensional r a) => ChuSeparated r (ChuONeg r a)

instance (ChuSeparated r a) => ChuExtensional r (ChuONeg r a)

-- | The self-dual two-point Chu object used in the oracles.
data ChuTwo = ChuTwo

instance ChuObject Bool ChuTwo where
  chuObject = ChuObj (uncurry (==))
  chuPosAll = [False, True]
  chuNegAll = [False, True]

instance ChuSeparated Bool ChuTwo

instance ChuExtensional Bool ChuTwo

-- | A non-self-dual three-point Chu object over 'Bool'.
--
-- Both carriers are @Maybe Bool@, but the pairing is the non-symmetric
-- partial-order relation (@Nothing <= Just False <= Just True@), not equality.
-- This breaks the self-duality coincidence of 'ChuTwo' while keeping the
-- object separated and extensional.
data ChuThree = ChuThree

instance ChuObject Bool ChuThree where
  chuObject = ChuObj (uncurry (<=))
  chuPosAll = [Nothing, Just False, Just True]
  chuNegAll = [Nothing, Just False, Just True]

instance ChuSeparated Bool ChuThree

instance ChuExtensional Bool ChuThree

-- | A finite Double-semiring Chu object.
--
-- Carriers are the two-element type @Bool@, representing the subset
-- @{0, 1}@ of 'Double'.  The full real line is replaced by this tiny
-- subset so the finite oracles remain runnable.  The pairing lands in
-- 'Double' via the existing 'ChuSemiring' instance.
data ChuDouble01 = ChuDouble01

instance ChuObject Double ChuDouble01 where
  chuObject = ChuObj chuDouble01Pair
    where
      chuDouble01Pair :: (Bool, Bool) -> Double
      chuDouble01Pair (False, False) = 0
      chuDouble01Pair (False, True) = 0.5
      chuDouble01Pair (True, False) = 0
      chuDouble01Pair (True, True) = 1
  chuPosAll = [False, True]
  chuNegAll = [False, True]

instance ChuSeparated Double ChuDouble01

instance ChuExtensional Double ChuDouble01

-- | A concrete delivery-matrix Chu object: two posts and two agents.
--
-- The pairing is the boolean delivery matrix computed by 'deliveryMatrix'
-- and 'deliversToSemiring'.  Posts and agents are indexed by 'Bool' so the
-- carriers stay finite and the oracles remain runnable.
data ChuDelivery = ChuDelivery

instance ChuObject Bool ChuDelivery where
  chuObject = ChuObj chuDeliveryPair
    where
      agents :: [Bool]
      agents = [False, True]
      recipients :: [[Bool]]
      recipients = [[False], [False, True]]
      chuDeliveryPair :: (Bool, Bool) -> Bool
      chuDeliveryPair (p, a) = deliveryMatrix agents recipients !! fromEnum p !! fromEnum a
  chuPosAll = [False, True]
  chuNegAll = [False, True]

instance ChuSeparated Bool ChuDelivery

instance ChuExtensional Bool ChuDelivery

-- | A tiny self-dual Chu object over @Any@ (disjunction monoid) with equality
-- pairing. Used to test the bimonoid on @!A@ from a 'Monoid' on @A⁺@.
data ChuAny = ChuAny

instance ChuObject Bool ChuAny where
  chuObject = ChuObj (\(Any x, Any y) -> x == y)
  chuPosAll = [Any False, Any True]
  chuNegAll = [Any False, Any True]

instance ChuSeparated Bool ChuAny

instance ChuExtensional Bool ChuAny

-- | The object-indexed Chu construction as a base arrow.
newtype OChu (r :: Type) (a :: Type) (b :: Type) = OChu {unOChu :: Chu (,) r (->) a b}

-- | Documentation alias for 'OChu'.
--
-- This is a plain type synonym, not a separate category: the
-- separated-extensional conditions are enforced only by the 'Ob' constraint
-- of 'OChu'.  If you need Barr's subcategory to be tracked in the type
-- system, wrap 'OChu' in a newtype with its own 'Category' instance.
type SepChu = OChu

instance Category (OChu r) where
  id :: forall a. OChu r a a
  id = OChu id
  (.) :: forall a b c. OChu r b c -> OChu r a b -> OChu r a c
  OChu g . OChu f = OChu (g . f)

-- | Symmetric braiding for the Chu tensor over @Set@.
swapChu ::
  forall r a b.
  ( ChuPosType (ChuOTensor r a b) ~ (ChuPosType a, ChuPosType b),
    ChuNegType (ChuOTensor r a b)
      ~ ChuTensorNeg (ChuPosType a) (ChuNegType a) (ChuPosType b) (ChuNegType b),
    ChuPosType (ChuOTensor r b a) ~ (ChuPosType b, ChuPosType a),
    ChuNegType (ChuOTensor r b a)
      ~ ChuTensorNeg (ChuPosType b) (ChuNegType b) (ChuPosType a) (ChuNegType a)
  ) =>
  ChuMorphism
    (,)
    r
    (->)
    (ChuPosType (ChuOTensor r a b))
    (ChuNegType (ChuOTensor r a b))
    (ChuPosType (ChuOTensor r b a))
    (ChuNegType (ChuOTensor r b a))
swapChu = ChuMorphism (\(x, y) -> (y, x)) (\(ChuTensorNeg h k) -> ChuTensorNeg k h)

-- | Parallel composition for 'OChu'.
parOChu ::
  forall r (a :: Type) (b :: Type) (c :: Type) (d :: Type).
  OChu r a b ->
  OChu r c d ->
  OChu r (ChuOTensor r a c) (ChuOTensor r b d)
parOChu (OChu (Chu f)) (OChu (Chu g)) = OChu (Chu (tensorChu f g))
{-# INLINE parOChu #-}

-- | Left unitor @I ⊗ A → A@ for 'OChu'.
unitlOChu ::
  forall r (a :: Type).
  (ChuObject r a) =>
  OChu r (ChuOTensor r (ChuOUnit r) a) a
unitlOChu = OChu (Chu (leftUnitorChu (chuObject @r @a)))
{-# INLINE unitlOChu #-}

-- | Inverse left unitor @A → I ⊗ A@ for 'OChu'.
unitlOChu' ::
  forall r (a :: Type).
  (ChuObject r a) =>
  OChu r a (ChuOTensor r (ChuOUnit r) a)
unitlOChu' = OChu (Chu (leftUnitorChuInv (chuObject @r @a)))
{-# INLINE unitlOChu' #-}

-- | Right unitor @A ⊗ I → A@ for 'OChu'.
unitrOChu ::
  forall r (a :: Type).
  (ChuObject r a) =>
  OChu r (ChuOTensor r a (ChuOUnit r)) a
unitrOChu = OChu (Chu (rightUnitorChu (chuObject @r @a)))
{-# INLINE unitrOChu #-}

-- | Inverse right unitor @A → A ⊗ I@ for 'OChu'.
unitrOChu' ::
  forall r (a :: Type).
  (ChuObject r a) =>
  OChu r a (ChuOTensor r a (ChuOUnit r))
unitrOChu' = OChu (Chu (rightUnitorChuInv (chuObject @r @a)))
{-# INLINE unitrOChu' #-}

-- | Symmetric braiding @A ⊗ B → B ⊗ A@ for 'OChu'.
swapOChu ::
  forall r (a :: Type) (b :: Type).
  OChu r (ChuOTensor r a b) (ChuOTensor r b a)
swapOChu = OChu (Chu (swapChu @r @a @b))
{-# INLINE swapOChu #-}

-- | Monoidal structure on the object-level Chu tensor.
--
-- 'assoc' / 'assoc'' / 'slide' are the Set-level maps 'assocChu',
-- 'assocChuInv', and 'slideChu'.  The pentagon is checked on 'ChuTwo'
-- by finite enumeration in @circuits-axioma@.
instance (Eq r) => Channel (ChuOTensor r) (OChu r) where
  assoc = OChu (Chu assocChu)
  assoc' = OChu (Chu assocChuInv)
  slide = OChu (Chu slideChu)

-- | Double-negation unit @A → A⊥⊥@.
--
-- On carriers this is the identity: two swaps restore @A⁺@ and @A⁻@, and
-- the pairing is @e . swap . swap = e@.  It is an isomorphism precisely
-- on separated-extensional objects.
dnUnitChu :: forall r a. OChu r a (ChuONeg r (ChuONeg r a))
dnUnitChu =
  OChu
    ( Chu
        ( idChu ::
            ChuMorphism
              (,)
              r
              (->)
              (ChuPosType a)
              (ChuNegType a)
              (ChuPosType (ChuONeg r (ChuONeg r a)))
              (ChuNegType (ChuONeg r (ChuONeg r a)))
        )
    )

-- | Double-negation counit @A⊥⊥ → A@.
dnCounitChu :: forall r a. OChu r (ChuONeg r (ChuONeg r a)) a
dnCounitChu =
  OChu
    ( Chu
        ( idChu ::
            ChuMorphism
              (,)
              r
              (->)
              (ChuPosType (ChuONeg r (ChuONeg r a)))
              (ChuNegType (ChuONeg r (ChuONeg r a)))
              (ChuPosType a)
              (ChuNegType a)
        )
    )

-- | Object-level linear implication @A ⊸ B = A⊥ ⅋ B@.
data ChuOLolli (r :: Type) a b = ChuOLolli

instance
  (Eq r, ChuObject r a, ChuObject r b) =>
  ChuObject r (ChuOLolli r a b)
  where
  chuObject = lolliChuObj (chuObject @r @a) (chuObject @r @b)
  chuPosAll = error "chuPosAll: linear implication positive carrier is not enumerated"
  chuNegAll = cartesian (chuPosAll @r @a) (chuNegAll @r @b)

instance (Eq r, ChuSeparated r a, ChuSeparated r b) => ChuSeparated r (ChuOLolli r a b)

instance (Eq r, ChuExtensional r a, ChuExtensional r b) => ChuExtensional r (ChuOLolli r a b)

-- | Object-level additive conjunction @A & B@.
--
-- 'ChuSeparated' is available whenever both summands are separated.
-- 'ChuExtensional' is guarded by 'ChuPosNonEmpty': when one summand has an
-- empty positive carrier (e.g. @A & 0@), distinct negative injections cannot
-- be separated, so the instance is not asserted.
data ChuOWith (r :: Type) a b = ChuOWith

instance
  (ChuObject r a, ChuObject r b) =>
  ChuObject r (ChuOWith r a b)
  where
  chuObject = withChuObj (chuObject @r @a) (chuObject @r @b)
  chuPosAll = cartesian (chuPosAll @r @a) (chuPosAll @r @b)
  chuNegAll = map Left (chuNegAll @r @a) ++ map Right (chuNegAll @r @b)

instance (ChuSeparated r a, ChuSeparated r b) => ChuSeparated r (ChuOWith r a b)

instance
  ( ChuExtensional r a,
    ChuExtensional r b,
    ChuPosNonEmpty a ~ 'True,
    ChuPosNonEmpty b ~ 'True
  ) =>
  ChuExtensional r (ChuOWith r a b)

-- | Object-level additive disjunction @A ⊕ B@.
--
-- 'ChuExtensional' is available whenever both summands are extensional.
-- 'ChuSeparated' is guarded by 'ChuNegNonEmpty': when one summand has an
-- empty negative carrier (e.g. @⊤ ⊕ B@), distinct positive injections cannot
-- be separated, so the instance is not asserted.
data ChuOPlus (r :: Type) a b = ChuOPlus

instance
  (ChuObject r a, ChuObject r b) =>
  ChuObject r (ChuOPlus r a b)
  where
  chuObject = oplusChuObj (chuObject @r @a) (chuObject @r @b)
  chuPosAll = map Left (chuPosAll @r @a) ++ map Right (chuPosAll @r @b)
  chuNegAll = cartesian (chuNegAll @r @a) (chuNegAll @r @b)

instance
  ( ChuSeparated r a,
    ChuSeparated r b,
    ChuNegNonEmpty a ~ 'True,
    ChuNegNonEmpty b ~ 'True
  ) =>
  ChuSeparated r (ChuOPlus r a b)

instance (ChuExtensional r a, ChuExtensional r b) => ChuExtensional r (ChuOPlus r a b)

-- | Object-level multiplicative disjunction @A ⅋ B@.
--
-- Positive carrier is the set of 'ChuParPos' witnesses; negative carrier is
-- the product @A⁻ × B⁻@.  This is the real par, distinct from the additive
-- disjunction 'ChuOPlus'.
data ChuOPar (r :: Type) a b = ChuOPar

instance
  (Eq r, ChuObject r a, ChuObject r b) =>
  ChuObject r (ChuOPar r a b)
  where
  chuObject = parChuObj (chuObject @r @a) (chuObject @r @b)
  chuPosAll = error "chuPosAll: par positive carrier is not enumerated"
  chuNegAll = cartesian (chuNegAll @r @a) (chuNegAll @r @b)

instance (Eq r, ChuSeparated r a, ChuSeparated r b) => ChuSeparated r (ChuOPar r a b)

instance (Eq r, ChuExtensional r a, ChuExtensional r b) => ChuExtensional r (ChuOPar r a b)

-- | Object-level additive unit @⊤@.
data ChuOTop (r :: Type) = ChuOTop

instance ChuObject r (ChuOTop r) where
  chuObject = topChuObj
  chuPosAll = [()]
  chuNegAll = []

instance ChuSeparated r (ChuOTop r)

instance ChuExtensional r (ChuOTop r)

-- | Object-level additive zero @0@.
data ChuOZero (r :: Type) = ChuOZero

instance ChuObject r (ChuOZero r) where
  chuObject = zeroChuObj
  chuPosAll = []
  chuNegAll = [()]

instance ChuSeparated r (ChuOZero r)

instance ChuExtensional r (ChuOZero r)

-- | The par unit is the dual of the tensor unit: @⊥ = I⊥@.
type instance Bot (ChuOPar r) = ChuONeg r (ChuOUnit r)

-- | Par structure on the object-indexed Chu category.
--
-- The par product of objects is 'ChuOPar'; the structural morphisms are the
-- Set-level par maps already defined for 'Chu' morphisms.

-- | Parallel composition for the par product on 'OChu'.
parPOChu ::
  forall r (a :: Type) (b :: Type) (c :: Type) (d :: Type).
  OChu r a b ->
  OChu r c d ->
  OChu r (ChuOPar r a c) (ChuOPar r b d)
parPOChu (OChu (Chu f)) (OChu (Chu g)) = OChu (Chu (parChu f g))
{-# INLINE parPOChu #-}

-- | Left unitor @⊥ ⅋ A → A@ for 'OChu'.
unitlPOChu ::
  forall r (a :: Type).
  OChu r (ChuOPar r (Bot (ChuOPar r)) a) a
unitlPOChu = OChu (Chu leftUnitorParChu)
{-# INLINE unitlPOChu #-}

-- | Inverse left unitor @A → ⊥ ⅋ A@ for 'OChu'.
unitlPOChu' ::
  forall r (a :: Type).
  (ChuObject r a) =>
  OChu r a (ChuOPar r (Bot (ChuOPar r)) a)
unitlPOChu' = OChu (Chu (leftUnitorParChuInv (chuObject @r @a)))
{-# INLINE unitlPOChu' #-}

-- | Right unitor @A ⅋ ⊥ → A@ for 'OChu'.
unitrPOChu ::
  forall r (a :: Type).
  OChu r (ChuOPar r a (Bot (ChuOPar r))) a
unitrPOChu = OChu (Chu rightUnitorParChu)
{-# INLINE unitrPOChu #-}

-- | Inverse right unitor @A → A ⅋ ⊥@ for 'OChu'.
unitrPOChu' ::
  forall r (a :: Type).
  (ChuObject r a) =>
  OChu r a (ChuOPar r a (Bot (ChuOPar r)))
unitrPOChu' = OChu (Chu (rightUnitorParChuInv (chuObject @r @a)))
{-# INLINE unitrPOChu' #-}

-- | Curry @(A ⊗ B → C) → (A → B ⊸ C)@ over @Set@.
curryChu ::
  ChuMorphism
    (,)
    r
    (->)
    (a, c)
    (ChuTensorNeg a b c d)
    e
    f ->
  ChuMorphism
    (,)
    r
    (->)
    a
    b
    (ChuParPos d c e f)
    (c, f)
curryChu (ChuMorphism fPos fNeg) =
  ChuMorphism
    (\x -> ChuParPos (\y -> fPos (x, y)) (\z -> ctnForward (fNeg z) x))
    (\(y, z) -> ctnBackward (fNeg z) y)
{-# INLINE curryChu #-}

-- | Uncurry @(A → B ⊸ C) → (A ⊗ B → C)@ over @Set@.
uncurryChu ::
  ChuMorphism
    (,)
    r
    (->)
    a
    b
    (ChuParPos d c e f)
    (c, f) ->
  ChuMorphism
    (,)
    r
    (->)
    (a, c)
    (ChuTensorNeg a b c d)
    e
    f
uncurryChu (ChuMorphism gPos gNeg) =
  ChuMorphism
    (\(x, y) -> cppForward (gPos x) y)
    (\z -> ChuTensorNeg (\x -> cppBackward (gPos x) z) (\y -> gNeg (y, z)))
{-# INLINE uncurryChu #-}

-- | Evaluation counit @A ⊗ (A ⊸ B) → B@ for 'OChu'.
evalOChu ::
  forall r (a :: Type) (b :: Type).
  (ChuObject r a, ChuObject r b) =>
  OChu r (ChuOTensor r a (ChuOLolli r a b)) b
evalOChu = OChu (Chu (evalChu (chuObject @r @a) (chuObject @r @b)))
{-# INLINE evalOChu #-}

-- | Curry @(A ⊗ B → C) → (A → B ⊸ C)@ for 'OChu'.
curryOChu ::
  forall r (a :: Type) (b :: Type) (c :: Type).
  OChu r (ChuOTensor r a b) c ->
  OChu r a (ChuOLolli r b c)
curryOChu (OChu (Chu f)) = OChu (Chu (curryChu f))
{-# INLINE curryOChu #-}

-- | Uncurry @(A → B ⊸ C) → (A ⊗ B → C)@ for 'OChu'.
uncurryOChu ::
  forall r (a :: Type) (b :: Type) (c :: Type).
  OChu r a (ChuOLolli r b c) ->
  OChu r (ChuOTensor r a b) c
uncurryOChu (OChu (Chu g)) =
  OChu
    ( Chu
        ( uncurryChu g ::
            ChuMorphism
              (,)
              r
              (->)
              (ChuPosType a, ChuPosType b)
              (ChuTensorNeg (ChuPosType a) (ChuNegType a) (ChuPosType b) (ChuNegType b))
              (ChuPosType c)
              (ChuNegType c)
        )
    )
{-# INLINE uncurryOChu #-}

-- ===========================================================================
-- Exponentials: !A = (A⁺, A⁺ → r, eval), ?A = (!A⊥)⊥
-- ===========================================================================

-- | All functions from a finite domain to a finite codomain.
chuFunctionals :: (Eq a) => [a] -> [r] -> [a -> r]
chuFunctionals = functions

-- | Cofree cocommutative comonoid on a Set-based Chu object.
--
-- Positives are those of @A@; negatives are every functional @A⁺ → r@;
-- the pairing is evaluation.  Original negatives embed by Yoneda
-- @d ↦ \\a -> e(a, d)@, and constants @k ↦ const k@ supply discard.
bangChuObj :: ChuObj (,) r (->) a b -> ChuObj (,) r (->) a (a -> r)
bangChuObj _ = ChuObj (\(x, f) -> f x)

-- | Free commutative monoid @?A = (!A⊥)⊥@.
--
-- Positives are the functionals @A⁻ → r@; negatives are those of @A@.
whyNotChuObj :: ChuObj (,) r (->) a b -> ChuObj (,) r (->) (b -> r) b
whyNotChuObj a = negateChu (bangChuObj (negateChu a))

-- | Copy @!A → !A ⊗ !A@: diagonal on points, contraction on functionals.
copyBangChu ::
  ChuMorphism
    (,)
    r
    (->)
    a
    (a -> r)
    (a, a)
    (ChuTensorNeg a (a -> r) a (a -> r))
copyBangChu =
  ChuMorphism
    (\x -> (x, x))
    (\n x -> ctnBackward n x x)
{-# INLINE copyBangChu #-}

-- | Discard @!A → I@: the constant functionals.
discardBangChu ::
  ChuMorphism (,) r (->) a (a -> r) () r
discardBangChu =
  ChuMorphism (\_ -> ()) const
{-# INLINE discardBangChu #-}

-- | Merge @!A ⊗ !A → !A@: the monoid operation on points, bilinearly
-- extended to functionals.
mergeBangChu ::
  (Monoid a) =>
  ChuMorphism
    (,)
    r
    (->)
    (a, a)
    (ChuTensorNeg a (a -> r) a (a -> r))
    a
    (a -> r)
mergeBangChu =
  ChuMorphism
    (uncurry (<>))
    (\k -> ChuTensorNeg (\x y -> k (x <> y)) (\y x -> k (x <> y)))
{-# INLINE mergeBangChu #-}

-- | Zero @I → !A@: the monoid unit as a point of @A⁺@.
zeroBangChu ::
  (Monoid a) =>
  ChuMorphism (,) r (->) () r a (a -> r)
zeroBangChu =
  ChuMorphism (\_ -> mempty) (\k -> k mempty)
{-# INLINE zeroBangChu #-}

-- | Dereliction @!A → A@: identity on points, Yoneda on negatives.
derelictChu ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) a (a -> r) a b
derelictChu (ChuObj e) =
  ChuMorphism id (\d a -> e (a, d))
{-# INLINE derelictChu #-}

-- | Introduction @A → ?A@: Yoneda on positives, identity on negatives.
introduceChu ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) a b (b -> r) b
introduceChu (ChuObj e) =
  ChuMorphism (\x d -> e (x, d)) id
{-# INLINE introduceChu #-}

-- | Digging @!A → !!A@.
--
-- Over the Set-based ! of this module, @!!A@ is the same object as @!A@
-- (positive carrier @A⁺@, negative carrier @A⁺ → r@), so digging is the
-- identity. This is an observable fact about the model, not a stub.
digChu ::
  ChuMorphism (,) r (->) a (a -> r) a (a -> r)
digChu = idChu
{-# INLINE digChu #-}

-- | Promotion @!A ⊗ !B → !(A & B)@.
--
-- Forward is the identity on the shared positive carrier @(A⁺, B⁺)@.
-- Backward turns a bilinear element of @!A ⊗ !B@ into a functional on
-- @(A⁺, B⁺)@ using either leg of the bilinear condition.
promoteChu ::
  ChuMorphism
    (,)
    r
    (->)
    (a, c)
    (ChuTensorNeg a (a -> r) c (c -> r))
    (a, c)
    ((a, c) -> r)
promoteChu =
  ChuMorphism
    id
    (\n -> ChuTensorNeg (\x y -> n (x, y)) (\y x -> n (x, y)))
{-# INLINE promoteChu #-}

-- | Zero @I → ?A@.  The unit functional is constantly 'sZero'.
--
-- This is not the ⅋-monoid unit (that is 'zeroWhyNotParChu' : @⊥ → ?A@).
zeroWhyNotChu ::
  (ChuSemiring r) =>
  ChuMorphism (,) r (->) () r (b -> r) b
zeroWhyNotChu =
  ChuMorphism (\_ -> const sZero) (\_ -> sZero)
{-# INLINE zeroWhyNotChu #-}

-- | Merge @?A ⅋ ?A → ?A@: the dual of 'copyBangChu'.
--
-- A par-positive is a pair of functionals @A⁻ → (A⁻ → r)@ satisfying
-- @g y x = f x y@.  Merge contracts the diagonal @\\x -> g x x@.
mergeWhyNotParChu ::
  ChuMorphism
    (,)
    r
    (->)
    (ChuParPos (b -> r) b (b -> r) b)
    (b, b)
    (b -> r)
    b
mergeWhyNotParChu =
  ChuMorphism
    (\(ChuParPos _ g) x -> g x x)
    (\d -> (d, d))
{-# INLINE mergeWhyNotParChu #-}

-- | ⅋-monoid unit @⊥ → ?A@: constants, dual of 'discardBangChu'.
zeroWhyNotParChu ::
  ChuMorphism (,) r (->) r () (b -> r) b
zeroWhyNotParChu =
  ChuMorphism const (\_ -> ())
{-# INLINE zeroWhyNotParChu #-}

-- | Left unitor @⊥ ⅋ A → A@ over @Set@.
leftUnitorParChu ::
  ChuMorphism (,) r (->) (ChuParPos r () p n) ((), n) p n
leftUnitorParChu =
  ChuMorphism (\q -> cppForward q ()) (\d -> ((), d))
{-# INLINE leftUnitorParChu #-}

-- | Right unitor @A ⅋ ⊥ → A@ over @Set@.
rightUnitorParChu ::
  ChuMorphism (,) r (->) (ChuParPos p n r ()) (n, ()) p n
rightUnitorParChu =
  ChuMorphism (\q -> cppBackward q ()) (\d -> (d, ()))
{-# INLINE rightUnitorParChu #-}

-- | Inverse of the left par unitor: @A → ⊥ ⅋ A@ over @Set@.
leftUnitorParChuInv ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) a b (ChuParPos r () a b) ((), b)
leftUnitorParChuInv (ChuObj e) =
  ChuMorphism
    (\x -> ChuParPos (\_ -> x) (\d -> e (x, d)))
    (\(_, d) -> d)
{-# INLINE leftUnitorParChuInv #-}

-- | Inverse of the right par unitor: @A → A ⅋ ⊥@ over @Set@.
rightUnitorParChuInv ::
  ChuObj (,) r (->) a b ->
  ChuMorphism (,) r (->) a b (ChuParPos a b r ()) (b, ())
rightUnitorParChuInv (ChuObj e) =
  ChuMorphism
    (\x -> ChuParPos (\d -> e (x, d)) (\_ -> x))
    (\(d, _) -> d)
{-# INLINE rightUnitorParChuInv #-}

-- | Associator @(A ⅋ B) ⅋ C → A ⅋ (B ⅋ C)@ over @Set@.
assocParChu ::
  ChuMorphism
    (,)
    r
    (->)
    (ChuParPos (ChuParPos a b c d) (b, d) e f)
    ((b, d), f)
    (ChuParPos a b (ChuParPos c d e f) (d, f))
    (b, (d, f))
assocParChu =
  ChuMorphism
    ( \p ->
        ChuParPos
          ( \x ->
              ChuParPos
                (\y -> cppForward p (x, y))
                (\z -> cppForward (cppBackward p z) x)
          )
          (\(y, z) -> cppBackward (cppBackward p z) y)
    )
    (\(x, (y, z)) -> ((x, y), z))
{-# INLINE assocParChu #-}

-- | Inverse associator @A ⅋ (B ⅋ C) → (A ⅋ B) ⅋ C@ over @Set@.
assocParChuInv ::
  ChuMorphism
    (,)
    r
    (->)
    (ChuParPos a b (ChuParPos c d e f) (d, f))
    (b, (d, f))
    (ChuParPos (ChuParPos a b c d) (b, d) e f)
    ((b, d), f)
assocParChuInv =
  ChuMorphism
    ( \q ->
        ChuParPos
          (\(x, y) -> cppForward (cppForward q x) y)
          ( \z ->
              ChuParPos
                (\x -> cppBackward (cppForward q x) z)
                (\y -> cppBackward q (y, z))
          )
    )
    (\((x, y), z) -> (x, (y, z)))
{-# INLINE assocParChuInv #-}

-- | Symmetric braiding @A ⅋ B → B ⅋ A@ over @Set@.
swapParChu ::
  ChuMorphism
    (,)
    r
    (->)
    (ChuParPos a b c d)
    (b, d)
    (ChuParPos c d a b)
    (d, b)
swapParChu =
  ChuMorphism
    (\(ChuParPos f g) -> ChuParPos g f)
    (\(x, y) -> (y, x))
{-# INLINE swapParChu #-}

-- | Object-level @!A@.
data ChuOBang (r :: Type) a = ChuOBang

instance (ChuObject r a) => ChuObject r (ChuOBang r a) where
  chuObject = bangChuObj (chuObject @r @a)

instance (ChuSeparated r a) => ChuSeparated r (ChuOBang r a)

instance (ChuObject r a) => ChuExtensional r (ChuOBang r a)

-- | Object-level @?A = (!A⊥)⊥@.
data ChuOWhyNot (r :: Type) a = ChuOWhyNot

instance (ChuObject r a) => ChuObject r (ChuOWhyNot r a) where
  chuObject = whyNotChuObj (chuObject @r @a)

instance (ChuObject r a) => ChuSeparated r (ChuOWhyNot r a)

instance (ChuExtensional r a) => ChuExtensional r (ChuOWhyNot r a)

-- | Discard @!A → I@ for 'OChu'.
discardEOChu ::
  forall r (a :: Type).
  OChu r (ChuOBang r a) (ChuOUnit r)
discardEOChu =
  OChu
    ( Chu
        ( discardBangChu ::
            ChuMorphism
              (,)
              r
              (->)
              (ChuPosType a)
              (ChuPosType a -> r)
              ()
              r
        )
    )
{-# INLINE discardEOChu #-}

-- | Dereliction @!A → A@ for 'OChu'.
derelictOChu ::
  forall r a.
  (ChuObject r a) =>
  OChu r (ChuOBang r a) a
derelictOChu = OChu (Chu (derelictChu (chuObject @r @a)))
{-# INLINE derelictOChu #-}

-- | Introduction @A → ?A@ for 'OChu'.
introduceOChu ::
  forall r a.
  (ChuObject r a) =>
  OChu r a (ChuOWhyNot r a)
introduceOChu = OChu (Chu (introduceChu (chuObject @r @a)))
{-# INLINE introduceOChu #-}

-- | Merge @?A ⅋ ?A → ?A@ for 'OChu'.
mergeEOChu ::
  forall r (a :: Type).
  OChu r (ChuOPar r (ChuOWhyNot r a) (ChuOWhyNot r a)) (ChuOWhyNot r a)
mergeEOChu =
  OChu
    ( Chu
        ( mergeWhyNotParChu ::
            ChuMorphism
              (,)
              r
              (->)
              (ChuParPos (ChuNegType a -> r) (ChuNegType a) (ChuNegType a -> r) (ChuNegType a))
              (ChuNegType a, ChuNegType a)
              (ChuNegType a -> r)
              (ChuNegType a)
        )
    )
{-# INLINE mergeEOChu #-}

-- | Unit @⊥ → ?A@ for 'OChu'.
zeroEOChu ::
  forall r (a :: Type).
  OChu r (ChuONeg r (ChuOUnit r)) (ChuOWhyNot r a)
zeroEOChu =
  OChu
    ( Chu
        ( zeroWhyNotParChu ::
            ChuMorphism
              (,)
              r
              (->)
              r
              ()
              (ChuNegType a -> r)
              (ChuNegType a)
        )
    )
{-# INLINE zeroEOChu #-}

-- | Copy @!A → !A ⊗ !A@ for 'OChu'.
copyTOChu ::
  forall r (a :: Type).
  OChu r (ChuOBang r a) (ChuOTensor r (ChuOBang r a) (ChuOBang r a))
copyTOChu =
  OChu
    ( Chu
        ( copyBangChu ::
            ChuMorphism
              (,)
              r
              (->)
              (ChuPosType a)
              (ChuPosType a -> r)
              (ChuPosType a, ChuPosType a)
              (ChuTensorNeg (ChuPosType a) (ChuPosType a -> r) (ChuPosType a) (ChuPosType a -> r))
        )
    )
{-# INLINE copyTOChu #-}

-- | Discard @!A → I@ for 'OChu'.
discardTOChu ::
  forall r (a :: Type).
  OChu r (ChuOBang r a) (ChuOUnit r)
discardTOChu =
  OChu
    ( Chu
        ( discardBangChu ::
            ChuMorphism
              (,)
              r
              (->)
              (ChuPosType a)
              (ChuPosType a -> r)
              ()
              r
        )
    )
{-# INLINE discardTOChu #-}

-- | Merge @!A ⊗ !A → !A@ for 'OChu'.
plusTOChu ::
  forall r (a :: Type).
  (Monoid (ChuPosType a)) =>
  OChu r (ChuOTensor r (ChuOBang r a) (ChuOBang r a)) (ChuOBang r a)
plusTOChu =
  OChu
    ( Chu
        ( mergeBangChu ::
            ChuMorphism
              (,)
              r
              (->)
              (ChuPosType a, ChuPosType a)
              (ChuTensorNeg (ChuPosType a) (ChuPosType a -> r) (ChuPosType a) (ChuPosType a -> r))
              (ChuPosType a)
              (ChuPosType a -> r)
        )
    )
{-# INLINE plusTOChu #-}

-- | Zero @I → !A@ for 'OChu'.
zeroTOChu ::
  forall r (a :: Type).
  (Monoid (ChuPosType a)) =>
  OChu r (ChuOUnit r) (ChuOBang r a)
zeroTOChu =
  OChu
    ( Chu
        ( zeroBangChu ::
            ChuMorphism
              (,)
              r
              (->)
              ()
              r
              (ChuPosType a)
              (ChuPosType a -> r)
        )
    )
{-# INLINE zeroTOChu #-}

-- ---------------------------------------------------------------------------
-- Embedding from 'Circuit.Ends'
-- ---------------------------------------------------------------------------

-- | Embed a symmetric end into a pointed Chu object.
--
-- A self-dual channel @Ends arr a a@ has write end @In arr a@ and read end
-- @Out arr a@.  'Circuit.Ends.close' is already the pairing
-- @In ⊗ Out → arr a a@, so the embedding is direct.  The point pair
-- @(conjoint e, companion e)@ is retained as the chosen point of the pointed
-- object.
endsAsChu ::
  Ends arr a a ->
  PointedChuObj (,) (arr a a) (->) (In arr a) (Out arr a)
endsAsChu e = PointedChuObj (ChuObj (Pre.uncurry close)) (conjoint e) (companion e)
{-# INLINE endsAsChu #-}

-- | Apply a Chu endomorphism to a symmetric end.
--
-- This is the lawful counterpart to the free 'Circuit.Ends.dimapEnds': the
-- forward and backward maps are an adjoint pair by construction of
-- 'ChuMorphism'.  The Chu law is discharged by the type, not just tested.
lawfulDimapEnds ::
  ChuMorphism (,) (arr a a) (->) (In arr a) (Out arr a) (In arr a) (Out arr a) ->
  Ends arr a a ->
  Ends arr a a
lawfulDimapEnds (ChuMorphism f g) e = Ends (f (conjoint e)) (g (companion e))
{-# INLINE lawfulDimapEnds #-}
