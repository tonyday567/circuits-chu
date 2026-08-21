{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Circuit.Boundary (Boundary (..), IsLinear, Linear (..), NotLinear, Stamped (..), isMark, isPayload)
import Circuit.Category (Category (..), id, (.), (.>))
import Circuit.Channel (Channel (..), Strength (..), Traced (..), assoc, assoc', slide, strength, trace)
import Circuit.ChannelPoly (Channel (..), commitChannel, constChannel, emitChannel, idChannel, mapChannel)
import Circuit.Chu (ChuObject (..))
import Circuit.Chu qualified as Chu
import Circuit.Dagger (Copy (..), CopyDiscard, Dagger (..), Discard (..), Merge (..), MergeZero, Zero (..), transpose)
import Circuit.Ends (Bias (..), Ends (..), HasDual (..), box, close, composeEnds0, copycat, ends, ends0, endsK, pairEnds, prefixIn, raceEnds, splay, splay0, suffixOut)
import Circuit.Ends qualified as MedState
import Circuit.FinRel
import Circuit.Fragment qualified as Frag
import Circuit.Hyper (Hyper, observe)
import Circuit.Hyper qualified as HyperLoop
import Circuit.Layer (bind, run)
import Circuit.Loop (Loop (..))
import Circuit.Mediate (Debt (..), FlushableResidual (..), LinearResidual (..), LinearityViolation (..), Mediator (..), PS (..), closeCertified, closeCertifiedWith, closeCertifiedWithBy, count, linear, medComult, medCounit, mediateLoop, mediateProcess, mediateSharedBody, mediateSharedBodyChecked, pairSum, runMediator, runMediatorState, runSharedBodyChecked)
import Circuit.Net qualified as Net
import Circuit.Poly (Dir, Eval (..), Mono, System, fromEvalSystem, lens, monoDir, monoIn, mooreSystem, runSystem, system)
import Circuit.Prob (Prob (..), embed, fromWeighted, mass, orP, parFG, parGF, score, traceE, traceEN)
import Circuit.Process (Process (..), delay, encode, fold, markSystem, register, scan, systemToProcess)
import Circuit.Tensor (Action (..), BangCopy (..), BangWeaken (..), Bot, Exponential (..), Fire (..), Lolli (..), Schedule (..), Shared (..), Tensor (..), WhyNotIntro (..), distL, distR, mix, sharedKnotBy, superpose)
import Circuit.Test.Utils (approx, check)
import Control.Arrow (Kleisli (..), runKleisli)
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.Kind (Type)
import Data.List (foldl', isInfixOf, permutations, sort, uncons)
import Data.Maybe (catMaybes, fromMaybe, isNothing)
import Data.Monoid (Any (..))
import Data.Proxy (Proxy (..))
import Data.These (These (..), these)
import Data.Tuple qualified as Tuple
import Data.Void (Void, absurd)
import GHC.TypeNats (KnownNat, natVal)
import Prelude hiding (curry, id, uncurry, (.))
import Prelude qualified as Pre

-- | Forward-only Chu interpretation: objects are Chu object tags, morphisms
-- are functions between their positive carriers via the closed 'Chu.ChuPosType'
-- family.  This is Chu's *positive projection*, not Chu itself: the backward
-- leg is discarded.
--
-- Used to test whether a Chu net can be interpreted into a traced target via
-- 'Net.bind' without requiring 'Traced' on the source category.
newtype ForwardChu (r :: Type) a b = ForwardChu (Chu.ChuPosType a -> Chu.ChuPosType b)

instance Category (ForwardChu r) where
  id = ForwardChu Pre.id
  ForwardChu g . ForwardChu f = ForwardChu (g Pre.. f)

instance Tensor (Chu.ChuOTensor r) (ForwardChu r) where
  par (ForwardChu f) (ForwardChu g) = ForwardChu (\(x, y) -> (f x, g y))
  unitl = ForwardChu (\((), a) -> a)
  unitl' = ForwardChu (\a -> ((), a))
  unitr = ForwardChu (\(a, ()) -> a)
  unitr' = ForwardChu (\a -> (a, ()))

instance Action (Chu.ChuOTensor r) (ForwardChu r) where
  swap = ForwardChu (\(a, b) -> (b, a))

instance Circuit.Channel.Channel (Chu.ChuOTensor r) (ForwardChu r) where
  assoc = ForwardChu (\((x, y), z) -> (x, (y, z)))
  assoc' = ForwardChu (\(x, (y, z)) -> ((x, y), z))
  slide = ForwardChu (\(a, (b, c)) -> (b, (a, c)))

instance Strength (Chu.ChuOTensor r) (ForwardChu r) where
  strength (ForwardChu f) = ForwardChu (\(a, b) -> (a, f b))

instance Traced (Chu.ChuOTensor r) (ForwardChu r) where
  trace (ForwardChu f) = ForwardChu (\x -> let (y, z) = f (y, x) in z)

-- | Extract the forward map from an 'OChu' morphism.
--
-- Because 'ForwardChu' uses the same closed 'Chu.ChuPosType' family as the
-- underlying 'Chu' category, no bridging coercion is needed.
forwardChu :: Chu.OChu r a b -> ForwardChu r a b
forwardChu (Chu.OChu (Chu.Chu (Chu.ChuMorphism f _))) = ForwardChu f

type F = Bool

type N1 = FinObj 1

type N2 = FinObj 2

-- ---------------------------------------------------------------------------
-- Chu helpers
-- ---------------------------------------------------------------------------

-- | Enumerate all functions from a finite domain to a finite codomain.
enumFunctions :: (Eq a) => [a] -> [b] -> [a -> b]
enumFunctions [] _ = [const (error "enumFunctions: empty domain")]
enumFunctions domain codomain = map (listToFunction domain) (sequenceA (replicate (length domain) codomain))
  where
    listToFunction dom vals x = fromMaybe (error "listToFunction: input not in domain") (lookup x (zip dom vals))

-- | Cartesian product of two lists.
enumCartesian :: [a] -> [b] -> [(a, b)]
enumCartesian xs ys = [(x, y) | x <- xs, y <- ys]

-- | List-taking tensor-negative enumeration for objects whose carriers are
-- not supplied by the 'ChuObject' class (e.g. exponentials).
chuTensorNegsExplicit ::
  (Eq r, Eq a, Eq c) =>
  [a] ->
  [b] ->
  [c] ->
  [d] ->
  Chu.ChuObj (,) r (->) a b ->
  Chu.ChuObj (,) r (->) c d ->
  [Chu.ChuTensorNeg a b c d]
chuTensorNegsExplicit as bs cs ds (Chu.ChuObj r) (Chu.ChuObj s) =
  [ Chu.ChuTensorNeg f g
  | f <- enumFunctions as ds,
    g <- enumFunctions cs bs,
    all (\(a', c') -> r (a', g c') == s (c', f a')) (enumCartesian as cs)
  ]

-- | List-taking par-positive enumeration for objects whose carriers are
-- not supplied by the 'ChuObject' class (e.g. exponentials).
chuParPossExplicit ::
  (Eq r, Eq b, Eq d) =>
  [a] ->
  [b] ->
  [c] ->
  [d] ->
  Chu.ChuObj (,) r (->) a b ->
  Chu.ChuObj (,) r (->) c d ->
  [Chu.ChuParPos a b c d]
chuParPossExplicit as bs cs ds (Chu.ChuObj r) (Chu.ChuObj s) =
  [ Chu.ChuParPos f g
  | f <- enumFunctions bs cs,
    g <- enumFunctions ds as,
    all (\(b', d') -> r (g d', b') == s (f b', d')) (enumCartesian bs ds)
  ]

-- | List-taking separation check.
chuSeparatedExplicit :: (Eq r, Eq a) => [a] -> [b] -> Chu.ChuObj (,) r (->) a b -> Bool
chuSeparatedExplicit as bs (Chu.ChuObj e) =
  all
    (\(a1, a2) -> a1 == a2 || any (\b -> e (a1, b) /= e (a2, b)) bs)
    (enumCartesian as as)

-- | List-taking extensionality check.
chuExtensionalExplicit :: (Eq r, Eq b) => [a] -> [b] -> Chu.ChuObj (,) r (->) a b -> Bool
chuExtensionalExplicit as bs (Chu.ChuObj e) =
  all
    (\(b1, b2) -> b1 == b2 || any (\a -> e (a, b1) /= e (a, b2)) as)
    (enumCartesian bs bs)

-- | Check the adjoint law for a Chu morphism between Set-based objects with
-- explicitly supplied carriers.
chuMorphismLaw ::
  (Eq r) =>
  Chu.ChuObj (,) r (->) a b ->
  Chu.ChuObj (,) r (->) c d ->
  Chu.ChuMorphism (,) r (->) a b c d ->
  [a] ->
  [d] ->
  Bool
chuMorphismLaw src tgt mor as ds =
  all (\a -> all (\d -> Chu.chuLaw src tgt mor a d) ds) as

-- | Equality of two Chu morphisms over explicit finite carrier lists.
eqChuMorphism ::
  (Eq b, Eq c) =>
  [a] ->
  [d] ->
  Chu.ChuMorphism (,) r (->) a b c d ->
  Chu.ChuMorphism (,) r (->) a b c d ->
  Bool
eqChuMorphism as ds m1 m2 =
  all (\a -> Chu.chuForward m1 a == Chu.chuForward m2 a) as
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) ds

-- | A post-shaped value for the Chu delivery oracles.  Carriers are 'Int's so
-- the example needs no 'Text'.
data ChuPost = ChuPost
  { chuFrom :: Int,
    chuTo :: [Int],
    chuBody :: Int
  }
  deriving (Eq, Show)

mkChuPost :: Int -> [Int] -> Int -> ChuPost
mkChuPost = ChuPost

-- | Prefix used to rename subscribers across a Chu morphism.
chuPrefix :: Int
chuPrefix = 10

prefixName :: Int -> Int
prefixName = (+ chuPrefix)

unprefixName :: Int -> Int
unprefixName = subtract chuPrefix

prefixTo :: [Int] -> [Int]
prefixTo = map prefixName

unprefixSub :: Int -> Int
unprefixSub = unprefixName

chuDelivers :: ChuPost -> Int -> Bool
chuDelivers p = Chu.deliversToSemiring (chuTo p)

-- | Sample Chu object over posts and names with boolean delivery pairing.
chuObjPostInt :: Chu.ChuObj (,) Bool (->) ChuPost Int
chuObjPostInt = Chu.ChuObj (Pre.uncurry chuDelivers)

-- | A tiny self-dual Chu object over @Bool@ with equality pairing.
chuTwo :: Chu.ChuObj (,) Bool (->) Bool Bool
chuTwo = Chu.ChuObj (Pre.uncurry (==))

-- | Negation as a Chu endomorphism of the self-dual @Bool@ object.
chuNot :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
chuNot = Chu.ChuMorphism not not

-- | Positive and negative carriers for the finite @chuTwo@ object.
chuTwoPos :: [Bool]
chuTwoPos = Chu.chuPosAll @Bool @Chu.ChuTwo

-- | Enumerated negative carrier of @chuTwo ⊗ chuTwo@.
chuTwoTensorNegs :: [Chu.ChuTensorNeg Bool Bool Bool Bool]
chuTwoTensorNegs = Chu.chuTensorNegs @Bool (Proxy @Chu.ChuTwo) (Proxy @Chu.ChuTwo)

-- | Enumerated positive carrier of @chuTwo ⅋ chuTwo@.
chuTwoParPoss :: [Chu.ChuParPos Bool Bool Bool Bool]
chuTwoParPoss = Chu.chuParPoss @Bool (Proxy @Chu.ChuTwo) (Proxy @Chu.ChuTwo)

-- | Unit object @I@ used in the Chu unit-law oracles.
chuUnitObjBool :: Chu.ChuObj (,) Bool (->) () Bool
chuUnitObjBool = Chu.chuUnitObj

-- | Enumerated negative carrier of @I ⊗ chuTwo@.
--
-- The unit object's negative carrier is the dualising object @Bool@, which is
-- not enumerated by 'Chu.chuNegAll', so we use the explicit list-taking helper.
chuTwoLeftUnitNegs :: [Chu.ChuTensorNeg () Bool Bool Bool]
chuTwoLeftUnitNegs = chuTensorNegsExplicit [()] [True, False] chuTwoPos chuTwoPos chuUnitObjBool chuTwo

-- | Enumerated positive carrier of @chuTwo ⊸ chuTwo@.
chuTwoLollPoss :: [Chu.ChuParPos Bool Bool Bool Bool]
chuTwoLollPoss = Chu.chuParPoss @Bool (Proxy @(Chu.ChuONeg Bool Chu.ChuTwo)) (Proxy @Chu.ChuTwo)

-- | Enumerated negative carrier of @chuTwo & chuTwo@ and positive carrier of
-- @chuTwo ⊕ chuTwo@.
chuTwoEither :: [Either Bool Bool]
chuTwoEither = map Left chuTwoPos ++ map Right chuTwoPos

-- | Enumerated negative carrier of @chuTwo ⊗ I@.
chuTwoRightUnitNegs :: [Chu.ChuTensorNeg Bool Bool () Bool]
chuTwoRightUnitNegs = chuTensorNegsExplicit chuTwoPos chuTwoPos [()] [True, False] chuTwo chuUnitObjBool

-- | Equality of Chu endomorphisms of @chuTwo@.
eqChuMorphismAA ::
  Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool ->
  Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool ->
  Bool
eqChuMorphismAA m1 m2 =
  all (\a -> Chu.chuForward m1 a == Chu.chuForward m2 a) chuTwoPos
    && all (\b -> Chu.chuBackward m1 b == Chu.chuBackward m2 b) chuTwoPos

-- | Equality of Chu endomorphisms of @I ⊗ chuTwo@.
eqChuMorphismIIA ::
  Chu.ChuMorphism (,) Bool (->) ((), Bool) (Chu.ChuTensorNeg () Bool Bool Bool) ((), Bool) (Chu.ChuTensorNeg () Bool Bool Bool) ->
  Chu.ChuMorphism (,) Bool (->) ((), Bool) (Chu.ChuTensorNeg () Bool Bool Bool) ((), Bool) (Chu.ChuTensorNeg () Bool Bool Bool) ->
  Bool
eqChuMorphismIIA m1 m2 =
  let pos2 = [((), x) | x <- chuTwoPos]
      eqTensorNeg n1 n2 =
        Chu.ctnForward n1 () == Chu.ctnForward n2 ()
          && all (\c -> Chu.ctnBackward n1 c == Chu.ctnBackward n2 c) chuTwoPos
   in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) pos2
        && all (\n -> eqTensorNeg (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoLeftUnitNegs

-- | Equality of Chu endomorphisms of @chuTwo ⊗ I@.
eqChuMorphismAII ::
  Chu.ChuMorphism (,) Bool (->) (Bool, ()) (Chu.ChuTensorNeg Bool Bool () Bool) (Bool, ()) (Chu.ChuTensorNeg Bool Bool () Bool) ->
  Chu.ChuMorphism (,) Bool (->) (Bool, ()) (Chu.ChuTensorNeg Bool Bool () Bool) (Bool, ()) (Chu.ChuTensorNeg Bool Bool () Bool) ->
  Bool
eqChuMorphismAII m1 m2 =
  let pos2 = [(x, ()) | x <- chuTwoPos]
      eqTensorNeg n1 n2 =
        all (\a -> Chu.ctnForward n1 a == Chu.ctnForward n2 a) chuTwoPos
          && Chu.ctnBackward n1 () == Chu.ctnBackward n2 ()
   in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) pos2
        && all (\n -> eqTensorNeg (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoRightUnitNegs

-- | Does @chuTwo@ admit a copy morphism @chuTwo -> chuTwo ⊗ chuTwo@?
hasCopyChuTwo :: Bool
hasCopyChuTwo =
  let tensObj = Chu.tensorChuObj chuTwo chuTwo
      negs = chuTwoTensorNegs
      ok hVals =
        all
          (\(n, hVal) -> all (\a -> Chu.chuPair tensObj ((a, a), n) == Chu.chuPair chuTwo (a, hVal)) chuTwoPos)
          (zip negs hVals)
   in any ok (sequenceA (replicate (length negs) [True, False]))

-- | Does @chuTwo@ admit a discard morphism @chuTwo -> I@?
hasDiscardChuTwo :: Bool
hasDiscardChuTwo =
  let ok gVals =
        all
          (\(k, gVal) -> all (\a -> Chu.chuPair chuUnitObjBool ((), k) == Chu.chuPair chuTwo (a, gVal)) chuTwoPos)
          (zip [True, False] gVals)
   in any ok (sequenceA (replicate 2 [True, False]))

-- | Is a finite Chu object isomorphic to its dual?
--
-- Searches all pairs of bijections between the positive and negative
-- carriers.  A self-duality isomorphism @f : A -> A^⊥@ has
-- @forward, backward : A⁺ -> A⁻@ satisfying
-- @e(p, backward n) = e(n, forward p)@ for all @p, n :: A⁺@.
isSelfDualChu ::
  forall r a.
  (Eq r, Eq (Chu.ChuPosType a), Chu.ChuObject r a) =>
  Proxy r ->
  Proxy a ->
  Bool
isSelfDualChu _ _ =
  let obj = Chu.chuObject @r @a
      poss = Chu.chuPosAll @r @a
      negs = Chu.chuNegAll @r @a
   in any
        ( \(fwd, bwd) ->
            all
              (\p -> all (\n -> Chu.chuPair obj (p, bwd n) == Chu.chuPair obj (n, fwd p)) poss)
              poss
        )
        [(fwd, bwd) | fwd <- bijections poss negs, bwd <- bijections poss negs]
  where
    bijections xs ys = [\x -> fromMaybe (error "isSelfDualChu: bijection lookup failed") (lookup x (zip xs ys')) | ys' <- permutations ys]

-- | Equality of Chu morphisms on the tensor of two @chuTwo@s.
--
-- The backward component returns a 'ChuTensorNeg', which contains functions,
-- so we compare pointwise over the finite domains.
eqTensorMorphism ::
  Chu.ChuMorphism (,) Bool (->) (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) ->
  Chu.ChuMorphism (,) Bool (->) (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) ->
  Bool
eqTensorMorphism m1 m2 =
  let pos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
      eqTensorNeg n1 n2 =
        all (\a -> Chu.ctnForward n1 a == Chu.ctnForward n2 a) chuTwoPos
          && all (\c -> Chu.ctnBackward n1 c == Chu.ctnBackward n2 c) chuTwoPos
   in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) pos2
        && all (\n -> eqTensorNeg (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoTensorNegs

-- | Extract the underlying 'ChuMorphism' from an 'OChu' arrow.
ochuToChuMorphism ::
  Chu.OChu r a b ->
  Chu.ChuMorphism (,) r (->) (Chu.ChuPosType a) (Chu.ChuNegType a) (Chu.ChuPosType b) (Chu.ChuNegType b)
ochuToChuMorphism (Chu.OChu (Chu.Chu m)) = m

-- | Class-wiring smoke test: 'zeroEOChu' for @?ChuTwo@.
_zeroEChuTwo ::
  Chu.OChu Bool (Chu.ChuONeg Bool (Chu.ChuOUnit Bool)) (Chu.ChuOWhyNot Bool Chu.ChuTwo)
_zeroEChuTwo = Chu.zeroEOChu

-- ---------------------------------------------------------------------------
-- SepChu / associator helpers
-- ---------------------------------------------------------------------------

chuTwoObjAA :: Chu.ChuObj (,) Bool (->) (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)
chuTwoObjAA = Chu.tensorChuObj chuTwo chuTwo

chuTwoObjRightAssoc ::
  Chu.ChuObj
    (,)
    Bool
    (->)
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
chuTwoObjRightAssoc = Chu.tensorChuObj chuTwo chuTwoObjAA

chuTwoObjLeftAssoc ::
  Chu.ChuObj
    (,)
    Bool
    (->)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
chuTwoObjLeftAssoc = Chu.tensorChuObj chuTwoObjAA chuTwo

chuTwoPos2 :: [(Bool, Bool)]
chuTwoPos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]

chuTwoPos3L :: [((Bool, Bool), Bool)]
chuTwoPos3L = [(p, z) | p <- chuTwoPos2, z <- chuTwoPos]

chuTwoPos3R :: [(Bool, (Bool, Bool))]
chuTwoPos3R = [(x, p) | x <- chuTwoPos, p <- chuTwoPos2]

chuTwoPos4L :: [(((Bool, Bool), Bool), Bool)]
chuTwoPos4L = [(p, w) | p <- chuTwoPos3L, w <- chuTwoPos]

chuTwoNeg3R ::
  [Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)]
chuTwoNeg3R =
  chuTensorNegsExplicit chuTwoPos chuTwoPos chuTwoPos2 chuTwoTensorNegs chuTwo chuTwoObjAA

eqTensorNeg2 ::
  Chu.ChuTensorNeg Bool Bool Bool Bool ->
  Chu.ChuTensorNeg Bool Bool Bool Bool ->
  Bool
eqTensorNeg2 n1 n2 =
  all (\a -> Chu.ctnForward n1 a == Chu.ctnForward n2 a) chuTwoPos
    && all (\c -> Chu.ctnBackward n1 c == Chu.ctnBackward n2 c) chuTwoPos

eqTensorNeg3L ::
  Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool ->
  Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool ->
  Bool
eqTensorNeg3L n1 n2 =
  all (\p -> Chu.ctnForward n1 p == Chu.ctnForward n2 p) chuTwoPos2
    && all (\z -> eqTensorNeg2 (Chu.ctnBackward n1 z) (Chu.ctnBackward n2 z)) chuTwoPos

eqTensorNeg3R ::
  Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) ->
  Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) ->
  Bool
eqTensorNeg3R n1 n2 =
  all (\a -> eqTensorNeg2 (Chu.ctnForward n1 a) (Chu.ctnForward n2 a)) chuTwoPos
    && all (\p -> Chu.ctnBackward n1 p == Chu.ctnBackward n2 p) chuTwoPos2

eqAssocMorphism ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)) ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)) ->
  Bool
eqAssocMorphism m1 m2 =
  all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) chuTwoPos3L
    && all (\n -> eqTensorNeg3L (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoNeg3R

eqEndo3R ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)) ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
    (Bool, (Bool, Bool))
    (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool)) ->
  Bool
eqEndo3R m1 m2 =
  all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) chuTwoPos3R
    && all (\n -> eqTensorNeg3R (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoNeg3R

eqEndo3L ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool) ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool) ->
  Bool

-- | Enumerated negative carrier of @(chuTwo ⊗ chuTwo) ⊗ chuTwo@.
chuTwoNeg3L ::
  [Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool]
chuTwoNeg3L =
  chuTensorNegsExplicit chuTwoPos2 chuTwoTensorNegs chuTwoPos chuTwoPos chuTwoObjAA chuTwo

eqEndo3L m1 m2 =
  all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) chuTwoPos3L
    && all (\n -> eqTensorNeg3L (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoNeg3L

chuTwoNeg4R ::
  [ Chu.ChuTensorNeg
      Bool
      Bool
      (Bool, (Bool, Bool))
      (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
  ]
chuTwoNeg4R =
  chuTensorNegsExplicit chuTwoPos chuTwoPos chuTwoPos3R chuTwoNeg3R chuTwo chuTwoObjRightAssoc

eqTensorNeg4L ::
  Chu.ChuTensorNeg
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    Bool
    Bool ->
  Chu.ChuTensorNeg
    ((Bool, Bool), Bool)
    (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
    Bool
    Bool ->
  Bool
eqTensorNeg4L n1 n2 =
  all (\p -> Chu.ctnForward n1 p == Chu.ctnForward n2 p) chuTwoPos3L
    && all (\w -> eqTensorNeg3L (Chu.ctnBackward n1 w) (Chu.ctnBackward n2 w)) chuTwoPos

eqPentagonMorphism ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (((Bool, Bool), Bool), Bool)
    ( Chu.ChuTensorNeg
        ((Bool, Bool), Bool)
        (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
        Bool
        Bool
    )
    (Bool, (Bool, (Bool, Bool)))
    ( Chu.ChuTensorNeg
        Bool
        Bool
        (Bool, (Bool, Bool))
        (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
    ) ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (((Bool, Bool), Bool), Bool)
    ( Chu.ChuTensorNeg
        ((Bool, Bool), Bool)
        (Chu.ChuTensorNeg (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool) Bool Bool)
        Bool
        Bool
    )
    (Bool, (Bool, (Bool, Bool)))
    ( Chu.ChuTensorNeg
        Bool
        Bool
        (Bool, (Bool, Bool))
        (Chu.ChuTensorNeg Bool Bool (Bool, Bool) (Chu.ChuTensorNeg Bool Bool Bool Bool))
    ) ->
  Bool
eqPentagonMorphism m1 m2 =
  all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) chuTwoPos4L
    && all (\n -> eqTensorNeg4L (Chu.chuBackward m1 n) (Chu.chuBackward m2 n)) chuTwoNeg4R

-- | Equality of morphisms @ChuTwo ⊗ I → ChuTwo@.
eqChuTwoUnitr ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, ())
    (Chu.ChuTensorNeg Bool Bool () Bool)
    Bool
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, ())
    (Chu.ChuTensorNeg Bool Bool () Bool)
    Bool
    Bool ->
  Bool
eqChuTwoUnitr m1 m2 =
  let pos = [(x, ()) | x <- chuTwoPos]
      eqN n1 n2 =
        all (\a -> Chu.ctnForward n1 a == Chu.ctnForward n2 a) chuTwoPos
          && Chu.ctnBackward n1 () == Chu.ctnBackward n2 ()
   in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) pos
        && all (\b -> eqN (Chu.chuBackward m1 b) (Chu.chuBackward m2 b)) chuTwoPos

eqTensorNegLolli ::
  Chu.ChuTensorNeg Bool Bool (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) ->
  Chu.ChuTensorNeg Bool Bool (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) ->
  Bool
eqTensorNegLolli n1 n2 =
  all (\a -> Chu.ctnForward n1 a == Chu.ctnForward n2 a) chuTwoPos
    && all (\m -> Chu.ctnBackward n1 m == Chu.ctnBackward n2 m) chuTwoLollPoss

eqChuMorphismLolliEval ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, Chu.ChuParPos Bool Bool Bool Bool)
    (Chu.ChuTensorNeg Bool Bool (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool))
    Bool
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Bool, Chu.ChuParPos Bool Bool Bool Bool)
    (Chu.ChuTensorNeg Bool Bool (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool))
    Bool
    Bool ->
  Bool
eqChuMorphismLolliEval m1 m2 =
  let poss = [(a, m) | a <- chuTwoPos, m <- chuTwoLollPoss]
   in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) poss
        && all (\d -> eqTensorNegLolli (Chu.chuBackward m1 d) (Chu.chuBackward m2 d)) chuTwoPos

chuTwoFuns :: [Bool -> Bool]
chuTwoFuns = Chu.chuFunctionals chuTwoPos [True, False]

-- | Positive carrier and functionals for the @Any@-based Chu object.
chuAnyPos :: [Any]
chuAnyPos = Chu.chuPosAll @Bool @Chu.ChuAny

chuAnyFuns :: [Any -> Bool]
chuAnyFuns = Chu.chuFunctionals chuAnyPos [True, False]

eqFun :: (Bool -> Bool) -> (Bool -> Bool) -> Bool
eqFun f g = all (\a -> f a == g a) chuTwoPos

-- | Chu morphisms @I → A@ for a Set-based object with finite carriers.
iHoms ::
  (Eq r) =>
  [a] ->
  [b] ->
  Chu.ChuObj (,) r (->) a b ->
  [Chu.ChuMorphism (,) r (->) () r a b]
iHoms as bs obj =
  [ m
  | a <- as,
    let m = Chu.ChuMorphism (const a) (\d -> Chu.chuPair obj (a, d)),
    all (\d -> Chu.chuLaw Chu.chuUnitObj obj m () d) bs
  ]

iHomsChuTwo ::
  Chu.ChuObj (,) Bool (->) a b ->
  [a] ->
  [b] ->
  [Chu.ChuMorphism (,) Bool (->) () Bool a b]
iHomsChuTwo obj as bs = iHoms as bs obj

composeITo ::
  Chu.ChuMorphism (,) Bool (->) a b c d ->
  Chu.ChuMorphism (,) Bool (->) () Bool a b ->
  Chu.ChuMorphism (,) Bool (->) () Bool c d
composeITo = Chu.composeChu

eqIToTwo ::
  Chu.ChuMorphism (,) Bool (->) () Bool Bool Bool ->
  Chu.ChuMorphism (,) Bool (->) () Bool Bool Bool ->
  Bool
eqIToTwo m1 m2 =
  Chu.chuForward m1 () == Chu.chuForward m2 ()
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

eqIToWhy ::
  Chu.ChuMorphism (,) Bool (->) () Bool (Bool -> Bool) Bool ->
  Chu.ChuMorphism (,) Bool (->) () Bool (Bool -> Bool) Bool ->
  Bool
eqIToWhy m1 m2 =
  eqFun (Chu.chuForward m1 ()) (Chu.chuForward m2 ())
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

whyNotTwo :: Chu.ChuObj (,) Bool (->) (Bool -> Bool) Bool
whyNotTwo = Chu.whyNotChuObj chuTwo

whyNotTwoParPoss :: [Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool]
whyNotTwoParPoss =
  chuParPossExplicit chuTwoFuns chuTwoPos chuTwoFuns chuTwoPos whyNotTwo whyNotTwo

eqWhyParPos ::
  Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool ->
  Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool ->
  Bool
eqWhyParPos p1 p2 =
  all (\b -> eqFun (Chu.cppForward p1 b) (Chu.cppForward p2 b)) chuTwoPos
    && all (\d -> eqFun (Chu.cppBackward p1 d) (Chu.cppBackward p2 d)) chuTwoPos

eqMergeWhy ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
    (Bool, Bool)
    (Bool -> Bool)
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
    (Bool, Bool)
    (Bool -> Bool)
    Bool ->
  Bool
eqMergeWhy m1 m2 =
  all (\p -> eqFun (Chu.chuForward m1 p) (Chu.chuForward m2 p)) whyNotTwoParPoss
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

botWhyParPoss :: [Chu.ChuParPos Bool () (Bool -> Bool) Bool]
botWhyParPoss =
  chuParPossExplicit [True, False] [()] chuTwoFuns chuTwoPos Chu.chuBottomObj whyNotTwo

eqLeftUnitWhy ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos Bool () (Bool -> Bool) Bool)
    ((), Bool)
    (Bool -> Bool)
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos Bool () (Bool -> Bool) Bool)
    ((), Bool)
    (Bool -> Bool)
    Bool ->
  Bool
eqLeftUnitWhy m1 m2 =
  all (\p -> eqFun (Chu.chuForward m1 p) (Chu.chuForward m2 p)) botWhyParPoss
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

whyBotParPoss :: [Chu.ChuParPos (Bool -> Bool) Bool Bool ()]
whyBotParPoss =
  chuParPossExplicit chuTwoFuns chuTwoPos [True, False] [()] whyNotTwo Chu.chuBottomObj

eqRightUnitWhy ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos (Bool -> Bool) Bool Bool ())
    (Bool, ())
    (Bool -> Bool)
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    (Chu.ChuParPos (Bool -> Bool) Bool Bool ())
    (Bool, ())
    (Bool -> Bool)
    Bool ->
  Bool
eqRightUnitWhy m1 m2 =
  all (\p -> eqFun (Chu.chuForward m1 p) (Chu.chuForward m2 p)) whyBotParPoss
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

eqWhyParPos3 ::
  Chu.ChuParPos
    (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
    (Bool, Bool)
    (Bool -> Bool)
    Bool ->
  Chu.ChuParPos
    (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
    (Bool, Bool)
    (Bool -> Bool)
    Bool ->
  Bool
eqWhyParPos3 p1 p2 =
  let pos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
   in all (\xy -> eqFun (Chu.cppForward p1 xy) (Chu.cppForward p2 xy)) pos2
        && all (\z -> eqWhyParPos (Chu.cppBackward p1 z) (Chu.cppBackward p2 z)) chuTwoPos

whyNotTwoPar3LPoss ::
  [ Chu.ChuParPos
      (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
      (Bool, Bool)
      (Bool -> Bool)
      Bool
  ]
whyNotTwoPar3LPoss =
  chuParPossExplicit
    whyNotTwoParPoss
    [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
    chuTwoFuns
    chuTwoPos
    (Chu.parChuObj whyNotTwo whyNotTwo)
    whyNotTwo

eqAssocWhyL ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ( Chu.ChuParPos
        (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
        (Bool, Bool)
        (Bool -> Bool)
        Bool
    )
    ((Bool, Bool), Bool)
    ( Chu.ChuParPos
        (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
        (Bool, Bool)
        (Bool -> Bool)
        Bool
    )
    ((Bool, Bool), Bool) ->
  Bool
eqAssocWhyL m =
  let negs = [((x, y), z) | x <- chuTwoPos, y <- chuTwoPos, z <- chuTwoPos]
   in all (\p -> eqWhyParPos3 (Chu.chuForward m p) p) whyNotTwoPar3LPoss
        && all (\n -> Chu.chuBackward m n == n) negs

eqWhy3ToWhy ::
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ( Chu.ChuParPos
        (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
        (Bool, Bool)
        (Bool -> Bool)
        Bool
    )
    ((Bool, Bool), Bool)
    (Bool -> Bool)
    Bool ->
  Chu.ChuMorphism
    (,)
    Bool
    (->)
    ( Chu.ChuParPos
        (Chu.ChuParPos (Bool -> Bool) Bool (Bool -> Bool) Bool)
        (Bool, Bool)
        (Bool -> Bool)
        Bool
    )
    ((Bool, Bool), Bool)
    (Bool -> Bool)
    Bool ->
  Bool
eqWhy3ToWhy m1 m2 =
  all (\p -> eqFun (Chu.chuForward m1 p) (Chu.chuForward m2 p)) whyNotTwoPar3LPoss
    && all (\d -> Chu.chuBackward m1 d == Chu.chuBackward m2 d) chuTwoPos

-- | Equality of Chu morphisms on the par of two @chuTwo@s.
--
-- The forward component returns a 'ChuParPos', which contains functions, so we
-- compare pointwise over the finite domains.
eqParMorphism ::
  Chu.ChuMorphism (,) Bool (->) (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) ->
  Chu.ChuMorphism (,) Bool (->) (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) (Chu.ChuParPos Bool Bool Bool Bool) (Bool, Bool) ->
  Bool
eqParMorphism m1 m2 =
  let neg2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
      eqParPos p1 p2 =
        all (\b -> Chu.cppForward p1 b == Chu.cppForward p2 b) chuTwoPos
          && all (\d -> Chu.cppBackward p1 d == Chu.cppBackward p2 d) chuTwoPos
   in all (\p -> eqParPos (Chu.chuForward m1 p) (Chu.chuForward m2 p)) chuTwoParPoss
        && all (\n -> Chu.chuBackward m1 n == Chu.chuBackward m2 n) neg2

-- | Generic forward-only equality of Chu morphisms.
--
-- In the separated-extensional subcategory the backward component is uniquely
-- determined by the forward component, so comparing forward values over the
-- positive carrier is enough.
eqChuMorphismForward ::
  (Eq p') =>
  [p] ->
  Chu.ChuMorphism (,) r (->) p n p' n' ->
  Chu.ChuMorphism (,) r (->) p n p' n' ->
  Bool
eqChuMorphismForward ps m1 m2 =
  all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) ps

-- | ChuThree: canonical object and finite carriers.
chuThreeObj :: Chu.ChuObj (,) Bool (->) (Maybe Bool) (Maybe Bool)
chuThreeObj = Chu.chuObject @Bool @Chu.ChuThree

chuThreePos :: [Maybe Bool]
chuThreePos = Chu.chuPosAll @Bool @Chu.ChuThree

chuThreeNeg :: [Maybe Bool]
chuThreeNeg = Chu.chuNegAll @Bool @Chu.ChuThree

chuThreePos2 :: [(Maybe Bool, Maybe Bool)]
chuThreePos2 = [(x, y) | x <- chuThreePos, y <- chuThreePos]

chuThreePos3L :: [((Maybe Bool, Maybe Bool), Maybe Bool)]
chuThreePos3L = [(p, z) | p <- chuThreePos2, z <- chuThreePos]

chuThreePos3R :: [(Maybe Bool, (Maybe Bool, Maybe Bool))]
chuThreePos3R = [(x, p) | x <- chuThreePos, p <- chuThreePos2]

chuThreePos4L :: [(((Maybe Bool, Maybe Bool), Maybe Bool), Maybe Bool)]
chuThreePos4L = [(p, w) | p <- chuThreePos3L, w <- chuThreePos]

-- | ChuDouble01: canonical object and finite carriers.
chuDouble01Obj :: Chu.ChuObj (,) Double (->) Bool Bool
chuDouble01Obj = Chu.chuObject @Double @Chu.ChuDouble01

chuDouble01Pos :: [Bool]
chuDouble01Pos = Chu.chuPosAll @Double @Chu.ChuDouble01

chuDouble01Neg :: [Bool]
chuDouble01Neg = Chu.chuNegAll @Double @Chu.ChuDouble01

-- | ChuDelivery: canonical object and finite carriers.
chuDeliveryObj :: Chu.ChuObj (,) Bool (->) Bool Bool
chuDeliveryObj = Chu.chuObject @Bool @Chu.ChuDelivery

chuDeliveryPos :: [Bool]
chuDeliveryPos = Chu.chuPosAll @Bool @Chu.ChuDelivery

chuDeliveryNeg :: [Bool]
chuDeliveryNeg = Chu.chuNegAll @Bool @Chu.ChuDelivery

-- | Forward-only unit-law oracle for an 'OChu' object.
checkChuUnitlForward ::
  forall r (a :: Type).
  (Eq (Chu.ChuPosType a), Chu.ChuSeparated r a) =>
  Proxy r ->
  Proxy a ->
  String ->
  IO Bool
checkChuUnitlForward _ _ name =
  let pos = Chu.chuPosAll @r @a
      psI = [((), x) | x <- pos]
      u :: Chu.OChu r (Chu.ChuOTensor r (Chu.ChuOUnit r) a) a
      u = Chu.unitlOChu
      u' :: Chu.OChu r a (Chu.ChuOTensor r (Chu.ChuOUnit r) a)
      u' = Chu.unitlOChu'
      idA = id :: Chu.OChu r a a
      idIA = id :: Chu.OChu r (Chu.ChuOTensor r (Chu.ChuOUnit r) a) (Chu.ChuOTensor r (Chu.ChuOUnit r) a)
   in check name $
        eqChuMorphismForward pos (ochuToChuMorphism (u . u')) (ochuToChuMorphism idA)
          && eqChuMorphismForward psI (ochuToChuMorphism (u' . u)) (ochuToChuMorphism idIA)

-- | Forward-only right unit-law oracle for an 'OChu' object.
checkChuUnitrForward ::
  forall r (a :: Type).
  (Eq (Chu.ChuPosType a), Chu.ChuSeparated r a) =>
  Proxy r ->
  Proxy a ->
  String ->
  IO Bool
checkChuUnitrForward _ _ name =
  let pos = Chu.chuPosAll @r @a
      psI = [(x, ()) | x <- pos]
      u :: Chu.OChu r (Chu.ChuOTensor r a (Chu.ChuOUnit r)) a
      u = Chu.unitrOChu
      u' :: Chu.OChu r a (Chu.ChuOTensor r a (Chu.ChuOUnit r))
      u' = Chu.unitrOChu'
      idA = id :: Chu.OChu r a a
      idAI = id :: Chu.OChu r (Chu.ChuOTensor r a (Chu.ChuOUnit r)) (Chu.ChuOTensor r a (Chu.ChuOUnit r))
   in check name $
        eqChuMorphismForward pos (ochuToChuMorphism (u . u')) (ochuToChuMorphism idA)
          && eqChuMorphismForward psI (ochuToChuMorphism (u' . u)) (ochuToChuMorphism idAI)

-- | Forward-only associator inverse oracle for an 'OChu' object.
checkChuAssocInversesForward ::
  forall r (a :: Type).
  (Eq r, Eq (Chu.ChuPosType a), Chu.ChuSeparated r a) =>
  Proxy r ->
  Proxy a ->
  String ->
  IO Bool
checkChuAssocInversesForward _ _ name =
  let pos3L = Chu.chuPosAll @r @(Chu.ChuOTensor r (Chu.ChuOTensor r a a) a)
      pos3R = Chu.chuPosAll @r @(Chu.ChuOTensor r a (Chu.ChuOTensor r a a))
      isoL =
        assoc' . assoc ::
          Chu.OChu
            r
            (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a)
            (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a)
      isoR =
        assoc . assoc' ::
          Chu.OChu
            r
            (Chu.ChuOTensor r a (Chu.ChuOTensor r a a))
            (Chu.ChuOTensor r a (Chu.ChuOTensor r a a))
      idL = id :: Chu.OChu r (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a) (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a)
      idR = id :: Chu.OChu r (Chu.ChuOTensor r a (Chu.ChuOTensor r a a)) (Chu.ChuOTensor r a (Chu.ChuOTensor r a a))
   in check name $
        eqChuMorphismForward pos3L (ochuToChuMorphism isoL) (ochuToChuMorphism idL)
          && eqChuMorphismForward pos3R (ochuToChuMorphism isoR) (ochuToChuMorphism idR)

-- | Forward-only pentagon oracle for an 'OChu' object.
checkChuPentagonForward ::
  forall r (a :: Type).
  (Eq r, Eq (Chu.ChuPosType a), Chu.ChuSeparated r a) =>
  Proxy r ->
  Proxy a ->
  String ->
  IO Bool
checkChuPentagonForward _ _ name =
  let pos = Chu.chuPosAll @r @a
      pos4 = [(p, w) | p <- [(q, z) | q <- [(x, y) | x <- pos, y <- pos], z <- pos], w <- pos]
      assoc1 ::
        Chu.OChu
          r
          (Chu.ChuOTensor r (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a) a)
          (Chu.ChuOTensor r (Chu.ChuOTensor r a a) (Chu.ChuOTensor r a a))
      assoc1 = assoc
      assoc2 ::
        Chu.OChu
          r
          (Chu.ChuOTensor r (Chu.ChuOTensor r a a) (Chu.ChuOTensor r a a))
          (Chu.ChuOTensor r a (Chu.ChuOTensor r a (Chu.ChuOTensor r a a)))
      assoc2 = assoc
      assocInner ::
        Chu.OChu
          r
          (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a)
          (Chu.ChuOTensor r a (Chu.ChuOTensor r a a))
      assocInner = assoc
      lhs = assoc2 . assoc1
      bot1 =
        Chu.parOChu assocInner id ::
          Chu.OChu
            r
            (Chu.ChuOTensor r (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a) a)
            (Chu.ChuOTensor r (Chu.ChuOTensor r a (Chu.ChuOTensor r a a)) a)
      bot2 =
        assoc ::
          Chu.OChu
            r
            (Chu.ChuOTensor r (Chu.ChuOTensor r a (Chu.ChuOTensor r a a)) a)
            (Chu.ChuOTensor r a (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a))
      bot3 =
        Chu.parOChu id assocInner ::
          Chu.OChu
            r
            (Chu.ChuOTensor r a (Chu.ChuOTensor r (Chu.ChuOTensor r a a) a))
            (Chu.ChuOTensor r a (Chu.ChuOTensor r a (Chu.ChuOTensor r a a)))
      rhs = bot3 . bot2 . bot1
   in check name $ eqChuMorphismForward pos4 (ochuToChuMorphism lhs) (ochuToChuMorphism rhs)

main :: IO ()
main = do
  results <-
    sequence
      [ -- copy/discard comonoid laws
        -- Chu construction
        check "Chu is a base arrow: id and composition typecheck" $
          let cid :: Chu.Chu (,) Bool (->) (Chu.ChuObj (,) Bool (->) Int Int) (Chu.ChuObj (,) Bool (->) Int Int)
              cid = Chu.Chu (Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Int Int Int Int)
              ccompose = cid . cid
           in case ccompose of
                Chu.Chu (Chu.ChuMorphism f g) -> f 0 == 0 && g 0 == 0,
        check "Chu negation is involutive" $
          let e :: (Int, Int) -> Bool
              e (x, y) = x == y
              obj = Chu.ChuObj e
              obj'' = Chu.negateChu (Chu.negateChu obj)
           in all (\p -> Chu.chuPair obj p == Chu.chuPair obj'' p) [(x, y) | x <- [0 .. 2 :: Int], y <- [0 .. 2 :: Int]],
        check "Chu adjoint law holds for lawful prefix pair" $
          let domainAgents = [1, 2] :: [Int]
              codomainAgents = map prefixName domainAgents
              posts =
                [ mkChuPost 0 [r] 0
                | r <- domainAgents
                ]
                  ++ [mkChuPost 0 [1, 2] 0, mkChuPost 0 [] 0]
              subs = codomainAgents
              fwd p = p {chuTo = prefixTo (chuTo p)}
              bwd = unprefixSub
           in all (\p -> all (Chu.chuLaw chuObjPostInt chuObjPostInt (Chu.ChuMorphism fwd bwd) p) subs) posts,
        check "Chu adjoint law fails for unlawful backward map" $
          let posts = [mkChuPost 0 [1] 0 :: ChuPost]
              subs = [prefixName 1]
              fwd p = p {chuTo = prefixTo (chuTo p)}
              bwd = id
           in not (all (\p -> all (Chu.chuLaw chuObjPostInt chuObjPostInt (Chu.ChuMorphism fwd bwd) p) subs) posts),
        check "Chu tensor and par have different shapes over Bool" $
          let pos = chuTwoPos
              pos2 = [(x, y) | x <- pos, y <- pos]
              tensNegs = Chu.chuTensorNegs @Bool (Proxy @Chu.ChuTwo) (Proxy @Chu.ChuTwo)
              parPoss = Chu.chuParPoss @Bool (Proxy @Chu.ChuTwo) (Proxy @Chu.ChuTwo)
           in length tensNegs == 2
                && length parPoss == 2
                && (length pos2, length tensNegs) /= (length parPoss, length pos2),
        check "Chu Bool self-dual object is separated and extensional" $
          Chu.chuSeparated @Bool (Proxy @Chu.ChuTwo) && Chu.chuExtensional @Bool (Proxy @Chu.ChuTwo),
        check "Chu tensor preserves identity" $
          let idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              tId = Chu.tensorChu idC idC
           in eqTensorMorphism tId Chu.idChu,
        check "Chu tensor preserves composition" $
          let idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              lhs = Chu.tensorChu (Chu.composeChu chuNot chuNot) idC
              rhs = Chu.composeChu (Chu.tensorChu chuNot idC) (Chu.tensorChu chuNot idC)
           in eqTensorMorphism lhs rhs,
        check "Chu tensor morphism satisfies adjoint law" $
          let tObj = Chu.tensorChuObj chuTwo chuTwo
              tMor = Chu.tensorChu chuNot idC
              idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              pos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
           in all (\p -> all (\n -> Chu.chuLaw tObj tObj tMor p n) chuTwoTensorNegs) pos2,
        check "Chu par preserves identity" $
          let idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              pId = Chu.parChu idC idC
           in eqParMorphism pId Chu.idChu,
        check "Chu par preserves composition" $
          let idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              lhs = Chu.parChu (Chu.composeChu chuNot chuNot) idC
              rhs = Chu.composeChu (Chu.parChu chuNot idC) (Chu.parChu chuNot idC)
           in eqParMorphism lhs rhs,
        check "Chu left unitor satisfies adjoint law" $
          let iObj = Chu.tensorChuObj chuUnitObjBool chuTwo
              mor = Chu.leftUnitorChu chuTwo
              pos2 = [((), x) | x <- chuTwoPos]
           in all (\p -> all (\b -> Chu.chuLaw iObj chuTwo mor p b) chuTwoPos) pos2,
        check "Chu left unitor is inverse on A" $
          let iso = Chu.composeChu (Chu.leftUnitorChu chuTwo) (Chu.leftUnitorChuInv chuTwo)
           in eqChuMorphismAA iso Chu.idChu,
        check "Chu left unitor inverse is inverse on I ⊗ A" $
          let iso = Chu.composeChu (Chu.leftUnitorChuInv chuTwo) (Chu.leftUnitorChu chuTwo)
           in eqChuMorphismIIA iso Chu.idChu,
        check "Chu right unitor satisfies adjoint law" $
          let iObj = Chu.tensorChuObj chuTwo chuUnitObjBool
              mor = Chu.rightUnitorChu chuTwo
              pos2 = [(x, ()) | x <- chuTwoPos]
           in all (\p -> all (\b -> Chu.chuLaw iObj chuTwo mor p b) chuTwoPos) pos2,
        check "Chu right unitor is inverse on A" $
          let iso = Chu.composeChu (Chu.rightUnitorChu chuTwo) (Chu.rightUnitorChuInv chuTwo)
           in eqChuMorphismAA iso Chu.idChu,
        check "Chu right unitor inverse is inverse on A ⊗ I" $
          let iso = Chu.composeChu (Chu.rightUnitorChuInv chuTwo) (Chu.rightUnitorChu chuTwo)
           in eqChuMorphismAII iso Chu.idChu,
        check "Chu implication object differs from compact A⊥ ⊗ B" $
          let lollPoss = Chu.chuParPoss @Bool (Proxy @(Chu.ChuONeg Bool Chu.ChuTwo)) (Proxy @Chu.ChuTwo)
              compactNegs = Chu.chuTensorNegs @Bool (Proxy @(Chu.ChuONeg Bool Chu.ChuTwo)) (Proxy @Chu.ChuTwo)
              compactPos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
           in length lollPoss == 2
                && length compactNegs == 2
                && (length compactPos2, length compactNegs) /= (length lollPoss, length compactPos2),
        check "Chu chuTwo has no copy morphism to chuTwo ⊗ chuTwo" $
          not hasCopyChuTwo,
        check "Chu chuTwo has no discard morphism to I" $
          not hasDiscardChuTwo,
        check "Chu additive conjunction has distinct shape" $
          let pos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
           in length pos2 == 4
                && length chuTwoEither == 4
                && (length pos2, length chuTwoEither) /= (length pos2, length chuTwoTensorNegs)
                && (length pos2, length chuTwoEither) /= (length chuTwoLollPoss, length pos2),
        check "Chu additive disjunction has distinct shape" $
          let pos2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
              neg2 = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
           in length chuTwoEither == 4
                && length neg2 == 4
                && (length chuTwoEither, length neg2) /= (length pos2, length chuTwoTensorNegs)
                && (length chuTwoEither, length neg2) /= (length chuTwoLollPoss, length pos2),
        check "Chu top and zero have expected shapes" $
          let emptyV = [] :: [Void]
           in length [()] == 1 && null emptyV && null emptyV,
        check "Chu additive tags have expected shapes" $
          let withPos = Chu.chuPosAll @Bool @(Chu.ChuOWith Bool Chu.ChuTwo Chu.ChuTwo)
              withNeg = Chu.chuNegAll @Bool @(Chu.ChuOWith Bool Chu.ChuTwo Chu.ChuTwo)
              plusPos = Chu.chuPosAll @Bool @(Chu.ChuOPlus Bool Chu.ChuTwo Chu.ChuTwo)
              plusNeg = Chu.chuNegAll @Bool @(Chu.ChuOPlus Bool Chu.ChuTwo Chu.ChuTwo)
              topPos = Chu.chuPosAll @Bool @(Chu.ChuOTop Bool)
              topNeg = Chu.chuNegAll @Bool @(Chu.ChuOTop Bool)
              zeroPos = Chu.chuPosAll @Bool @(Chu.ChuOZero Bool)
              zeroNeg = Chu.chuNegAll @Bool @(Chu.ChuOZero Bool)
           in length withPos == 4
                && length withNeg == 4
                && length plusPos == 4
                && length plusNeg == 4
                && length topPos == 1
                && length topNeg == 0
                && length zeroPos == 0
                && length zeroNeg == 1,
        check "Chu additive & and ⊕ on ChuTwo are separated and extensional" $
          Chu.chuSeparated @Bool (Proxy @(Chu.ChuOWith Bool Chu.ChuTwo Chu.ChuTwo))
            && Chu.chuExtensional @Bool (Proxy @(Chu.ChuOWith Bool Chu.ChuTwo Chu.ChuTwo))
            && Chu.chuSeparated @Bool (Proxy @(Chu.ChuOPlus Bool Chu.ChuTwo Chu.ChuTwo))
            && Chu.chuExtensional @Bool (Proxy @(Chu.ChuOPlus Bool Chu.ChuTwo Chu.ChuTwo)),
        check "Chu additive ⊤ and 0 are separated and extensional" $
          Chu.chuSeparated @Bool (Proxy @(Chu.ChuOTop Bool))
            && Chu.chuExtensional @Bool (Proxy @(Chu.ChuOTop Bool))
            && Chu.chuSeparated @Bool (Proxy @(Chu.ChuOZero Bool))
            && Chu.chuExtensional @Bool (Proxy @(Chu.ChuOZero Bool)),
        check "Chu additive A & 0 is not extensional (empty-carrier blocker)" $
          not (Chu.chuExtensional @Bool (Proxy @(Chu.ChuOWith Bool Chu.ChuTwo (Chu.ChuOZero Bool)))),
        check "Chu additive ⊤ ⊕ ⊤ is not separated (empty-carrier blocker)" $
          not (Chu.chuSeparated @Bool (Proxy @(Chu.ChuOPlus Bool (Chu.ChuOTop Bool) (Chu.ChuOTop Bool)))),
        check "Chu additive ChuTwo & ChuTwo is an OChu object" $
          let _ = id :: Chu.OChu Bool (Chu.ChuOWith Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOWith Bool Chu.ChuTwo Chu.ChuTwo)
           in True,
        check "Chu additive ChuTwo ⊕ ChuTwo is an OChu object" $
          let _ = id :: Chu.OChu Bool (Chu.ChuOPlus Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOPlus Bool Chu.ChuTwo Chu.ChuTwo)
           in True,
        check "Chu projection A & B → A is a Chu morphism" $
          let src = Chu.withChuObj chuTwo chuTwo
              tgt = chuTwo
           in chuMorphismLaw src tgt Chu.proj1Chu chuTwoPos2 chuTwoPos,
        check "Chu projection A & B → B is a Chu morphism" $
          let src = Chu.withChuObj chuTwo chuTwo
              tgt = chuTwo
           in chuMorphismLaw src tgt Chu.proj2Chu chuTwoPos2 chuTwoPos,
        check "Chu injection A → A ⊕ B is a Chu morphism" $
          let src = chuTwo
              tgt = Chu.oplusChuObj chuTwo chuTwo
              neg = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
           in chuMorphismLaw src tgt Chu.inj1Chu chuTwoPos neg,
        check "Chu injection B → A ⊕ B is a Chu morphism" $
          let src = chuTwo
              tgt = Chu.oplusChuObj chuTwo chuTwo
              neg = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
           in chuMorphismLaw src tgt Chu.inj2Chu chuTwoPos neg,
        check "Chu A → ⊤ is a Chu morphism" $
          chuMorphismLaw chuTwo Chu.topChuObj Chu.unitTopChu chuTwoPos [],
        check "Chu 0 → A is a Chu morphism" $
          chuMorphismLaw Chu.zeroChuObj chuTwo Chu.unitZeroChu [] chuTwoPos,
        check "Chu pair(f,g) composed with projections recovers f and g" $
          let withObj = Chu.withChuObj chuTwo chuTwo
              pairFG = Chu.pairChu chuNot Chu.idChu
              lhs1 = Chu.composeChu Chu.proj1Chu pairFG
              lhs2 = Chu.composeChu Chu.proj2Chu pairFG
           in chuMorphismLaw chuTwo withObj pairFG chuTwoPos (map Left chuTwoPos ++ map Right chuTwoPos)
                && eqChuMorphism chuTwoPos chuTwoPos lhs1 chuNot
                && eqChuMorphism chuTwoPos chuTwoPos lhs2 Chu.idChu,
        check "Chu copair(f,g) composed with injections recovers f and g" $
          let plusObj = Chu.oplusChuObj chuTwo chuTwo
              copairFG = Chu.copairChu chuNot Chu.idChu
              lhs1 = Chu.composeChu copairFG Chu.inj1Chu
              lhs2 = Chu.composeChu copairFG Chu.inj2Chu
           in chuMorphismLaw plusObj chuTwo copairFG chuTwoEither chuTwoPos
                && eqChuMorphism chuTwoPos chuTwoPos lhs1 chuNot
                && eqChuMorphism chuTwoPos chuTwoPos lhs2 Chu.idChu,
        check "Chu A & ⊤ is isomorphic to A" $
          let topRNegs = map Left chuTwoPos
              topRPos = [(x, ()) | x <- chuTwoPos]
              iso = Chu.composeChu Chu.withTopRInvChu Chu.withTopRChu
              iso' = Chu.composeChu Chu.withTopRChu Chu.withTopRInvChu
           in eqChuMorphism chuTwoPos chuTwoPos iso Chu.idChu
                && eqChuMorphism topRPos topRNegs iso' (Chu.idChu :: Chu.ChuMorphism (,) Bool (->) (Bool, ()) (Either Bool Void) (Bool, ()) (Either Bool Void)),
        check "Chu ⊤ & A is isomorphic to A" $
          let topLNegs = map Right chuTwoPos
              topLPos = [((), x) | x <- chuTwoPos]
              iso = Chu.composeChu Chu.withTopLInvChu Chu.withTopLChu
              iso' = Chu.composeChu Chu.withTopLChu Chu.withTopLInvChu
           in eqChuMorphism chuTwoPos chuTwoPos iso Chu.idChu
                && eqChuMorphism topLPos topLNegs iso' (Chu.idChu :: Chu.ChuMorphism (,) Bool (->) ((), Bool) (Either Void Bool) ((), Bool) (Either Void Bool)),
        check "Chu 0 ⊕ A is isomorphic to A" $
          let plusLNegs = [((), x) | x <- chuTwoPos]
              plusLPos = map Right chuTwoPos
              iso = Chu.composeChu Chu.zeroPlusLInvChu Chu.zeroPlusLChu
              iso' = Chu.composeChu Chu.zeroPlusLChu Chu.zeroPlusLInvChu
           in eqChuMorphism chuTwoPos chuTwoPos iso Chu.idChu
                && eqChuMorphism plusLPos plusLNegs iso' (Chu.idChu :: Chu.ChuMorphism (,) Bool (->) (Either Void Bool) ((), Bool) (Either Void Bool) ((), Bool)),
        check "Chu A ⊕ 0 is isomorphic to A" $
          let plusRNegs = [(x, ()) | x <- chuTwoPos]
              plusRPos = map Left chuTwoPos
              iso = Chu.composeChu Chu.zeroPlusRInvChu Chu.zeroPlusRChu
              iso' = Chu.composeChu Chu.zeroPlusRChu Chu.zeroPlusRInvChu
           in eqChuMorphism chuTwoPos chuTwoPos iso Chu.idChu
                && eqChuMorphism plusRPos plusRNegs iso' (Chu.idChu :: Chu.ChuMorphism (,) Bool (->) (Either Bool Void) (Bool, ()) (Either Bool Void) (Bool, ())),
        check "Chu evaluation satisfies adjoint law" $
          let src = Chu.tensorChuObj chuTwo (Chu.lolliChuObj chuTwo chuTwo)
              mor = Chu.evalChu chuTwo chuTwo
              poss = [(a, m) | a <- chuTwoPos, m <- chuTwoLollPoss]
           in all (\p -> all (\d -> Chu.chuLaw src chuTwo mor p d) chuTwoPos) poss,
        check "Chu delivery matrix commutes with prefix morphism (Bool)" $
          let domainAgents = [1, 2] :: [Int]
              codomainAgents = map prefixName domainAgents
              posts = [mkChuPost 0 [1] 0, mkChuPost 0 [1, 2] 0, mkChuPost 0 [2] 0, mkChuPost 0 [] 0]
              domainMat = Chu.deliveryMatrix domainAgents (map chuTo posts) :: [[Bool]]
              codomainMat = Chu.deliveryMatrix codomainAgents (map (prefixTo . chuTo) posts) :: [[Bool]]
           in domainMat == codomainMat,
        check "Chu delivery matrix commutes with prefix morphism (Double)" $
          let domainAgents = [1, 2] :: [Int]
              codomainAgents = map prefixName domainAgents
              posts = [mkChuPost 0 [1, 2] 0, mkChuPost 0 [] 0]
              domainMat = Chu.deliveryMatrix domainAgents (map chuTo posts) :: [[Double]]
              codomainMat = Chu.deliveryMatrix codomainAgents (map (prefixTo . chuTo) posts) :: [[Double]]
           in domainMat == codomainMat,
        check "Chu prefix without backward rename breaks matrix equality" $
          let domainAgents = [1, 2] :: [Int]
              posts = [mkChuPost 0 [1] 0]
              domainMat = Chu.deliveryMatrix domainAgents (map chuTo posts) :: [[Bool]]
              forwardOnlyMat = Chu.deliveryMatrix domainAgents (map (prefixTo . chuTo) posts) :: [[Bool]]
           in domainMat /= forwardOnlyMat,
        -- Coherence: Loop/Dagger transpose and Chu negation on embedded Ends
        check "copycat witness is fixed by Chu negation and Dagger transpose" $
          let e :: Ends (->) () ()
              e = copycat
              chu = Chu.pointedObj (Chu.endsAsChu e)
              chuNeg = Chu.negateChu chu
              d = Dagger id id :: Dagger (->) () ()
           in Chu.chuPair chu (conjoint e, companion e) () == Chu.chuPair chuNeg (companion e, conjoint e) ()
                && (let Dagger f g = transpose d in f () == () && g () == ()),
        check "constant self-map witness is fixed by Chu negation and Dagger transpose" $
          let e :: Ends (->) Int Int
              e = ends0 (const ()) (const 42)
              chu = Chu.pointedObj (Chu.endsAsChu e)
              chuNeg = Chu.negateChu chu
              d = Dagger (const 42) (const 42) :: Dagger (->) Int Int
           in Chu.chuPair chu (conjoint e, companion e) 0 == Chu.chuPair chuNeg (companion e, conjoint e) 0
                && (let Dagger f g = transpose d in f 0 == 42 && g 0 == 42),
        -- Object-indexed Chu category (OChu) constrained combinators
        check "OChu left unitor round-trips on ChuTwo" $
          let u :: Chu.OChu Bool (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo) Chu.ChuTwo
              u = Chu.unitlOChu
              u' :: Chu.OChu Bool Chu.ChuTwo (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo)
              u' = Chu.unitlOChu'
           in eqChuMorphismAA (ochuToChuMorphism (u . u')) Chu.idChu,
        check "OChu left unitor inverse round-trips on I ⊗ ChuTwo" $
          let t :: Chu.OChu Bool (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo) (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo)
              t = id
              u :: Chu.OChu Bool (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo) Chu.ChuTwo
              u = Chu.unitlOChu
              u' :: Chu.OChu Bool Chu.ChuTwo (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) Chu.ChuTwo)
              u' = Chu.unitlOChu'
           in eqChuMorphismIIA (ochuToChuMorphism (u' . u)) (ochuToChuMorphism t),
        check "OChu right unitor round-trips on ChuTwo" $
          let u :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool)) Chu.ChuTwo
              u = Chu.unitrOChu
              u' :: Chu.OChu Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool))
              u' = Chu.unitrOChu'
           in eqChuMorphismAA (ochuToChuMorphism (u . u')) Chu.idChu,
        check "OChu right unitor inverse round-trips on ChuTwo ⊗ I" $
          let t :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool)) (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool))
              t = id
              u :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool)) Chu.ChuTwo
              u = Chu.unitrOChu
              u' :: Chu.OChu Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool))
              u' = Chu.unitrOChu'
           in eqChuMorphismAII (ochuToChuMorphism (u' . u)) (ochuToChuMorphism t),
        check "OChu par preserves identity on ChuTwo ⊗ ChuTwo" $
          let idChuTwo = id :: Chu.OChu Bool Chu.ChuTwo Chu.ChuTwo
              idT = id :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
              p = Chu.parOChu idChuTwo idChuTwo :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
           in eqTensorMorphism (ochuToChuMorphism p) (ochuToChuMorphism idT),
        check "OChu swap is involutive on ChuTwo ⊗ ChuTwo" $
          let s :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
              s = Chu.swapOChu
              idT = id :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
           in eqTensorMorphism (ochuToChuMorphism (s . s)) (ochuToChuMorphism idT),
        -- SepChu: double negation, associator, pentagon
        check "SepChu ChuTwo is separated and extensional" $
          Chu.chuSeparated @Bool (Proxy @Chu.ChuTwo)
            && Chu.chuExtensional @Bool (Proxy @Chu.ChuTwo),
        check "SepChu double negation is iso on ChuTwo" $
          let eta = Chu.dnUnitChu @Bool @Chu.ChuTwo
              eps = Chu.dnCounitChu @Bool @Chu.ChuTwo
           in eqChuMorphismAA (ochuToChuMorphism (eps . eta)) Chu.idChu
                && eqChuMorphismAA (ochuToChuMorphism (eta . eps)) Chu.idChu,
        check "SepChu associator satisfies adjoint law on ChuTwo" $
          all
            (\p -> all (\n -> Chu.chuLaw chuTwoObjLeftAssoc chuTwoObjRightAssoc Chu.assocChu p n) chuTwoNeg3R)
            chuTwoPos3L,
        check "SepChu associator is inverse on (ChuTwo ⊗ ChuTwo) ⊗ ChuTwo" $
          let iso = Chu.composeChu Chu.assocChuInv Chu.assocChu
           in eqEndo3L iso Chu.idChu,
        check "SepChu associator inverse is inverse on ChuTwo ⊗ (ChuTwo ⊗ ChuTwo)" $
          let iso = Chu.composeChu Chu.assocChu Chu.assocChuInv
           in eqEndo3R iso Chu.idChu,
        check "SepChu Channel assoc agrees with assocChu on ChuTwo" $
          let a ::
                Chu.OChu
                  Bool
                  (Chu.ChuOTensor Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) Chu.ChuTwo)
                  (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
              a = assoc
           in eqAssocMorphism (ochuToChuMorphism a) Chu.assocChu,
        check "SepChu slide agrees with assoc . par swap id . assoc' on ChuTwo" $
          let sl ::
                Chu.OChu
                  Bool
                  (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                  (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
              sl = slide
              derived =
                assoc
                  . Chu.parOChu Chu.swapOChu id
                  . assoc' ::
                  Chu.OChu
                    Bool
                    (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                    (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
           in eqEndo3R (ochuToChuMorphism sl) (ochuToChuMorphism derived),
        check "SepChu associator pentagon commutes on ChuTwo" $
          let top1 ::
                Chu.OChu
                  Bool
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) Chu.ChuTwo)
                      Chu.ChuTwo
                  )
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
                      (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
                  )
              top1 = assoc
              top2 ::
                Chu.OChu
                  Bool
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
                      (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo)
                  )
                  ( Chu.ChuOTensor
                      Bool
                      Chu.ChuTwo
                      (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                  )
              top2 = assoc
              bot1 ::
                Chu.OChu
                  Bool
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) Chu.ChuTwo)
                      Chu.ChuTwo
                  )
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                      Chu.ChuTwo
                  )
              bot1 = Chu.parOChu assoc id
              bot2 ::
                Chu.OChu
                  Bool
                  ( Chu.ChuOTensor
                      Bool
                      (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                      Chu.ChuTwo
                  )
                  ( Chu.ChuOTensor
                      Bool
                      Chu.ChuTwo
                      (Chu.ChuOTensor Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) Chu.ChuTwo)
                  )
              bot2 = assoc
              bot3 ::
                Chu.OChu
                  Bool
                  ( Chu.ChuOTensor
                      Bool
                      Chu.ChuTwo
                      (Chu.ChuOTensor Bool (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo) Chu.ChuTwo)
                  )
                  ( Chu.ChuOTensor
                      Bool
                      Chu.ChuTwo
                      (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOTensor Bool Chu.ChuTwo Chu.ChuTwo))
                  )
              bot3 = Chu.parOChu id assoc
           in eqPentagonMorphism (ochuToChuMorphism (top2 . top1)) (ochuToChuMorphism (bot3 . bot2 . bot1)),
        -- ChuThree: self-dual zoo member (total order is self-dual by reversal)
        check "SepChu ChuThree is separated and extensional" $
          Chu.chuSeparated @Bool (Proxy @Chu.ChuThree)
            && Chu.chuExtensional @Bool (Proxy @Chu.ChuThree),
        check "SepChu ChuThree is self-dual" $
          isSelfDualChu (Proxy @Bool) (Proxy @Chu.ChuThree),
        checkChuUnitlForward (Proxy @Bool) (Proxy @Chu.ChuThree) "OChu left unitor round-trips on ChuThree",
        checkChuUnitrForward (Proxy @Bool) (Proxy @Chu.ChuThree) "OChu right unitor round-trips on ChuThree",
        checkChuAssocInversesForward
          (Proxy @Bool)
          (Proxy @Chu.ChuThree)
          "SepChu associator is inverse on ChuThree",
        -- ChuDouble01: genuinely non-self-dual finite Double-semiring zoo member
        check "SepChu ChuDouble01 is separated and extensional" $
          Chu.chuSeparated @Double (Proxy @Chu.ChuDouble01)
            && Chu.chuExtensional @Double (Proxy @Chu.ChuDouble01),
        check "SepChu ChuDouble01 is not self-dual" $
          not (isSelfDualChu (Proxy @Double) (Proxy @Chu.ChuDouble01)),
        checkChuAssocInversesForward
          (Proxy @Double)
          (Proxy @Chu.ChuDouble01)
          "SepChu associator is inverse on ChuDouble01",
        checkChuPentagonForward (Proxy @Double) (Proxy @Chu.ChuDouble01) "SepChu associator pentagon commutes on ChuDouble01",
        -- ChuDelivery: self-dual delivery-matrix zoo member
        check "SepChu ChuDelivery is separated and extensional" $
          Chu.chuSeparated @Bool (Proxy @Chu.ChuDelivery)
            && Chu.chuExtensional @Bool (Proxy @Chu.ChuDelivery),
        check "SepChu ChuDelivery is self-dual" $
          isSelfDualChu (Proxy @Bool) (Proxy @Chu.ChuDelivery),
        checkChuAssocInversesForward
          (Proxy @Bool)
          (Proxy @Chu.ChuDelivery)
          "SepChu associator is inverse on ChuDelivery",
        checkChuPentagonForward (Proxy @Bool) (Proxy @Chu.ChuDelivery) "SepChu associator pentagon commutes on ChuDelivery",
        -- Lolli: internal hom
        check "Lolli (->) curry/uncurry are inverse" $
          let f (x, y) = x + y :: Int
              g x y = x * y :: Int
           in uncurry @(,) @(->) (curry @(,) @(->) f) (3, 4) == f (3, 4)
                && curry @(,) @(->) (uncurry @(,) @(->) g) 3 4 == g 3 4,
        check "Lolli (->) eval is application" $
          eval @(,) @(->) (3 :: Int, (+ 1)) == 4,
        check "Lolli (->) eval is uncurry id . swap" $
          let apply (x, f) = eval @(,) @(->) (x, f) :: Int
              derived = uncurry @(,) @(->) id . swap
           in apply (3, (* 2)) == derived (3, (* 2)),
        check "Lolli OChu implication shape is (2, 4) not compact (4, 2)" $
          let lollPoss = chuTwoLollPoss
              compactPos = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
              compactNegs = Chu.chuTensorNegs @Bool (Proxy @(Chu.ChuONeg Bool Chu.ChuTwo)) (Proxy @Chu.ChuTwo)
           in (length lollPoss, length compactPos) == (2, 4)
                && (length compactPos, length compactNegs) == (4, 2),
        check "Lolli OChu curry/uncurry are inverse on right unitor" $
          let u :: Chu.OChu Bool (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOUnit Bool)) Chu.ChuTwo
              u = Chu.unitrOChu
              recovered = Chu.uncurryOChu (Chu.curryOChu u)
           in eqChuTwoUnitr (ochuToChuMorphism recovered) (ochuToChuMorphism u),
        check "Lolli OChu eval agrees with evalChu on ChuTwo" $
          let evL ::
                Chu.OChu
                  Bool
                  (Chu.ChuOTensor Bool Chu.ChuTwo (Chu.ChuOLolli Bool Chu.ChuTwo Chu.ChuTwo))
                  Chu.ChuTwo
              evL = Chu.evalOChu
           in eqChuMorphismLolliEval (ochuToChuMorphism evL) (Chu.evalChu chuTwo chuTwo),
        -- Exponentials
        check "Exponential (->) !A is A" $
          derelict @(,) @(->) (7 :: Int) == 7
            && copyE @(,) @(->) (7 :: Int) == (7, 7)
            && discardE @(,) @(->) (7 :: Int) == (),
        check "Exponential (->) ?A is the free list monoid" $
          introduce @(,) @(->) (7 :: Int) == [7]
            && introduce @(,) @(->) (7 :: Int) ++ introduce @(,) @(->) (8 :: Int) == [7, 8],
        check "Exponential OChu !ChuTwo exists and is separated-extensional" $
          let bangObj = Chu.bangChuObj chuTwo
              funs = chuTwoFuns
              ext =
                all
                  ( \(f, g) ->
                      eqFun f g
                        || any (\a -> Chu.chuPair bangObj (a, f) /= Chu.chuPair bangObj (a, g)) chuTwoPos
                  )
                  [(f, g) | f <- funs, g <- funs]
           in chuSeparatedExplicit chuTwoPos funs bangObj
                && ext
                && length funs == 4,
        check "Exponential OChu copy/discard are a comonoid on !ChuTwo" $
          let bangObj = Chu.bangChuObj chuTwo
              tensObj = Chu.tensorChuObj bangObj bangObj
              iLeft = Chu.tensorChuObj Chu.chuUnitObj bangObj
              iRight = Chu.tensorChuObj bangObj Chu.chuUnitObj
              copyM = Chu.copyBangChu
              discM = Chu.discardBangChu
              pos = chuTwoPos
              funs = chuTwoFuns
              tensNegs = chuTensorNegsExplicit pos funs pos funs bangObj bangObj
              leftNegs = chuTensorNegsExplicit [()] [True, False] pos funs Chu.chuUnitObj bangObj
              rightNegs = chuTensorNegsExplicit pos funs [()] [True, False] bangObj Chu.chuUnitObj
              leftCounit = Chu.composeChu (Chu.tensorChu discM Chu.idChu) copyM
              rightCounit = Chu.composeChu (Chu.tensorChu Chu.idChu discM) copyM
           in all (\a -> all (\n -> Chu.chuLaw bangObj tensObj copyM a n) tensNegs) pos
                && all (\a -> all (\k -> Chu.chuLaw bangObj Chu.chuUnitObj discM a k) [True, False]) pos
                && all (\a -> Chu.chuForward copyM a == (a, a) && Chu.chuForward discM a == ()) pos
                && all (\a -> Chu.chuForward leftCounit a == ((), a)) pos
                && all (\a -> Chu.chuForward rightCounit a == (a, ())) pos
                && all (\a -> all (\n -> Chu.chuLaw bangObj iLeft leftCounit a n) leftNegs) pos
                && all (\a -> all (\n -> Chu.chuLaw bangObj iRight rightCounit a n) rightNegs) pos,
        check "Exponential OChu derelict !ChuTwo -> ChuTwo is a Chu morphism" $
          let bangObj = Chu.bangChuObj chuTwo
              mor = Chu.derelictChu chuTwo
           in all (\a -> all (\d -> Chu.chuLaw bangObj chuTwo mor a d) chuTwoPos) chuTwoPos
                && all (\a -> Chu.chuForward mor a == a) chuTwoPos,
        check "Exponential OChu derelict is the unique I-point bijection" $
          let bangObj = Chu.bangChuObj chuTwo
              toBang = iHomsChuTwo bangObj chuTwoPos chuTwoFuns
              toTwo = iHomsChuTwo chuTwo chuTwoPos chuTwoPos
           in length toBang == 2
                && length toTwo == 2
                && all
                  ( \m ->
                      any (\n -> eqIToTwo (composeITo (Chu.derelictChu chuTwo) m) n) toTwo
                  )
                  toBang,
        check "Exponential OChu Hom(I, ?ChuTwo) is the functionals" $
          let why = Chu.whyNotChuObj chuTwo
           in length (iHomsChuTwo why chuTwoFuns chuTwoPos) == 4,
        check "Exponential OChu introduce is injective on I-points" $
          let toA = iHomsChuTwo chuTwo chuTwoPos chuTwoPos
              via = fmap (composeITo (Chu.introduceChu chuTwo)) toA
           in case via of
                [m1, m2] -> not (eqIToWhy m1 m2)
                _ -> False,
        check "Exponential OChu pointwise ?-merge is not a tensor morphism" $
          let cand d = Chu.ChuTensorNeg (const d) (const d)
              bilinear n =
                all
                  ( \(f, g) ->
                      f (Chu.ctnBackward n g) == g (Chu.ctnForward n f)
                  )
                  [(f, g) | f <- chuTwoFuns, g <- chuTwoFuns]
           in not (all (\d -> bilinear (cand d)) chuTwoPos),
        check "Exponential OChu merge ?A ⅋ ?A -> ?A is a Chu morphism" $
          let parObj = Chu.parChuObj whyNotTwo whyNotTwo
              mor = Chu.mergeWhyNotParChu
           in all
                (\p -> all (\d -> Chu.chuLaw parObj whyNotTwo mor p d) chuTwoPos)
                whyNotTwoParPoss,
        check "Exponential OChu ⅋-unit ⊥ -> ?A is a Chu morphism" $
          let mor = Chu.zeroWhyNotParChu
           in all
                (\k -> all (\d -> Chu.chuLaw Chu.chuBottomObj whyNotTwo mor k d) chuTwoPos)
                [True, False],
        check "Exponential OChu ⅋-monoid left unit on ?ChuTwo" $
          let via =
                Chu.composeChu
                  Chu.mergeWhyNotParChu
                  (Chu.parChu Chu.zeroWhyNotParChu Chu.idChu)
           in eqLeftUnitWhy via Chu.leftUnitorParChu,
        check "Exponential OChu ⅋-monoid right unit on ?ChuTwo" $
          let via =
                Chu.composeChu
                  Chu.mergeWhyNotParChu
                  (Chu.parChu Chu.idChu Chu.zeroWhyNotParChu)
           in eqRightUnitWhy via Chu.rightUnitorParChu,
        check "Exponential OChu ⅋-monoid is commutative on ?ChuTwo" $
          let via = Chu.composeChu Chu.mergeWhyNotParChu Chu.swapParChu
           in eqMergeWhy via Chu.mergeWhyNotParChu,
        check "Exponential OChu ⅋-associator is inverse on ?ChuTwo" $
          eqAssocWhyL (Chu.composeChu Chu.assocParChuInv Chu.assocParChu),
        check "Exponential OChu ⅋-monoid is associative on ?ChuTwo" $
          let lhs =
                Chu.composeChu
                  Chu.mergeWhyNotParChu
                  ( Chu.composeChu
                      (Chu.parChu Chu.idChu Chu.mergeWhyNotParChu)
                      Chu.assocParChu
                  )
              rhs =
                Chu.composeChu
                  Chu.mergeWhyNotParChu
                  (Chu.parChu Chu.mergeWhyNotParChu Chu.idChu)
           in eqWhy3ToWhy lhs rhs,
        check "Exponential OChu introduce ChuTwo -> ?ChuTwo is a Chu morphism" $
          let why = Chu.whyNotChuObj chuTwo
              mor = Chu.introduceChu chuTwo
           in all (\a -> all (\d -> Chu.chuLaw chuTwo why mor a d) chuTwoPos) chuTwoPos,
        check "Exponential OChu zero I -> ?ChuTwo is a Chu morphism" $
          let why = Chu.whyNotChuObj chuTwo
              mor = Chu.zeroWhyNotChu
           in all (\d -> Chu.chuLaw Chu.chuUnitObj why mor () d) chuTwoPos,
        check "Exponential OChu digging is the identity on !ChuTwo" $
          let mor :: Chu.ChuMorphism (,) Bool (->) Bool (Bool -> Bool) Bool (Bool -> Bool)
              mor = Chu.digChu
           in all (\a -> Chu.chuForward mor a == Chu.chuForward Chu.idChu a) chuTwoPos
                && all (\f -> all (\a -> Chu.chuBackward mor f a == Chu.chuBackward Chu.idChu f a) chuTwoPos) chuTwoFuns,
        check "Exponential OChu promotion !A tensor !B -> !(A & B) is a Chu morphism" $
          let bangA = Chu.bangChuObj chuTwo
              bangB = Chu.bangChuObj chuTwo
              src = Chu.tensorChuObj bangA bangB
              tgt = Chu.bangChuObj (Chu.withChuObj chuTwo chuTwo)
              pos = [(x, y) | x <- chuTwoPos, y <- chuTwoPos]
              negs = enumFunctions (enumCartesian chuTwoPos chuTwoPos) [True, False]
           in all (\p -> all (\n -> Chu.chuLaw src tgt Chu.promoteChu p n) negs) pos
                && all (\p -> Chu.chuForward Chu.promoteChu p == p) pos,
        -- Class wiring: OChu constrained combinators for par, copy/discard/merge/zero
        check "OChu parP id id agrees with parChu id id on ChuTwo" $
          let idC = Chu.idChu :: Chu.ChuMorphism (,) Bool (->) Bool Bool Bool Bool
              viaClass = Chu.parPOChu (Chu.OChu (Chu.Chu idC)) (Chu.OChu (Chu.Chu idC)) :: Chu.OChu Bool (Chu.ChuOPar Bool Chu.ChuTwo Chu.ChuTwo) (Chu.ChuOPar Bool Chu.ChuTwo Chu.ChuTwo)
           in eqParMorphism (ochuToChuMorphism viaClass) (Chu.parChu idC idC),
        check "OChu copyE agrees with copyBangChu on !ChuTwo" $
          let bangObj = Chu.bangChuObj chuTwo
              viaClass :: Chu.OChu Bool (Chu.ChuOBang Bool Chu.ChuTwo) (Chu.ChuOTensor Bool (Chu.ChuOBang Bool Chu.ChuTwo) (Chu.ChuOBang Bool Chu.ChuTwo))
              viaClass = Chu.copyTOChu
              tensNegs = chuTensorNegsExplicit chuTwoPos chuTwoFuns chuTwoPos chuTwoFuns bangObj bangObj
              m1 = ochuToChuMorphism viaClass
              m2 = Chu.copyBangChu
           in all (\a -> Chu.chuForward m1 a == Chu.chuForward m2 a) chuTwoPos
                && all (\n -> all (\a -> Chu.chuBackward m1 n a == Chu.chuBackward m2 n a) chuTwoPos) tensNegs,
        check "OChu discardE agrees with discardBangChu on !ChuTwo" $
          let viaClass :: Chu.OChu Bool (Chu.ChuOBang Bool Chu.ChuTwo) (Chu.ChuOUnit Bool)
              viaClass = Chu.discardEOChu
              m1 = ochuToChuMorphism viaClass
              m2 = Chu.discardBangChu
           in all (\a -> Chu.chuForward m1 a == Chu.chuForward m2 a) chuTwoPos
                && all (\k -> all (\a -> Chu.chuBackward m1 k a == Chu.chuBackward m2 k a) chuTwoPos) [True, False],
        check "OChu copyT agrees with copyBangChu on !ChuTwo" $
          let bangObj = Chu.bangChuObj chuTwo
              viaClass :: Chu.OChu Bool (Chu.ChuOBang Bool Chu.ChuTwo) (Chu.ChuOTensor Bool (Chu.ChuOBang Bool Chu.ChuTwo) (Chu.ChuOBang Bool Chu.ChuTwo))
              viaClass = Chu.copyTOChu
              tensNegs = chuTensorNegsExplicit chuTwoPos chuTwoFuns chuTwoPos chuTwoFuns bangObj bangObj
              m1 = ochuToChuMorphism viaClass
              m2 = Chu.copyBangChu
           in all (\a -> Chu.chuForward m1 a == Chu.chuForward m2 a) chuTwoPos
                && all (\n -> all (\a -> Chu.chuBackward m1 n a == Chu.chuBackward m2 n a) chuTwoPos) tensNegs,
        check "OChu discardT agrees with discardBangChu on !ChuTwo" $
          let viaClass :: Chu.OChu Bool (Chu.ChuOBang Bool Chu.ChuTwo) (Chu.ChuOUnit Bool)
              viaClass = Chu.discardTOChu
              m1 = ochuToChuMorphism viaClass
              m2 = Chu.discardBangChu
           in all (\a -> Chu.chuForward m1 a == Chu.chuForward m2 a) chuTwoPos
                && all (\k -> all (\a -> Chu.chuBackward m1 k a == Chu.chuBackward m2 k a) chuTwoPos) [True, False],
        check "OChu plusT agrees with mergeBangChu on !ChuAny" $
          let viaClass :: Chu.OChu Bool (Chu.ChuOTensor Bool (Chu.ChuOBang Bool Chu.ChuAny) (Chu.ChuOBang Bool Chu.ChuAny)) (Chu.ChuOBang Bool Chu.ChuAny)
              viaClass = Chu.plusTOChu
              m1 = ochuToChuMorphism viaClass
              m2 = Chu.mergeBangChu
              eqAnyFun f g = all (\x -> f x == g x) chuAnyPos
              eqAnyTensorNeg n1 n2 =
                all (\x -> eqAnyFun (Chu.ctnForward n1 x) (Chu.ctnForward n2 x)) chuAnyPos
                  && all (\x -> eqAnyFun (Chu.ctnBackward n1 x) (Chu.ctnBackward n2 x)) chuAnyPos
           in all (\p -> Chu.chuForward m1 p == Chu.chuForward m2 p) (enumCartesian chuAnyPos chuAnyPos)
                && all (\k -> eqAnyTensorNeg (Chu.chuBackward m1 k) (Chu.chuBackward m2 k)) chuAnyFuns,
        check "OChu zeroT agrees with zeroBangChu on !ChuAny" $
          let viaClass :: Chu.OChu Bool (Chu.ChuOUnit Bool) (Chu.ChuOBang Bool Chu.ChuAny)
              viaClass = Chu.zeroTOChu
              m1 = ochuToChuMorphism viaClass
              m2 = Chu.zeroBangChu
           in Chu.chuForward m1 () == Chu.chuForward m2 ()
                && all (\k -> Chu.chuBackward m1 k == Chu.chuBackward m2 k) chuAnyFuns,
        check "Chu mergeBangChu satisfies adjoint law on !ChuAny" $
          let bangObj = Chu.bangChuObj (Chu.chuObject @Bool @Chu.ChuAny)
              src = Chu.tensorChuObj bangObj bangObj
              tgt = bangObj
              pos = enumCartesian chuAnyPos chuAnyPos
           in all (\p -> all (\k -> Chu.chuLaw src tgt Chu.mergeBangChu p k) chuAnyFuns) pos,
        check "Chu zeroBangChu satisfies adjoint law on !ChuAny" $
          let bangObj = Chu.bangChuObj (Chu.chuObject @Bool @Chu.ChuAny)
              src = Chu.chuUnitObj
              tgt = bangObj
           in all (\k -> Chu.chuLaw src tgt Chu.zeroBangChu () k) chuAnyFuns,
        check "OChu WhyNotMonoid ?ChuTwo object shapes are inhabited" $
          let _ = undefined :: Chu.OChu Bool (Chu.ChuOPar Bool (Chu.ChuOWhyNot Bool Chu.ChuTwo) (Chu.ChuOWhyNot Bool Chu.ChuTwo)) (Chu.ChuOWhyNot Bool Chu.ChuTwo)
              _ = Chu.OChu (Chu.Chu Chu.zeroWhyNotParChu) :: Chu.OChu Bool (Chu.ChuONeg Bool (Chu.ChuOUnit Bool)) (Chu.ChuOWhyNot Bool Chu.ChuTwo)
           in True,
        -- Net wiring over Chu: the tensor-generic Net accepts ChuOTensor as
        -- its wiring product.  Without constrained class instances for OChu,
        -- the bimonoid rows are supplied as explicit 'Net.lift' morphisms on
        -- the unit object.
        check "Net ChuOTensor ChuOUnit bimonoid rows typecheck" $
          let copyN :: Net.Net (Chu.ChuOTensor Bool) (Chu.OChu Bool) (Chu.ChuOUnit Bool) (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) (Chu.ChuOUnit Bool))
              copyN = Net.lift Chu.unitlOChu'
              plusN :: Net.Net (Chu.ChuOTensor Bool) (Chu.OChu Bool) (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) (Chu.ChuOUnit Bool)) (Chu.ChuOUnit Bool)
              plusN = Net.lift Chu.unitlOChu
              _composed = plusN . copyN :: Net.Net (Chu.ChuOTensor Bool) (Chu.OChu Bool) (Chu.ChuOUnit Bool) (Chu.ChuOUnit Bool)
           in True,
        -- First falsifier of traced-ochu: a Chu net can be interpreted via
        -- 'Net.bind' into a traced target category without needing 'Traced'
        -- on the source.  ForwardChu uses a closed carrier family so GHC can
        -- reduce 'ChuOTensor' carriers in polymorphic instance methods.
        check "Net.bind interprets Chu net into ForwardChu" $
          let copyN :: Net.Net (Chu.ChuOTensor Bool) (Chu.OChu Bool) (Chu.ChuOUnit Bool) (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) (Chu.ChuOUnit Bool))
              copyN = Net.lift Chu.unitlOChu'
              composedN :: Net.Net (Chu.ChuOTensor Bool) (Chu.OChu Bool) (Chu.ChuOUnit Bool) (Chu.ChuOUnit Bool)
              composedN = Net.lift Chu.unitlOChu . Net.lift Chu.unitlOChu'
              copyViaBind :: ForwardChu Bool (Chu.ChuOUnit Bool) (Chu.ChuOTensor Bool (Chu.ChuOUnit Bool) (Chu.ChuOUnit Bool))
              copyViaBind = bind forwardChu copyN
              composedViaBind :: ForwardChu Bool (Chu.ChuOUnit Bool) (Chu.ChuOUnit Bool)
              composedViaBind = bind forwardChu composedN
              ForwardChu copyF = copyViaBind
              ForwardChu composedF = composedViaBind
           in copyF () == ((), ()) && composedF () == ()
      ]
  if and results
    then putStrLn "\nAll tests passed."
    else error "Some tests failed."
