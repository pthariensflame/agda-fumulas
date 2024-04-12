------------------------------------------------------------------------
-- Algebraic structures of fumulas (not bundled).
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`, unless
-- you want to parameterise it via the equality relation and/or the ternary
-- operator.

open import Relation.Binary.Core using (Rel)
open import Algebra.Fumula.Core using (Op₃)

module Algebra.Fumula.Structures
  {a ℓ} {A : Set a}  -- The underlying set
  (_≈_ : Rel A ℓ)    -- The underlying equality relation
  (_⤙_⤚_ : Op₃ A)   -- The core ternary operator
  where

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Level using (_⊔_)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
open import Algebra.Fumula.Definitions _≈_ _⤙_⤚_
open import Algebra.Fumula.Bundles.Raw

record IsAlmostFumula : Set (a ⊔ ℓ) where
  field
    isEquivalence      : IsEquivalence _≈_
    cong            : Congruent₃
    double-exchange : MiddleNestedDoubleExchange
    

  open IsEquivalence isEquivalence public

  setoid : Setoid a ℓ
  setoid = record { isEquivalence = isEquivalence }

  rawAlmostFumula : RawAlmostFumula a ℓ
  rawAlmostFumula = record
    { _≈_ = _≈_
    ; _⤙_⤚_ = _⤙_⤚_
    }

record IsReversibleAlmostFumula : Set (a ⊔ ℓ) where
  field
    isAlmostFumula : IsAlmostFumula
    outer-commute : OuterCommutative

  open IsAlmostFumula isAlmostFumula public

record IsFumula (■ : A) : Set (a ⊔ ℓ) where
  field
    isAlmostFumula : IsAlmostFumula

  open IsAlmostFumula isAlmostFumula public

  rawFumula : RawFumula a ℓ
  rawFumula = record
    { _≈_ = _≈_
    ; _⤙_⤚_ = _⤙_⤚_
    ; ■ = ■
    }

  open RawFumula rawFumula
    using (◆; ●)

  field
    ■-outer-commute : _OuterCommutativeWith_ ■
    ■-collapse-dup : (∀ x → (■ ⤙ x ⤚ x) ≈ ◆) × (∀ x → (x ⤙ x ⤚ ■) ≈ ◆)
    ◆-outer-commute : _OuterCommutativeWith_ ◆
    ◆-collapse-middle : (∀ x z → (◆ ⤙ z ⤚ x) ≈ z) × (∀ x z → (x ⤙ z ⤚ ◆) ≈ z)
    ●-outer-commute : _OuterCommutativeWith_ ●
    ●-inner-commute : _InnerCommutativeWith_ ●
    ●-◆-collapse-side : (∀ x → (● ⤙ ◆ ⤚ x) ≈ x) × (∀ x → (x ⤙ ◆ ⤚ ●) ≈ x)

  ■-collapse-dupˡ : ∀ x → (■ ⤙ x ⤚ x) ≈ ◆
  ■-collapse-dupˡ = proj₁ ■-collapse-dup

  ■-collapse-dupʳ : ∀ x → (x ⤙ x ⤚ ■) ≈ ◆
  ■-collapse-dupʳ = proj₂ ■-collapse-dup

  ◆-collapse-middleˡ : ∀ x z → (◆ ⤙ z ⤚ x) ≈ z
  ◆-collapse-middleˡ = proj₁ ◆-collapse-middle

  ◆-collapse-middleʳ : ∀ x z → (x ⤙ z ⤚ ◆) ≈ z
  ◆-collapse-middleʳ = proj₂ ◆-collapse-middle

  ●-inner-commuteˡ : _LeftInnerCommutativeWith_ ●
  ●-inner-commuteˡ = proj₁ ●-inner-commute

  ●-inner-commuteʳ : _RightInnerCommutativeWith_ ●
  ●-inner-commuteʳ = proj₂ ●-inner-commute

  ●-◆-collapse-sideˡ : ∀ x → (● ⤙ ◆ ⤚ x) ≈ x
  ●-◆-collapse-sideˡ = proj₁ ●-◆-collapse-side

  ●-◆-collapse-sideʳ : ∀ x → (x ⤙ ◆ ⤚ ●) ≈ x
  ●-◆-collapse-sideʳ = proj₂ ●-◆-collapse-side

  field
    ◆-outer-associate : _OuterAssociativeWith_ ◆
    ◆-pullout : _PulloutWith_ ◆

  ◆-pulloutˡ : _LeftPulloutWith_ ◆
  ◆-pulloutˡ = proj₁ ◆-pullout

  ◆-pulloutʳ : _RightPulloutWith_ ◆
  ◆-pulloutʳ = proj₂ ◆-pullout

record IsReversibleFumula (■ : A) : Set (a ⊔ ℓ) where
  field
    isFumula         : IsFumula ■
    outer-commute : OuterCommutative

  open IsFumula isFumula public

  isReversibleAlmostFumula : IsReversibleAlmostFumula
  isReversibleAlmostFumula = record
    { isAlmostFumula = isAlmostFumula
    ; outer-commute = outer-commute
    }
  -- no new symbols to publically open
