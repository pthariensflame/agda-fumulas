------------------------------------------------------------------------
-- Algebraic structures of fumula extrusions (not bundled).
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Structures where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Algebra.Fumula.Core
import Algebra.Fumula.Definitions as BaseDefs
open import Algebra.Fumula.Structures
open import Algebra.Fumula.Bundles
open import Algebra.Fumula.Extrusion.Core
open import Algebra.Fumula.Extrusion.Definitions

private
  variable
    x ℓx f ℓf fₗ ℓfₗ fᵣ ℓfᵣ : Level
    X : Set x

module _ (F : AlmostFumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (AlmostFumula.Carrier F) X)
         where
  private
    module F = AlmostFumula F

  record IsLeftAlmostFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open LeftDefs ❲_❳⤙_⤚_ _≈_

    field
      isEquivalence : IsEquivalence _≈_
      ❲❳⤙⤚-cong : Congruent₃ F._≈_
      ❲❳⤙⤚-double-exchange : MiddleNestedDoubleExchange

module _ (F : AlmostFumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (_⤙_⤚❲_❳ : Op₃ᵣ (AlmostFumula.Carrier F) X)
         where
  private
    module F = AlmostFumula F

  record IsRightAlmostFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open RightDefs _⤙_⤚❲_❳ _≈_

    field
      isEquivalence : IsEquivalence _≈_
      ⤙⤚❲❳-cong : Congruent₃ F._≈_
      ⤙⤚❲❳-double-exchange : MiddleNestedDoubleExchange

module _ (Fₗ : AlmostFumula fₗ ℓfₗ) (Fᵣ : AlmostFumula fᵣ ℓfᵣ) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (AlmostFumula.Carrier Fₗ) X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (AlmostFumula.Carrier Fᵣ) X)
         where
  private
    module Fᵣ = AlmostFumula Fᵣ

  record IsBiAlmostFumulaExtrusion : Set (fₗ ⊔ fᵣ ⊔ x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ ℓx) where
    private
      module R = RightDefs _⤙_⤚❲_❳ _≈_
    open BiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      ❲❳⤙⤚-isLeftAlmostFumulaExtrusion : IsLeftAlmostFumulaExtrusion Fₗ _≈_ ❲_❳⤙_⤚_
      ⤙⤚❲❳-cong : R.Congruent₃ Fᵣ._≈_
      ⤙⤚❲❳-double-exchange : R.MiddleNestedDoubleExchange

    open IsLeftAlmostFumulaExtrusion ❲❳⤙⤚-isLeftAlmostFumulaExtrusion public

    ⤙⤚❲❳-isRightAlmostFumulaExtrusion : IsRightAlmostFumulaExtrusion Fᵣ _≈_ _⤙_⤚❲_❳
    ⤙⤚❲❳-isRightAlmostFumulaExtrusion = record
      { isEquivalence = isEquivalence
      ; ⤙⤚❲❳-cong = ⤙⤚❲❳-cong
      ; ⤙⤚❲❳-double-exchange = ⤙⤚❲❳-double-exchange
      }

    double-exchange : MiddleNestedDoubleExchange
    double-exchange = ❲❳⤙⤚-double-exchange , ⤙⤚❲❳-double-exchange

module _ (F : AlmostFumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (AlmostFumula.Carrier F) X) (_⤙_⤚❲_❳ : Op₃ᵣ (AlmostFumula.Carrier F) X)
         where

  record IsAlmostFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    field
      isBiAlmostFumulaExtrusion : IsBiAlmostFumulaExtrusion F F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳

    open IsBiAlmostFumulaExtrusion isBiAlmostFumulaExtrusion public

module _ (F : ReversibleAlmostFumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (ReversibleAlmostFumula.Carrier F) X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (ReversibleAlmostFumula.Carrier F) X)
         where
  private
    module F = ReversibleAlmostFumula F

  record IsReversibleAlmostFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open SimultaneousBiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isAlmostFumulaExtrusion : IsAlmostFumulaExtrusion F.almostFumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
      outer-commute : OuterCommutative

    open IsAlmostFumulaExtrusion isAlmostFumulaExtrusion public

module _ (F : Fumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (Fumula.Carrier F) X) (◆ : X) where
  private
    module F = Fumula F

  record IsLeftFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open LeftDefs ❲_❳⤙_⤚_ _≈_

    field
      ❲❳⤙⤚-isLeftAlmostFumulaExtrusion : IsLeftAlmostFumulaExtrusion F.almostFumula _≈_ ❲_❳⤙_⤚_
      ❲❳⤙⤚-●ᶠ-inner-commuteᵣ : RightInnerCommutativeWith F.●
      ❲❳⤙⤚-◆-pulloutᵣ : RightPulloutWith ◆
      ❲❳⤙⤚-■ᶠ-collapse-dupʳ : ∀ x → (❲ F.■ ❳⤙ x ⤚ x) ≈ ◆
      ❲❳⤙⤚-◆ᶠ-collapse-middleˡ : ∀ x z → (❲ F.◆ ❳⤙ z ⤚ x) ≈ z
      ❲❳⤙⤚-◆-collapse-middleʳ : ∀ x z → (❲ x ❳⤙ z ⤚ ◆) ≈ z
      ●-◆-collapse-sideˡ : ∀ x → (❲ F.● ❳⤙ ◆ ⤚ x) ≈ x

    open IsLeftAlmostFumulaExtrusion ❲❳⤙⤚-isLeftAlmostFumulaExtrusion public

module _ (F : Fumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (_⤙_⤚❲_❳ : Op₃ᵣ (Fumula.Carrier F) X) (◆ : X) where
  private
    module F = Fumula F

  record IsRightFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open RightDefs _⤙_⤚❲_❳ _≈_

    field
      ⤙⤚❲❳-isRightAlmostFumulaExtrusion : IsRightAlmostFumulaExtrusion F.almostFumula _≈_ _⤙_⤚❲_❳
      ⤙⤚❲❳-●ᶠ-inner-commuteₗ : LeftInnerCommutativeWith F.●
      ⤙⤚❲❳-◆-pulloutₗ : LeftPulloutWith ◆
      ⤙⤚❲❳-■ᶠ-collapse-dupˡ : ∀ x → (x ⤙ x ⤚❲ F.■ ❳) ≈ ◆
      ⤙⤚❲❳-◆-collapse-middleˡ : ∀ x z → (◆ ⤙ z ⤚❲ x ❳) ≈ z
      ⤙⤚❲❳-◆ᶠ-collapse-middleʳ : ∀ x z → (x ⤙ z ⤚❲ F.◆ ❳) ≈ z
      ●-◆-collapse-sideʳ : ∀ x → (x ⤙ ◆ ⤚❲ F.● ❳) ≈ x

    open IsRightAlmostFumulaExtrusion ⤙⤚❲❳-isRightAlmostFumulaExtrusion public

module _ (Fₗ : Fumula fₗ ℓfₗ) (Fᵣ : Fumula fᵣ ℓfᵣ) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (Fumula.Carrier Fₗ) X) (◆ : X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (Fumula.Carrier Fᵣ) X) (◆ : X)
         where
  private
    module Fₗ = Fumula Fₗ
    module Fᵣ = Fumula Fᵣ

  record IsPartialBiFumulaExtrusion : Set (fₗ ⊔ fᵣ ⊔ x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ ℓx) where
    private
      module R = RightDefs _⤙_⤚❲_❳ _≈_

    field
      ❲❳⤙⤚-isLeftFumulaExtrusion : IsLeftFumulaExtrusion Fₗ _≈_ ❲_❳⤙_⤚_ ◆
      ⤙⤚❲❳-cong : R.Congruent₃ Fᵣ._≈_
      ⤙⤚❲❳-double-exchange : R.MiddleNestedDoubleExchange
      ⤙⤚❲❳-●ᶠ-inner-commuteₗ : R.LeftInnerCommutativeWith Fᵣ.●
      ⤙⤚❲❳-◆-pulloutₗ : R.LeftPulloutWith ◆
      ⤙⤚❲❳-■ᶠ-collapse-dupˡ : ∀ x → (x ⤙ x ⤚❲ Fᵣ.■ ❳) ≈ ◆
      ⤙⤚❲❳-◆-collapse-middleˡ : ∀ x z → (◆ ⤙ z ⤚❲ x ❳) ≈ z
      ⤙⤚❲❳-◆ᶠ-collapse-middleʳ : ∀ x z → (x ⤙ z ⤚❲ Fᵣ.◆ ❳) ≈ z
      ●-◆-collapse-sideʳ : ∀ x → (x ⤙ ◆ ⤚❲ Fᵣ.● ❳) ≈ x

    open IsLeftFumulaExtrusion ❲❳⤙⤚-isLeftFumulaExtrusion public

    ⤙⤚❲❳-isRightFumulaExtrusion : IsRightFumulaExtrusion Fᵣ _≈_ _⤙_⤚❲_❳ ◆
    ⤙⤚❲❳-isRightFumulaExtrusion = record
      { ⤙⤚❲❳-isRightAlmostFumulaExtrusion = record
        { isEquivalence = isEquivalence
        ; ⤙⤚❲❳-cong = ⤙⤚❲❳-cong
        ; ⤙⤚❲❳-double-exchange = ⤙⤚❲❳-double-exchange
        }
      ; ⤙⤚❲❳-●ᶠ-inner-commuteₗ = ⤙⤚❲❳-●ᶠ-inner-commuteₗ
      ; ⤙⤚❲❳-◆-pulloutₗ = ⤙⤚❲❳-◆-pulloutₗ
      ; ⤙⤚❲❳-■ᶠ-collapse-dupˡ = ⤙⤚❲❳-■ᶠ-collapse-dupˡ
      ; ⤙⤚❲❳-◆-collapse-middleˡ = ⤙⤚❲❳-◆-collapse-middleˡ
      ; ⤙⤚❲❳-◆ᶠ-collapse-middleʳ = ⤙⤚❲❳-◆ᶠ-collapse-middleʳ
      ; ●-◆-collapse-sideʳ = ●-◆-collapse-sideʳ
      }

    open IsRightFumulaExtrusion ⤙⤚❲❳-isRightFumulaExtrusion public
      using (⤙⤚❲❳-isRightAlmostFumulaExtrusion)

    isBiAlmostFumulaExtrusion : IsBiAlmostFumulaExtrusion Fₗ.almostFumula Fᵣ.almostFumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
    isBiAlmostFumulaExtrusion = record
      { ❲❳⤙⤚-isLeftAlmostFumulaExtrusion = ❲❳⤙⤚-isLeftAlmostFumulaExtrusion
      ; ⤙⤚❲❳-cong = ⤙⤚❲❳-cong
      ; ⤙⤚❲❳-double-exchange = ⤙⤚❲❳-double-exchange
      }

    open IsBiAlmostFumulaExtrusion isBiAlmostFumulaExtrusion public
      using (double-exchange)

module _ (Fₗ : Fumula fₗ ℓfₗ) (Fᵣ : Fumula fᵣ ℓfᵣ) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (Fumula.Carrier Fₗ) X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (Fumula.Carrier Fᵣ) X) (◆ : X)
         where

  record IsBiFumulaExtrusion : Set (fₗ ⊔ fᵣ ⊔ x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ ℓx) where
    open BiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isPartialBiFumulaExtrusion : IsPartialBiFumulaExtrusion Fₗ Fᵣ _≈_ ❲_❳⤙_⤚_ ◆ _⤙_⤚❲_❳ ◆
      ◆-outer-associate : OuterAssociativeWith ◆

    open IsPartialBiFumulaExtrusion isPartialBiFumulaExtrusion public
      renaming (❲❳⤙⤚-◆-pulloutᵣ to ❲❳⤙⤚-◆-pulloutᵣ; ⤙⤚❲❳-◆-pulloutₗ to ⤙⤚❲❳-◆-pulloutₗ)

    ◆-pullout : PulloutWith ◆
    ◆-pullout = ⤙⤚❲❳-◆-pulloutₗ , ❲❳⤙⤚-◆-pulloutᵣ

module _ (F : Fumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (Fumula.Carrier F) X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (Fumula.Carrier F) X) (◆ : X)
         where
  private
    module F = Fumula F

  record IsFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open SimultaneousBiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isBiFumulaExtrusion : IsBiFumulaExtrusion F F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
      ■ᶠ-outer-commute : OuterCommutativeWithUnderlying F.■
      ◆ᶠ-outer-commute : OuterCommutativeWithUnderlying F.◆
      ●ᶠ-outer-commute : OuterCommutativeWithUnderlying F.●
      ◆-outer-commute : OuterCommutativeWith ◆

    open IsBiFumulaExtrusion isBiFumulaExtrusion public

    ●ᶠ-inner-commute : InnerCommutativeWith F.●
    ●ᶠ-inner-commute = ⤙⤚❲❳-●ᶠ-inner-commuteₗ , ❲❳⤙⤚-●ᶠ-inner-commuteᵣ

module _ (F : ReversibleFumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (ReversibleFumula.Carrier F) X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (ReversibleFumula.Carrier F) X) (◆ : X)
         where
  private
    module F = ReversibleFumula F

  record IsReversibleFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open SimultaneousBiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isFumulaExtrusion : IsFumulaExtrusion F.fumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
      outer-commute : OuterCommutative

    open IsFumulaExtrusion isFumulaExtrusion public
