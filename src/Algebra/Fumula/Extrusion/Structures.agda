------------------------------------------------------------------------
-- Algebraic structures of fumula extrusions (not bundled).
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Structures where

open import Level using (Level; _⊔_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.Core using (Rel)
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
    module Fₗ = AlmostFumula Fₗ
    module Fᵣ = AlmostFumula Fᵣ

  record IsBiAlmostFumulaExtrusion : Set (fₗ ⊔ fᵣ ⊔ x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ ℓx) where
    private
      module L = LeftDefs ❲_❳⤙_⤚_ _≈_
      module R = RightDefs _⤙_⤚❲_❳ _≈_
    open BiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isEquivalence : IsEquivalence _≈_
      ❲❳⤙⤚-cong : L.Congruent₃ Fₗ._≈_
      ❲❳⤙⤚-double-exchange : L.MiddleNestedDoubleExchange
      ⤙⤚❲❳-cong : R.Congruent₃ Fᵣ._≈_
      ⤙⤚❲❳-double-exchange : R.MiddleNestedDoubleExchange

    ❲❳⤙⤚-isLeftAlmostFumulaExtrusion : IsLeftAlmostFumulaExtrusion Fₗ _≈_ ❲_❳⤙_⤚_
    ❲❳⤙⤚-isLeftAlmostFumulaExtrusion = record
      { isEquivalence = isEquivalence
      ; ❲❳⤙⤚-cong = ❲❳⤙⤚-cong
      ; ❲❳⤙⤚-double-exchange = ❲❳⤙⤚-double-exchange
      }

    ⤙⤚❲❳-isRightAlmostFumulaExtrusion : IsRightAlmostFumulaExtrusion Fᵣ _≈_ _⤙_⤚❲_❳
    ⤙⤚❲❳-isRightAlmostFumulaExtrusion = record
      { isEquivalence = isEquivalence
      ; ⤙⤚❲❳-cong = ⤙⤚❲❳-cong
      ; ⤙⤚❲❳-double-exchange = ⤙⤚❲❳-double-exchange
      }

    double-exchange : MiddleNestedDoubleExchange
    double-exchange = ❲❳⤙⤚-double-exchange , ⤙⤚❲❳-double-exchange

module _ (F : ReversibleAlmostFumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (ReversibleAlmostFumula.Carrier F) X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (ReversibleAlmostFumula.Carrier F) X)
         where
  private
    module F = ReversibleAlmostFumula F

  record IsAlmostFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    field
      isBiAlmostFumulaExtrusion : IsBiAlmostFumulaExtrusion F.almostFumula F.almostFumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳

    open IsBiAlmostFumulaExtrusion isBiAlmostFumulaExtrusion public

  record IsReversibleAlmostFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open SimultaneousBiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isAlmostFumulaExtrusion : IsAlmostFumulaExtrusion
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
      ❲❳⤙⤚-◆ᶠ-pulloutₗ : LeftPulloutWith F._⤙_⤚_ F.◆
      ❲❳⤙⤚-◆-pulloutᵣ : RightPulloutWith ◆
      ❲❳⤙⤚-■ᶠ-collapse-dupʳ : ∀ x → (❲ F.■ ❳⤙ x ⤚ x) ≈ ◆
      ❲❳⤙⤚-◆ᶠ-collapse-middleˡ : ∀ x z → (❲ F.◆ ❳⤙ z ⤚ x) ≈ z
      ❲❳⤙⤚-◆-collapse-middleʳ : ∀ x z → (❲ x ❳⤙ z ⤚ ◆) ≈ z
      ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ : ∀ x → (❲ F.● ❳⤙ ◆ ⤚ x) ≈ x
      ❲❳⤙⤚-◆ᶠ-◆-outer-associate : OuterAssociativeWith F._⤙_⤚_ F.◆ ◆

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
      ⤙⤚❲❳-◆ᶠ-pulloutᵣ : RightPulloutWith F._⤙_⤚_ F.◆
      ⤙⤚❲❳-■ᶠ-collapse-dupˡ : ∀ x → (x ⤙ x ⤚❲ F.■ ❳) ≈ ◆
      ⤙⤚❲❳-◆-collapse-middleˡ : ∀ x z → (◆ ⤙ z ⤚❲ x ❳) ≈ z
      ⤙⤚❲❳-◆ᶠ-collapse-middleʳ : ∀ x z → (x ⤙ z ⤚❲ F.◆ ❳) ≈ z
      ⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ : ∀ x → (x ⤙ ◆ ⤚❲ F.● ❳) ≈ x
      ⤙⤚❲❳-◆ᶠ-◆-outer-associate : OuterAssociativeWith F._⤙_⤚_ F.◆ ◆

    open IsRightAlmostFumulaExtrusion ⤙⤚❲❳-isRightAlmostFumulaExtrusion public

module _ (Fₗ : Fumula fₗ ℓfₗ) (Fᵣ : Fumula fᵣ ℓfᵣ) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (Fumula.Carrier Fₗ) X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (Fumula.Carrier Fᵣ) X) (◆ : X)
         where
  private
    module Fₗ = Fumula Fₗ
    module Fᵣ = Fumula Fᵣ

  record IsBiFumulaExtrusion : Set (fₗ ⊔ fᵣ ⊔ x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ ℓx) where
    private
      module L = LeftDefs ❲_❳⤙_⤚_ _≈_
      module R = RightDefs _⤙_⤚❲_❳ _≈_
    open BiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isBiAlmostFumulaExtrusion : IsBiAlmostFumulaExtrusion Fₗ.almostFumula Fᵣ.almostFumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
      ❲❳⤙⤚-●ᶠ-inner-commuteᵣ : L.RightInnerCommutativeWith Fₗ.●
      ❲❳⤙⤚-◆ᶠ-pulloutₗ : L.LeftPulloutWith Fₗ._⤙_⤚_ Fₗ.◆
      ❲❳⤙⤚-◆-pulloutᵣ : L.RightPulloutWith ◆
      ❲❳⤙⤚-■ᶠ-collapse-dupʳ : ∀ x → (❲ Fₗ.■ ❳⤙ x ⤚ x) ≈ ◆
      ❲❳⤙⤚-◆ᶠ-collapse-middleˡ : ∀ x z → (❲ Fₗ.◆ ❳⤙ z ⤚ x) ≈ z
      ❲❳⤙⤚-◆-collapse-middleʳ : ∀ x z → (❲ x ❳⤙ z ⤚ ◆) ≈ z
      ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ : ∀ x → (❲ Fₗ.● ❳⤙ ◆ ⤚ x) ≈ x
      ❲❳⤙⤚-◆ᶠ-◆-outer-associate : L.OuterAssociativeWith Fₗ._⤙_⤚_ Fₗ.◆ ◆
      ⤙⤚❲❳-●ᶠ-inner-commuteₗ : R.LeftInnerCommutativeWith Fᵣ.●
      ⤙⤚❲❳-◆-pulloutₗ : R.LeftPulloutWith ◆
      ⤙⤚❲❳-◆ᶠ-pulloutᵣ : R.RightPulloutWith Fᵣ._⤙_⤚_ Fᵣ.◆
      ⤙⤚❲❳-■ᶠ-collapse-dupˡ : ∀ x → (x ⤙ x ⤚❲ Fᵣ.■ ❳) ≈ ◆
      ⤙⤚❲❳-◆-collapse-middleˡ : ∀ x z → (◆ ⤙ z ⤚❲ x ❳) ≈ z
      ⤙⤚❲❳-◆ᶠ-collapse-middleʳ : ∀ x z → (x ⤙ z ⤚❲ Fᵣ.◆ ❳) ≈ z
      ⤙⤚❲❳-●-◆-collapse-sideʳ : ∀ x → (x ⤙ ◆ ⤚❲ Fᵣ.● ❳) ≈ x
      ⤙⤚❲❳-◆ᶠ-◆-outer-associate : R.OuterAssociativeWith Fᵣ._⤙_⤚_ Fᵣ.◆ ◆
      ◆-outer-associate : OuterAssociativeWith ◆

    open IsBiAlmostFumulaExtrusion isBiAlmostFumulaExtrusion public

    ◆-pullout : PulloutWith ◆
    ◆-pullout = ⤙⤚❲❳-◆-pulloutₗ , ❲❳⤙⤚-◆-pulloutᵣ

    ❲❳⤙⤚-isLeftFumulaExtrusion : IsLeftFumulaExtrusion Fₗ _≈_ ❲_❳⤙_⤚_ ◆
    ❲❳⤙⤚-isLeftFumulaExtrusion = record
      { ❲❳⤙⤚-isLeftAlmostFumulaExtrusion = ❲❳⤙⤚-isLeftAlmostFumulaExtrusion
      ; ❲❳⤙⤚-●ᶠ-inner-commuteᵣ = ❲❳⤙⤚-●ᶠ-inner-commuteᵣ
      ; ❲❳⤙⤚-◆ᶠ-pulloutₗ = ❲❳⤙⤚-◆ᶠ-pulloutₗ
      ; ❲❳⤙⤚-◆-pulloutᵣ = ❲❳⤙⤚-◆-pulloutᵣ
      ; ❲❳⤙⤚-■ᶠ-collapse-dupʳ = ❲❳⤙⤚-■ᶠ-collapse-dupʳ
      ; ❲❳⤙⤚-◆ᶠ-collapse-middleˡ = ❲❳⤙⤚-◆ᶠ-collapse-middleˡ
      ; ❲❳⤙⤚-◆-collapse-middleʳ = ❲❳⤙⤚-◆-collapse-middleʳ
      ; ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ = ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ
      ; ❲❳⤙⤚-◆ᶠ-◆-outer-associate = ❲❳⤙⤚-◆ᶠ-◆-outer-associate
      }

    ⤙⤚❲❳-isRightFumulaExtrusion : IsRightFumulaExtrusion Fᵣ _≈_ _⤙_⤚❲_❳ ◆
    ⤙⤚❲❳-isRightFumulaExtrusion = record
      { ⤙⤚❲❳-isRightAlmostFumulaExtrusion = ⤙⤚❲❳-isRightAlmostFumulaExtrusion
      ; ⤙⤚❲❳-●ᶠ-inner-commuteₗ = ⤙⤚❲❳-●ᶠ-inner-commuteₗ
      ; ⤙⤚❲❳-◆-pulloutₗ = ⤙⤚❲❳-◆-pulloutₗ
      ; ⤙⤚❲❳-◆ᶠ-pulloutᵣ = ⤙⤚❲❳-◆ᶠ-pulloutᵣ
      ; ⤙⤚❲❳-■ᶠ-collapse-dupˡ = ⤙⤚❲❳-■ᶠ-collapse-dupˡ
      ; ⤙⤚❲❳-◆-collapse-middleˡ = ⤙⤚❲❳-◆-collapse-middleˡ
      ; ⤙⤚❲❳-◆ᶠ-collapse-middleʳ = ⤙⤚❲❳-◆ᶠ-collapse-middleʳ
      ; ⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ = ⤙⤚❲❳-●-◆-collapse-sideʳ
      ; ⤙⤚❲❳-◆ᶠ-◆-outer-associate = ⤙⤚❲❳-◆ᶠ-◆-outer-associate
      }

module _ (F : ReversibleFumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (ReversibleFumula.Carrier F) X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (ReversibleFumula.Carrier F) X) (◆ : X)
         where
  private
    module F = ReversibleFumula F

  record IsFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open SimultaneousBiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isBiFumulaExtrusion : IsBiFumulaExtrusion F.fumula F.fumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
      ■ᶠ-outer-commute : OuterCommutativeWithUnderlying F.■
      ◆ᶠ-outer-commute : OuterCommutativeWithUnderlying F.◆
      ●ᶠ-outer-commute : OuterCommutativeWithUnderlying F.●
      ◆-outer-commute : OuterCommutativeWith ◆

    open IsBiFumulaExtrusion isBiFumulaExtrusion public

    ●ᶠ-inner-commute : InnerCommutativeWith F.●
    ●ᶠ-inner-commute = ⤙⤚❲❳-●ᶠ-inner-commuteₗ , ❲❳⤙⤚-●ᶠ-inner-commuteᵣ

    ◆ᶠ-pullout : PulloutWith F._⤙_⤚_ F.◆
    ◆ᶠ-pullout = ❲❳⤙⤚-◆ᶠ-pulloutₗ , ⤙⤚❲❳-◆ᶠ-pulloutᵣ

    isAlmostFumulaExtrusion : IsAlmostFumulaExtrusion F.reversibleAlmostFumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
    isAlmostFumulaExtrusion = record { isBiAlmostFumulaExtrusion = isBiAlmostFumulaExtrusion }

  record IsReversibleFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open SimultaneousBiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isFumulaExtrusion : IsFumulaExtrusion
      outer-commute : OuterCommutative

    open IsFumulaExtrusion isFumulaExtrusion public

    isReversibleAlmostFumulaExtrusion : IsReversibleAlmostFumulaExtrusion F.reversibleAlmostFumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
    isReversibleAlmostFumulaExtrusion = record
      { isAlmostFumulaExtrusion = isAlmostFumulaExtrusion
      ; outer-commute = outer-commute
      }
