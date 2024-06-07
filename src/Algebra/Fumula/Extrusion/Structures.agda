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

  record IsDoubleAlmostFumulaExtrusion : Set (fₗ ⊔ fᵣ ⊔ x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ ℓx) where
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
      ❲❳⤙⤚-⤙⤚❲❳-double-exchange : MiddleNestedDoubleExchange -- TODO: ought to be provable from other axioms

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

module _ (F : ReversibleAlmostFumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (ReversibleAlmostFumula.Carrier F) X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (ReversibleAlmostFumula.Carrier F) X)
         where
  private
    module F = ReversibleAlmostFumula F

  record IsAlmostFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open SimultaneousBiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isDoubleAlmostFumulaExtrusion : IsDoubleAlmostFumulaExtrusion F.almostFumula F.almostFumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
      outer-commute : OuterCommutative

    open IsDoubleAlmostFumulaExtrusion isDoubleAlmostFumulaExtrusion public

module _ (F : Fumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (Fumula.Carrier F) X) (◆ : X) where
  private
    module F = Fumula F

  record IsLeftFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open LeftDefs ❲_❳⤙_⤚_ _≈_

    field
      isLeftAlmostFumulaExtrusion : IsLeftAlmostFumulaExtrusion F.almostFumula _≈_ ❲_❳⤙_⤚_
      ❲❳⤙⤚-●ᶠ-inner-commuteʳ : RightInnerCommutativeWith F.●
      ❲❳⤙⤚-◆ᶠ-pulloutˡ : LeftPulloutWith F._⤙_⤚_ F.◆
      ❲❳⤙⤚-◆-pulloutʳ : RightPulloutWith ◆
      ❲❳⤙⤚-■ᶠ-collapse-dupʳ : ∀ x → (❲ F.■ ❳⤙ x ⤚ x) ≈ ◆
      ❲❳⤙⤚-◆ᶠ-collapse-middleˡ : ∀ x z → (❲ F.◆ ❳⤙ z ⤚ x) ≈ z
      ❲❳⤙⤚-◆-collapse-middleʳ : ∀ x z → (❲ x ❳⤙ z ⤚ ◆) ≈ z
      ❲❳⤙⤚-◆ᶠ-◆-outer-associate : OuterAssociativeWith F._⤙_⤚_ F.◆ ◆

    open IsLeftAlmostFumulaExtrusion isLeftAlmostFumulaExtrusion public

module _ (F : Fumula f ℓf) (_≈_ : Rel {x} X ℓx)
         (_⤙_⤚❲_❳ : Op₃ᵣ (Fumula.Carrier F) X) (◆ : X) where
  private
    module F = Fumula F

  record IsRightFumulaExtrusion : Set (f ⊔ x ⊔ ℓf ⊔ ℓx) where
    open RightDefs _⤙_⤚❲_❳ _≈_

    field
      isRightAlmostFumulaExtrusion : IsRightAlmostFumulaExtrusion F.almostFumula _≈_ _⤙_⤚❲_❳
      ⤙⤚❲❳-●ᶠ-inner-commuteˡ : LeftInnerCommutativeWith F.●
      ⤙⤚❲❳-◆-pulloutˡ : LeftPulloutWith ◆
      ⤙⤚❲❳-◆ᶠ-pulloutʳ : RightPulloutWith F._⤙_⤚_ F.◆
      ⤙⤚❲❳-■ᶠ-collapse-dupˡ : ∀ x → (x ⤙ x ⤚❲ F.■ ❳) ≈ ◆
      ⤙⤚❲❳-◆-collapse-middleˡ : ∀ x z → (◆ ⤙ z ⤚❲ x ❳) ≈ z
      ⤙⤚❲❳-◆ᶠ-collapse-middleʳ : ∀ x z → (x ⤙ z ⤚❲ F.◆ ❳) ≈ z
      ⤙⤚❲❳-◆ᶠ-◆-outer-associate : OuterAssociativeWith F._⤙_⤚_ F.◆ ◆

    open IsRightAlmostFumulaExtrusion isRightAlmostFumulaExtrusion public

module _ (Fₗ : Fumula fₗ ℓfₗ) (Fᵣ : Fumula fᵣ ℓfᵣ) (_≈_ : Rel {x} X ℓx)
         (❲_❳⤙_⤚_ : Op₃ₗ (Fumula.Carrier Fₗ) X)
         (_⤙_⤚❲_❳ : Op₃ᵣ (Fumula.Carrier Fᵣ) X) (◆ : X)
         where
  private
    module Fₗ = Fumula Fₗ
    module Fᵣ = Fumula Fᵣ

  record IsDoubleFumulaExtrusion : Set (fₗ ⊔ fᵣ ⊔ x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ ℓx) where
    private
      module L = LeftDefs ❲_❳⤙_⤚_ _≈_
      module R = RightDefs _⤙_⤚❲_❳ _≈_
    open BiDefs ❲_❳⤙_⤚_ _⤙_⤚❲_❳ _≈_

    field
      isDoubleAlmostFumulaExtrusion : IsDoubleAlmostFumulaExtrusion Fₗ.almostFumula Fᵣ.almostFumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
      ❲❳⤙⤚-●ᶠ-inner-commuteʳ : L.RightInnerCommutativeWith Fₗ.●
      ❲❳⤙⤚-◆ᶠ-pulloutˡ : L.LeftPulloutWith Fₗ._⤙_⤚_ Fₗ.◆
      ❲❳⤙⤚-◆-pulloutʳ : L.RightPulloutWith ◆
      ❲❳⤙⤚-■ᶠ-collapse-dupʳ : ∀ x → (❲ Fₗ.■ ❳⤙ x ⤚ x) ≈ ◆
      ❲❳⤙⤚-◆ᶠ-collapse-middleˡ : ∀ x z → (❲ Fₗ.◆ ❳⤙ z ⤚ x) ≈ z
      ❲❳⤙⤚-◆-collapse-middleʳ : ∀ x z → (❲ x ❳⤙ z ⤚ ◆) ≈ z
      ❲❳⤙⤚-◆ᶠ-◆-outer-associate : L.OuterAssociativeWith Fₗ._⤙_⤚_ Fₗ.◆ ◆
      ⤙⤚❲❳-●ᶠ-inner-commuteˡ : R.LeftInnerCommutativeWith Fᵣ.●
      ⤙⤚❲❳-◆-pulloutˡ : R.LeftPulloutWith ◆
      ⤙⤚❲❳-◆ᶠ-pulloutʳ : R.RightPulloutWith Fᵣ._⤙_⤚_ Fᵣ.◆
      ⤙⤚❲❳-■ᶠ-collapse-dupˡ : ∀ x → (x ⤙ x ⤚❲ Fᵣ.■ ❳) ≈ ◆
      ⤙⤚❲❳-◆-collapse-middleˡ : ∀ x z → (◆ ⤙ z ⤚❲ x ❳) ≈ z
      ⤙⤚❲❳-◆ᶠ-collapse-middleʳ : ∀ x z → (x ⤙ z ⤚❲ Fᵣ.◆ ❳) ≈ z
      ⤙⤚❲❳-◆ᶠ-◆-outer-associate : R.OuterAssociativeWith Fᵣ._⤙_⤚_ Fᵣ.◆ ◆
      ⤙⤚❲❳-❲❳⤙⤚-◆-pulloutˡ : LeftPulloutAlternatingWith ◆ -- TODO: ought to be provable from other axioms
      ❲❳⤙⤚-⤙⤚❲❳-◆-pulloutʳ : RightPulloutAlternatingWith ◆ -- TODO: ought to be provable from other axioms
      ■ᶠ-outer-commute : OuterCommutativeWithUnderlying Fₗ.■ Fᵣ.■
      ◆ᶠ-outer-commute : OuterCommutativeWithUnderlying Fₗ.◆ Fᵣ.◆
      ●ᶠ-outer-commute : OuterCommutativeWithUnderlying Fₗ.● Fᵣ.●
      ◆-outer-associate : OuterAssociativeWith ◆

    open IsDoubleAlmostFumulaExtrusion isDoubleAlmostFumulaExtrusion public

    ◆-pullout : PulloutWith ◆
    ◆-pullout = ⤙⤚❲❳-◆-pulloutˡ , ❲❳⤙⤚-◆-pulloutʳ

    ◆-pullout-alternating : PulloutAlternatingWith ◆
    ◆-pullout-alternating = ⤙⤚❲❳-❲❳⤙⤚-◆-pulloutˡ , ❲❳⤙⤚-⤙⤚❲❳-◆-pulloutʳ

    ❲❳⤙⤚-isLeftFumulaExtrusion : IsLeftFumulaExtrusion Fₗ _≈_ ❲_❳⤙_⤚_ ◆
    ❲❳⤙⤚-isLeftFumulaExtrusion = record
      { isLeftAlmostFumulaExtrusion = ❲❳⤙⤚-isLeftAlmostFumulaExtrusion
      ; ❲❳⤙⤚-●ᶠ-inner-commuteʳ = ❲❳⤙⤚-●ᶠ-inner-commuteʳ
      ; ❲❳⤙⤚-◆ᶠ-pulloutˡ = ❲❳⤙⤚-◆ᶠ-pulloutˡ
      ; ❲❳⤙⤚-◆-pulloutʳ = ❲❳⤙⤚-◆-pulloutʳ
      ; ❲❳⤙⤚-■ᶠ-collapse-dupʳ = ❲❳⤙⤚-■ᶠ-collapse-dupʳ
      ; ❲❳⤙⤚-◆ᶠ-collapse-middleˡ = ❲❳⤙⤚-◆ᶠ-collapse-middleˡ
      ; ❲❳⤙⤚-◆-collapse-middleʳ = ❲❳⤙⤚-◆-collapse-middleʳ
      ; ❲❳⤙⤚-◆ᶠ-◆-outer-associate = ❲❳⤙⤚-◆ᶠ-◆-outer-associate
      }

    ⤙⤚❲❳-isRightFumulaExtrusion : IsRightFumulaExtrusion Fᵣ _≈_ _⤙_⤚❲_❳ ◆
    ⤙⤚❲❳-isRightFumulaExtrusion = record
      { isRightAlmostFumulaExtrusion = ⤙⤚❲❳-isRightAlmostFumulaExtrusion
      ; ⤙⤚❲❳-●ᶠ-inner-commuteˡ = ⤙⤚❲❳-●ᶠ-inner-commuteˡ
      ; ⤙⤚❲❳-◆-pulloutˡ = ⤙⤚❲❳-◆-pulloutˡ
      ; ⤙⤚❲❳-◆ᶠ-pulloutʳ = ⤙⤚❲❳-◆ᶠ-pulloutʳ
      ; ⤙⤚❲❳-■ᶠ-collapse-dupˡ = ⤙⤚❲❳-■ᶠ-collapse-dupˡ
      ; ⤙⤚❲❳-◆-collapse-middleˡ = ⤙⤚❲❳-◆-collapse-middleˡ
      ; ⤙⤚❲❳-◆ᶠ-collapse-middleʳ = ⤙⤚❲❳-◆ᶠ-collapse-middleʳ
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
      isDoubleFumulaExtrusion : IsDoubleFumulaExtrusion F.fumula F.fumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
      outer-commute : OuterCommutative

    open IsDoubleFumulaExtrusion isDoubleFumulaExtrusion public

    ●ᶠ-inner-commute : InnerCommutativeWith F.●
    ●ᶠ-inner-commute = ⤙⤚❲❳-●ᶠ-inner-commuteˡ , ❲❳⤙⤚-●ᶠ-inner-commuteʳ

    ◆-outer-commute : OuterCommutativeWith ◆
    ◆-outer-commute = outer-commute ◆

    ◆ᶠ-pullout : PulloutWith F._⤙_⤚_ F.◆
    ◆ᶠ-pullout = ❲❳⤙⤚-◆ᶠ-pulloutˡ , ⤙⤚❲❳-◆ᶠ-pulloutʳ

    isAlmostFumulaExtrusion : IsAlmostFumulaExtrusion F.reversibleAlmostFumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
    isAlmostFumulaExtrusion = record
      { isDoubleAlmostFumulaExtrusion = isDoubleAlmostFumulaExtrusion
      ; outer-commute = outer-commute
      }
