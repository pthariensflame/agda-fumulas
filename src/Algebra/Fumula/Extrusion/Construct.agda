module Algebra.Fumula.Extrusion.Construct where
open import Level using (_⊔_)
open import Data.Empty.Polymorphic
open import Data.Unit.Polymorphic
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise; ×-isEquivalence)
open import Algebra.Fumula.Bundles
open import Algebra.Fumula.Extrusion.Core
open import Algebra.Fumula.Extrusion.Definitions
open import Algebra.Fumula.Extrusion.Structures
open import Algebra.Fumula.Extrusion.Bundles

module Terminal {x xℓ} where

  module 𝕆ne where

    Carrier : Set x
    Carrier = ⊤

    infix  4 _≈_
    _≈_ : Rel Carrier xℓ
    _ ≈ _ = ⊤

  open 𝕆ne

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record { 𝕆ne }

  module _ {f fℓ} (F : AlmostFumula f fℓ) where

    leftAlmostFumulaExtrusion : LeftAlmostFumulaExtrusion F x xℓ
    leftAlmostFumulaExtrusion = record { 𝕆ne }
    open LeftAlmostFumulaExtrusion leftAlmostFumulaExtrusion public
      using (isLeftAlmostFumulaExtrusion)

    rightAlmostFumulaExtrusion : RightAlmostFumulaExtrusion F x xℓ
    rightAlmostFumulaExtrusion = record { 𝕆ne }
    open RightAlmostFumulaExtrusion rightAlmostFumulaExtrusion public
      using (isRightAlmostFumulaExtrusion)

  module _ {fₗ fᵣ fℓₗ fℓᵣ} (Fₗ : AlmostFumula fₗ fℓₗ) (Fᵣ : AlmostFumula fᵣ fℓᵣ) where

    doubleAlmostFumulaExtrusion : DoubleAlmostFumulaExtrusion Fₗ Fᵣ x xℓ
    doubleAlmostFumulaExtrusion = record { 𝕆ne }
    open DoubleAlmostFumulaExtrusion doubleAlmostFumulaExtrusion public
      using (isDoubleAlmostFumulaExtrusion)

  module _ {f fℓ} (F : ReversibleAlmostFumula f fℓ) where

    almostFumulaExtrusion : AlmostFumulaExtrusion F x xℓ
    almostFumulaExtrusion = record { 𝕆ne }
    open AlmostFumulaExtrusion almostFumulaExtrusion public
      using (isAlmostFumulaExtrusion)

  module _ {f fℓ} (F : Fumula f fℓ) where

    leftFumulaExtrusion : LeftFumulaExtrusion F x xℓ
    leftFumulaExtrusion = record { 𝕆ne }
    open LeftFumulaExtrusion leftFumulaExtrusion public
      using (isLeftFumulaExtrusion)

    rightFumulaExtrusion : RightFumulaExtrusion F x xℓ
    rightFumulaExtrusion = record { 𝕆ne }
    open RightFumulaExtrusion rightFumulaExtrusion public
      using (isRightFumulaExtrusion)

  module _ {fₗ fᵣ fℓₗ fℓᵣ} (Fₗ : Fumula fₗ fℓₗ) (Fᵣ : Fumula fᵣ fℓᵣ) where

    doubleFumulaExtrusion : DoubleFumulaExtrusion Fₗ Fᵣ x xℓ
    doubleFumulaExtrusion = record { 𝕆ne }
    open DoubleFumulaExtrusion doubleFumulaExtrusion public
      using (isDoubleFumulaExtrusion)

  module _ {f fℓ} (F : ReversibleFumula f fℓ) where

    fumulaExtrusion : FumulaExtrusion F x xℓ
    fumulaExtrusion = record { 𝕆ne }
    open FumulaExtrusion fumulaExtrusion public
      using (isFumulaExtrusion)

module Initial {x xℓ} where

  module ℤero where

    Carrier : Set x
    Carrier = ⊥

    infix  4 _≈_
    _≈_ : Rel Carrier xℓ
    _≈_ ()

    refl : Reflexive _≈_
    refl {x = ()}

    sym : Symmetric _≈_
    sym {x = ()}

    module _ {f} {F : Set f} where

      infix 7 ❲_❳⤙_⤚_
      ❲_❳⤙_⤚_ : Op₃ₗ F Carrier
      ❲_❳⤙_⤚_ _ ()

      infix 7 _⤙_⤚❲_❳
      _⤙_⤚❲_❳ : Op₃ᵣ F Carrier
      _⤙_⤚❲_❳ ()

  open ℤero

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record { ℤero; trans = λ {i = i} → ⊥-elim i }

  module _ {f fℓ} (F : AlmostFumula f fℓ) where

    leftAlmostFumulaExtrusion : LeftAlmostFumulaExtrusion F x xℓ
    leftAlmostFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; ❲_❳⤙_⤚_ = ❲_❳⤙_⤚_
      ; isLeftAlmostFumulaExtrusion = record
        { isEquivalence = isEquivalence
        ; ❲❳⤙⤚-cong = λ {u = u} → ⊥-elim u
        ; ❲❳⤙⤚-double-exchange = λ _ ()
        }
      }
    open LeftAlmostFumulaExtrusion leftAlmostFumulaExtrusion public
      using (isLeftAlmostFumulaExtrusion)

    rightAlmostFumulaExtrusion : RightAlmostFumulaExtrusion F x xℓ
    rightAlmostFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _⤙_⤚❲_❳ = _⤙_⤚❲_❳
      ; isRightAlmostFumulaExtrusion = record
        { isEquivalence = isEquivalence
        ; ⤙⤚❲❳-cong = λ {x = x} → ⊥-elim x
        ; ⤙⤚❲❳-double-exchange = λ ()
        }
      }
    open RightAlmostFumulaExtrusion rightAlmostFumulaExtrusion public
      using (isRightAlmostFumulaExtrusion)

  module _ {fₗ fᵣ fℓₗ fℓᵣ} (Fₗ : AlmostFumula fₗ fℓₗ) (Fᵣ : AlmostFumula fᵣ fℓᵣ) where

    doubleAlmostFumulaExtrusion : DoubleAlmostFumulaExtrusion Fₗ Fᵣ x xℓ
    doubleAlmostFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; ❲_❳⤙_⤚_ = ❲_❳⤙_⤚_
      ; _⤙_⤚❲_❳ = _⤙_⤚❲_❳
      ; isDoubleAlmostFumulaExtrusion = record
        { isEquivalence = isEquivalence
        ; ❲❳⤙⤚-cong = λ {u = u} → ⊥-elim u
        ; ❲❳⤙⤚-double-exchange = λ _ ()
        ; ⤙⤚❲❳-cong = λ {x = x} → ⊥-elim x
        ; ⤙⤚❲❳-double-exchange = λ ()
        ; ❲❳⤙⤚-⤙⤚❲❳-double-exchange = λ _ ()
        }
      }
    open DoubleAlmostFumulaExtrusion doubleAlmostFumulaExtrusion public
      using (isDoubleAlmostFumulaExtrusion)

  module _ {f fℓ} (F : ReversibleAlmostFumula f fℓ) where

    almostFumulaExtrusion : AlmostFumulaExtrusion F x xℓ
    almostFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; ❲_❳⤙_⤚_ = ❲_❳⤙_⤚_
      ; _⤙_⤚❲_❳ = _⤙_⤚❲_❳
      ; isAlmostFumulaExtrusion = record
        { isDoubleAlmostFumulaExtrusion =
          let F′ = ReversibleAlmostFumula.almostFumula F
          in isDoubleAlmostFumulaExtrusion F′ F′
        ; outer-commute = λ ()
        }
      }
    open AlmostFumulaExtrusion almostFumulaExtrusion public
      using (isAlmostFumulaExtrusion)

  open Terminal {x} {xℓ} public
    hiding (module 𝕆ne; isEquivalence; leftAlmostFumulaExtrusion; rightAlmostFumulaExtrusion;
            doubleAlmostFumulaExtrusion; almostFumulaExtrusion)

module DirectProduct {x₁ xℓ₁ x₂ xℓ₂} where

  module _ {f fℓ} (F : AlmostFumula f fℓ) (X₁ : LeftAlmostFumulaExtrusion F x₁ xℓ₁) (X₂ : LeftAlmostFumulaExtrusion F x₂ xℓ₂) where
    private
      module X₁ = LeftAlmostFumulaExtrusion X₁
      module X₂ = LeftAlmostFumulaExtrusion X₂

    leftAlmostFumulaExtrusion : LeftAlmostFumulaExtrusion F (x₁ ⊔ x₂) (xℓ₁ ⊔ xℓ₂)
    leftAlmostFumulaExtrusion = record
      { Carrier = X₁.Carrier × X₂.Carrier
      ; _≈_ = Pointwise X₁._≈_ X₂._≈_
      ; ❲_❳⤙_⤚_ = λ s (z₁ , z₂) (x₁ , x₂) → (X₁.❲ s ❳⤙ z₁ ⤚ x₁) , (X₂.❲ s ❳⤙ z₂ ⤚ x₂)
      ; isLeftAlmostFumulaExtrusion = record
        { isEquivalence = ×-isEquivalence X₁.isEquivalence X₂.isEquivalence
        ; ❲❳⤙⤚-cong = λ s≈ (z₁≈ , z₂≈) (x₁≈ , x₂≈) → X₁.❲❳⤙⤚-cong s≈ z₁≈ x₁≈ , X₂.❲❳⤙⤚-cong s≈ z₂≈ x₂≈
        ; ❲❳⤙⤚-double-exchange = λ v (w₁ , w₂) x (y₁ , y₂) (z₁ , z₂) →
          X₁.❲❳⤙⤚-double-exchange v w₁ x y₁ z₁ , X₂.❲❳⤙⤚-double-exchange v w₂ x y₂ z₂
        }
      }
    open LeftAlmostFumulaExtrusion leftAlmostFumulaExtrusion public
      using (isLeftAlmostFumulaExtrusion)

  module _ {f fℓ} (F : AlmostFumula f fℓ) (X₁ : RightAlmostFumulaExtrusion F x₁ xℓ₁) (X₂ : RightAlmostFumulaExtrusion F x₂ xℓ₂) where
    private
      module X₁ = RightAlmostFumulaExtrusion X₁
      module X₂ = RightAlmostFumulaExtrusion X₂

    rightAlmostFumulaExtrusion : RightAlmostFumulaExtrusion F (x₁ ⊔ x₂) (xℓ₁ ⊔ xℓ₂)
    rightAlmostFumulaExtrusion = record
      { Carrier = X₁.Carrier × X₂.Carrier
      ; _≈_ = Pointwise X₁._≈_ X₂._≈_
      ; _⤙_⤚❲_❳ = λ (x₁ , x₂) (z₁ , z₂) s → (x₁ X₁.⤙ z₁ ⤚❲ s ❳) , (x₂ X₂.⤙ z₂ ⤚❲ s ❳)
      ; isRightAlmostFumulaExtrusion = record
        { isEquivalence = ×-isEquivalence X₁.isEquivalence X₂.isEquivalence
        ; ⤙⤚❲❳-cong = λ (x₁≈ , x₂≈) (z₁≈ , z₂≈) s≈ → X₁.⤙⤚❲❳-cong x₁≈ z₁≈ s≈ , X₂.⤙⤚❲❳-cong x₂≈ z₂≈ s≈
        ; ⤙⤚❲❳-double-exchange = λ (v₁ , v₂) w (x₁ , x₂) y (z₁ , z₂) →
          X₁.⤙⤚❲❳-double-exchange v₁ w x₁ y z₁ , X₂.⤙⤚❲❳-double-exchange v₂ w x₂ y z₂
        }
      }
    open RightAlmostFumulaExtrusion rightAlmostFumulaExtrusion public
      using (isRightAlmostFumulaExtrusion)

  module _ {fₗ fᵣ fℓₗ fℓᵣ} (Fₗ : AlmostFumula fₗ fℓₗ) (Fᵣ : AlmostFumula fᵣ fℓᵣ) (X₁ : DoubleAlmostFumulaExtrusion Fₗ Fᵣ x₁ xℓ₁) (X₂ : DoubleAlmostFumulaExtrusion Fₗ Fᵣ x₂ xℓ₂) where
    private
      module X₁ = DoubleAlmostFumulaExtrusion X₁
      module X₂ = DoubleAlmostFumulaExtrusion X₂

    doubleAlmostFumulaExtrusion : DoubleAlmostFumulaExtrusion Fₗ Fᵣ (x₁ ⊔ x₂) (xℓ₁ ⊔ xℓ₂)
    doubleAlmostFumulaExtrusion = record
      { Carrier = X₁.Carrier × X₂.Carrier
      ; _≈_ = Pointwise X₁._≈_ X₂._≈_
      ; ❲_❳⤙_⤚_ = λ s (z₁ , z₂) (x₁ , x₂) → (X₁.❲ s ❳⤙ z₁ ⤚ x₁) , (X₂.❲ s ❳⤙ z₂ ⤚ x₂)
      ; _⤙_⤚❲_❳ = λ (x₁ , x₂) (z₁ , z₂) s → (x₁ X₁.⤙ z₁ ⤚❲ s ❳) , (x₂ X₂.⤙ z₂ ⤚❲ s ❳)
      ; isDoubleAlmostFumulaExtrusion = record
        { isEquivalence = ×-isEquivalence X₁.isEquivalence X₂.isEquivalence
        ; ❲❳⤙⤚-cong = λ s≈ (z₁≈ , z₂≈) (x₁≈ , x₂≈) → X₁.❲❳⤙⤚-cong s≈ z₁≈ x₁≈ , X₂.❲❳⤙⤚-cong s≈ z₂≈ x₂≈
        ; ❲❳⤙⤚-double-exchange = λ v (w₁ , w₂) x (y₁ , y₂) (z₁ , z₂) →
          X₁.❲❳⤙⤚-double-exchange v w₁ x y₁ z₁ , X₂.❲❳⤙⤚-double-exchange v w₂ x y₂ z₂
        ; ⤙⤚❲❳-cong = λ (x₁≈ , x₂≈) (z₁≈ , z₂≈) s≈ → X₁.⤙⤚❲❳-cong x₁≈ z₁≈ s≈ , X₂.⤙⤚❲❳-cong x₂≈ z₂≈ s≈
        ; ⤙⤚❲❳-double-exchange = λ (v₁ , v₂) w (x₁ , x₂) y (z₁ , z₂) →
          X₁.⤙⤚❲❳-double-exchange v₁ w x₁ y z₁ , X₂.⤙⤚❲❳-double-exchange v₂ w x₂ y z₂
        ; ❲❳⤙⤚-⤙⤚❲❳-double-exchange = λ v (w₁ , w₂) (x₁ , x₂) y (z₁ , z₂) →
          X₁.❲❳⤙⤚-⤙⤚❲❳-double-exchange v w₁ x₁ y z₁ , X₂.❲❳⤙⤚-⤙⤚❲❳-double-exchange v w₂ x₂ y z₂
        }
      }
    open DoubleAlmostFumulaExtrusion doubleAlmostFumulaExtrusion public
      using (isDoubleAlmostFumulaExtrusion)

  module _ {f fℓ} (F : ReversibleAlmostFumula f fℓ) (X₁ : AlmostFumulaExtrusion F x₁ xℓ₁) (X₂ : AlmostFumulaExtrusion F x₂ xℓ₂) where
    private
      module X₁ = AlmostFumulaExtrusion X₁
      module X₂ = AlmostFumulaExtrusion X₂

    almostFumulaExtrusion : AlmostFumulaExtrusion F (x₁ ⊔ x₂) (xℓ₁ ⊔ xℓ₂)
    almostFumulaExtrusion = record
      { Carrier = X₁.Carrier × X₂.Carrier
      ; _≈_ = Pointwise X₁._≈_ X₂._≈_
      ; ❲_❳⤙_⤚_ = λ s (z₁ , z₂) (x₁ , x₂) → (X₁.❲ s ❳⤙ z₁ ⤚ x₁) , (X₂.❲ s ❳⤙ z₂ ⤚ x₂)
      ; _⤙_⤚❲_❳ = λ (x₁ , x₂) (z₁ , z₂) s → (x₁ X₁.⤙ z₁ ⤚❲ s ❳) , (x₂ X₂.⤙ z₂ ⤚❲ s ❳)
      ; isAlmostFumulaExtrusion = record
        { isDoubleAlmostFumulaExtrusion = 
          let F′ = ReversibleAlmostFumula.almostFumula F
          in isDoubleAlmostFumulaExtrusion F′ F′ X₁.doubleAlmostFumulaExtrusion X₂.doubleAlmostFumulaExtrusion
        ; outer-commute = λ (y₁ , y₂) x (z₁ , z₂) → X₁.outer-commute y₁ x z₁ , X₂.outer-commute y₂ x z₂
        }
      }
    open AlmostFumulaExtrusion almostFumulaExtrusion public
      using (isAlmostFumulaExtrusion)

  module _ {f fℓ} (F : Fumula f fℓ) (X₁ : LeftFumulaExtrusion F x₁ xℓ₁) (X₂ : LeftFumulaExtrusion F x₂ xℓ₂) where
    private
      module X₁ = LeftFumulaExtrusion X₁
      module X₂ = LeftFumulaExtrusion X₂

    leftFumulaExtrusion : LeftFumulaExtrusion F (x₁ ⊔ x₂) (xℓ₁ ⊔ xℓ₂)
    leftFumulaExtrusion = record
      { Carrier = X₁.Carrier × X₂.Carrier
      ; _≈_ = Pointwise X₁._≈_ X₂._≈_
      ; ❲_❳⤙_⤚_ = λ s (z₁ , z₂) (x₁ , x₂) → (X₁.❲ s ❳⤙ z₁ ⤚ x₁) , (X₂.❲ s ❳⤙ z₂ ⤚ x₂)
      ; ◆ = X₁.◆ , X₂.◆
      ; isLeftFumulaExtrusion = record
        { isLeftAlmostFumulaExtrusion =
          isLeftAlmostFumulaExtrusion (Fumula.almostFumula F) X₁.leftAlmostFumulaExtrusion X₂.leftAlmostFumulaExtrusion
        ; ❲❳⤙⤚-●ᶠ-inner-commuteʳ = λ (x₁ , x₂) (y₁ , y₂) → X₁.❲❳⤙⤚-●ᶠ-inner-commuteʳ x₁ y₁ , X₂.❲❳⤙⤚-●ᶠ-inner-commuteʳ x₂ y₂
        ; ❲❳⤙⤚-◆ᶠ-pulloutˡ = λ v w x (y₁ , y₂) (z₁ , z₂) → X₁.❲❳⤙⤚-◆ᶠ-pulloutˡ v w x y₁ z₁ , X₂.❲❳⤙⤚-◆ᶠ-pulloutˡ v w x y₂ z₂
        ; ❲❳⤙⤚-◆-pulloutʳ = λ (v₁ , v₂) w x (y₁ , y₂) (z₁ , z₂) → X₁.❲❳⤙⤚-◆-pulloutʳ v₁ w x y₁ z₁ , X₂.❲❳⤙⤚-◆-pulloutʳ v₂ w x y₂ z₂
        ; ❲❳⤙⤚-■ᶠ-collapse-dupʳ = λ (x₁ , x₂) → X₁.❲❳⤙⤚-■ᶠ-collapse-dupʳ x₁ , X₂.❲❳⤙⤚-■ᶠ-collapse-dupʳ x₂
        ; ❲❳⤙⤚-◆ᶠ-collapse-middleˡ = λ (x₁ , x₂) (z₁ , z₂) → X₁.❲❳⤙⤚-◆ᶠ-collapse-middleˡ x₁ z₁ , X₂.❲❳⤙⤚-◆ᶠ-collapse-middleˡ x₂ z₂
        ; ❲❳⤙⤚-◆-collapse-middleʳ = λ x (z₁ , z₂) → X₁.❲❳⤙⤚-◆-collapse-middleʳ x z₁ , X₂.❲❳⤙⤚-◆-collapse-middleʳ x z₂
        ; ❲❳⤙⤚-◆ᶠ-◆-outer-associate = λ w x (y₁ , y₂) (z₁ , z₂) → (X₁.❲❳⤙⤚-◆ᶠ-◆-outer-associate w x y₁ z₁) , X₂.❲❳⤙⤚-◆ᶠ-◆-outer-associate w x y₂ z₂
        }
      }
    open LeftFumulaExtrusion leftFumulaExtrusion public
      using (isLeftFumulaExtrusion)

  module _ {f fℓ} (F : Fumula f fℓ) (X₁ : RightFumulaExtrusion F x₁ xℓ₁) (X₂ : RightFumulaExtrusion F x₂ xℓ₂) where
    private
      module X₁ = RightFumulaExtrusion X₁
      module X₂ = RightFumulaExtrusion X₂

    rightFumulaExtrusion : RightFumulaExtrusion F (x₁ ⊔ x₂) (xℓ₁ ⊔ xℓ₂)
    rightFumulaExtrusion = record
      { Carrier = X₁.Carrier × X₂.Carrier
      ; _≈_ = Pointwise X₁._≈_ X₂._≈_
      ; _⤙_⤚❲_❳ = λ (x₁ , x₂) (z₁ , z₂) s → (x₁ X₁.⤙ z₁ ⤚❲ s ❳) , (x₂ X₂.⤙ z₂ ⤚❲ s ❳)
      ; ◆ = X₁.◆ , X₂.◆
      ; isRightFumulaExtrusion = record
        { isRightAlmostFumulaExtrusion =
          isRightAlmostFumulaExtrusion (Fumula.almostFumula F) X₁.rightAlmostFumulaExtrusion X₂.rightAlmostFumulaExtrusion
        ; ⤙⤚❲❳-●ᶠ-inner-commuteˡ = λ (x₁ , x₂) (y₁ , y₂) → X₁.⤙⤚❲❳-●ᶠ-inner-commuteˡ x₁ y₁ , X₂.⤙⤚❲❳-●ᶠ-inner-commuteˡ x₂ y₂
        ; ⤙⤚❲❳-◆-pulloutˡ = λ (v₁ , v₂) (w₁ , w₂) x y (z₁ , z₂) → X₁.⤙⤚❲❳-◆-pulloutˡ v₁ w₁ x y z₁ , X₂.⤙⤚❲❳-◆-pulloutˡ v₂ w₂ x y z₂
        ; ⤙⤚❲❳-◆ᶠ-pulloutʳ = λ (v₁ , v₂) (w₁ , w₂) x y z → X₁.⤙⤚❲❳-◆ᶠ-pulloutʳ v₁ w₁ x y z , X₂.⤙⤚❲❳-◆ᶠ-pulloutʳ v₂ w₂ x y z
        ; ⤙⤚❲❳-■ᶠ-collapse-dupˡ = λ (x₁ , x₂) → X₁.⤙⤚❲❳-■ᶠ-collapse-dupˡ x₁ , X₂.⤙⤚❲❳-■ᶠ-collapse-dupˡ x₂
        ; ⤙⤚❲❳-◆-collapse-middleˡ = λ x (z₁ , z₂) → X₁.⤙⤚❲❳-◆-collapse-middleˡ x z₁ , X₂.⤙⤚❲❳-◆-collapse-middleˡ x z₂
        ; ⤙⤚❲❳-◆ᶠ-collapse-middleʳ = λ (x₁ , x₂) (z₁ , z₂) → X₁.⤙⤚❲❳-◆ᶠ-collapse-middleʳ x₁ z₁ , X₂.⤙⤚❲❳-◆ᶠ-collapse-middleʳ x₂ z₂
        ; ⤙⤚❲❳-◆ᶠ-◆-outer-associate = λ (w₁ , w₂) x y (z₁ , z₂) → X₁.⤙⤚❲❳-◆ᶠ-◆-outer-associate w₁ x y z₁ , X₂.⤙⤚❲❳-◆ᶠ-◆-outer-associate w₂ x y z₂
        }
      }
    open RightFumulaExtrusion rightFumulaExtrusion public
      using (isRightFumulaExtrusion)

  module _ {fₗ fᵣ fℓₗ fℓᵣ} (Fₗ : Fumula fₗ fℓₗ) (Fᵣ : Fumula fᵣ fℓᵣ) (X₁ : DoubleFumulaExtrusion Fₗ Fᵣ x₁ xℓ₁) (X₂ : DoubleFumulaExtrusion Fₗ Fᵣ x₂ xℓ₂) where
    private
      module X₁ = DoubleFumulaExtrusion X₁
      module X₂ = DoubleFumulaExtrusion X₂

    doubleFumulaExtrusion : DoubleFumulaExtrusion Fₗ Fᵣ (x₁ ⊔ x₂) (xℓ₁ ⊔ xℓ₂)
    doubleFumulaExtrusion = record
      { Carrier = X₁.Carrier × X₂.Carrier
      ; _≈_ = Pointwise X₁._≈_ X₂._≈_
      ; ❲_❳⤙_⤚_ = λ s (z₁ , z₂) (x₁ , x₂) → (X₁.❲ s ❳⤙ z₁ ⤚ x₁) , (X₂.❲ s ❳⤙ z₂ ⤚ x₂)
      ; _⤙_⤚❲_❳ = λ (x₁ , x₂) (z₁ , z₂) s → (x₁ X₁.⤙ z₁ ⤚❲ s ❳) , (x₂ X₂.⤙ z₂ ⤚❲ s ❳)
      ; ◆ = X₁.◆ , X₂.◆
      ; isDoubleFumulaExtrusion = record
        { isDoubleAlmostFumulaExtrusion =
          isDoubleAlmostFumulaExtrusion (Fumula.almostFumula Fₗ) (Fumula.almostFumula Fᵣ) X₁.doubleAlmostFumulaExtrusion X₂.doubleAlmostFumulaExtrusion
        ; ❲❳⤙⤚-●ᶠ-inner-commuteʳ = λ (x₁ , x₂) (y₁ , y₂) → X₁.❲❳⤙⤚-●ᶠ-inner-commuteʳ x₁ y₁ , X₂.❲❳⤙⤚-●ᶠ-inner-commuteʳ x₂ y₂
        ; ❲❳⤙⤚-◆ᶠ-pulloutˡ = λ v w x (y₁ , y₂) (z₁ , z₂) → X₁.❲❳⤙⤚-◆ᶠ-pulloutˡ v w x y₁ z₁ , X₂.❲❳⤙⤚-◆ᶠ-pulloutˡ v w x y₂ z₂
        ; ❲❳⤙⤚-◆-pulloutʳ = λ (v₁ , v₂) w x (y₁ , y₂) (z₁ , z₂) → X₁.❲❳⤙⤚-◆-pulloutʳ v₁ w x y₁ z₁ , X₂.❲❳⤙⤚-◆-pulloutʳ v₂ w x y₂ z₂
        ; ❲❳⤙⤚-■ᶠ-collapse-dupʳ = λ (x₁ , x₂) → X₁.❲❳⤙⤚-■ᶠ-collapse-dupʳ x₁ , X₂.❲❳⤙⤚-■ᶠ-collapse-dupʳ x₂
        ; ❲❳⤙⤚-◆ᶠ-collapse-middleˡ = λ (x₁ , x₂) (z₁ , z₂) → X₁.❲❳⤙⤚-◆ᶠ-collapse-middleˡ x₁ z₁ , X₂.❲❳⤙⤚-◆ᶠ-collapse-middleˡ x₂ z₂
        ; ❲❳⤙⤚-◆-collapse-middleʳ = λ x (z₁ , z₂) → X₁.❲❳⤙⤚-◆-collapse-middleʳ x z₁ , X₂.❲❳⤙⤚-◆-collapse-middleʳ x z₂
        ; ❲❳⤙⤚-◆ᶠ-◆-outer-associate = λ w x (y₁ , y₂) (z₁ , z₂) → (X₁.❲❳⤙⤚-◆ᶠ-◆-outer-associate w x y₁ z₁) , X₂.❲❳⤙⤚-◆ᶠ-◆-outer-associate w x y₂ z₂
        ; ⤙⤚❲❳-●ᶠ-inner-commuteˡ = λ (x₁ , x₂) (y₁ , y₂) → X₁.⤙⤚❲❳-●ᶠ-inner-commuteˡ x₁ y₁ , X₂.⤙⤚❲❳-●ᶠ-inner-commuteˡ x₂ y₂
        ; ⤙⤚❲❳-◆-pulloutˡ = λ (v₁ , v₂) (w₁ , w₂) x y (z₁ , z₂) → X₁.⤙⤚❲❳-◆-pulloutˡ v₁ w₁ x y z₁ , X₂.⤙⤚❲❳-◆-pulloutˡ v₂ w₂ x y z₂
        ; ⤙⤚❲❳-◆ᶠ-pulloutʳ = λ (v₁ , v₂) (w₁ , w₂) x y z → X₁.⤙⤚❲❳-◆ᶠ-pulloutʳ v₁ w₁ x y z , X₂.⤙⤚❲❳-◆ᶠ-pulloutʳ v₂ w₂ x y z
        ; ⤙⤚❲❳-■ᶠ-collapse-dupˡ = λ (x₁ , x₂) → X₁.⤙⤚❲❳-■ᶠ-collapse-dupˡ x₁ , X₂.⤙⤚❲❳-■ᶠ-collapse-dupˡ x₂
        ; ⤙⤚❲❳-◆-collapse-middleˡ = λ x (z₁ , z₂) → X₁.⤙⤚❲❳-◆-collapse-middleˡ x z₁ , X₂.⤙⤚❲❳-◆-collapse-middleˡ x z₂
        ; ⤙⤚❲❳-◆ᶠ-collapse-middleʳ = λ (x₁ , x₂) (z₁ , z₂) → X₁.⤙⤚❲❳-◆ᶠ-collapse-middleʳ x₁ z₁ , X₂.⤙⤚❲❳-◆ᶠ-collapse-middleʳ x₂ z₂
        ; ⤙⤚❲❳-◆ᶠ-◆-outer-associate = λ (w₁ , w₂) x y (z₁ , z₂) → X₁.⤙⤚❲❳-◆ᶠ-◆-outer-associate w₁ x y z₁ , X₂.⤙⤚❲❳-◆ᶠ-◆-outer-associate w₂ x y z₂
        ; ⤙⤚❲❳-❲❳⤙⤚-◆-pulloutˡ = λ (v₁ , v₂) w (x₁ , x₂) y (z₁ , z₂) → X₁.⤙⤚❲❳-❲❳⤙⤚-◆-pulloutˡ v₁ w x₁ y z₁ , X₂.⤙⤚❲❳-❲❳⤙⤚-◆-pulloutˡ v₂ w x₂ y z₂
        ; ❲❳⤙⤚-⤙⤚❲❳-◆-pulloutʳ = λ (v₁ , v₂) w (x₁ , x₂) y (z₁ , z₂) → X₁.❲❳⤙⤚-⤙⤚❲❳-◆-pulloutʳ v₁ w x₁ y z₁ , X₂.❲❳⤙⤚-⤙⤚❲❳-◆-pulloutʳ v₂ w x₂ y z₂
        ; ■ᶠ-outer-commute = λ (x₁ , x₂) (z₁ , z₂) → X₁.■ᶠ-outer-commute x₁ z₁ , X₂.■ᶠ-outer-commute x₂ z₂
        ; ◆ᶠ-outer-commute = λ (x₁ , x₂) (z₁ , z₂) → X₁.◆ᶠ-outer-commute x₁ z₁ , X₂.◆ᶠ-outer-commute x₂ z₂
        ; ●ᶠ-outer-commute = λ (x₁ , x₂) (z₁ , z₂) → X₁.●ᶠ-outer-commute x₁ z₁ , X₂.●ᶠ-outer-commute x₂ z₂
        ; ◆-outer-associate = λ w (x₁ , x₂) y (z₁ , z₂) → X₁.◆-outer-associate w x₁ y z₁ , X₂.◆-outer-associate w x₂ y z₂
        }
      }
    open DoubleFumulaExtrusion doubleFumulaExtrusion public
      using (isDoubleFumulaExtrusion)

  module _ {f fℓ} (F : ReversibleFumula f fℓ) (X₁ : FumulaExtrusion F x₁ xℓ₁) (X₂ : FumulaExtrusion F x₂ xℓ₂) where
    private
      module X₁ = FumulaExtrusion X₁
      module X₂ = FumulaExtrusion X₂

    fumulaExtrusion : FumulaExtrusion F (x₁ ⊔ x₂) (xℓ₁ ⊔ xℓ₂)
    fumulaExtrusion = record
      { Carrier = X₁.Carrier × X₂.Carrier
      ; _≈_ = Pointwise X₁._≈_ X₂._≈_
      ; ❲_❳⤙_⤚_ = λ s (z₁ , z₂) (x₁ , x₂) → (X₁.❲ s ❳⤙ z₁ ⤚ x₁) , (X₂.❲ s ❳⤙ z₂ ⤚ x₂)
      ; _⤙_⤚❲_❳ = λ (x₁ , x₂) (z₁ , z₂) s → (x₁ X₁.⤙ z₁ ⤚❲ s ❳) , (x₂ X₂.⤙ z₂ ⤚❲ s ❳)
      ; ◆ = X₁.◆ , X₂.◆
      ; isFumulaExtrusion = record
        { isDoubleFumulaExtrusion =
          let F′ = ReversibleFumula.fumula F
          in isDoubleFumulaExtrusion F′ F′ X₁.doubleFumulaExtrusion X₂.doubleFumulaExtrusion
        ; outer-commute = λ (y₁ , y₂) x (z₁ , z₂) → X₁.outer-commute y₁ x z₁ , X₂.outer-commute y₂ x z₂
        }
      }
    open FumulaExtrusion fumulaExtrusion public
      using (isFumulaExtrusion)

module TensorUnit {f fℓ} where

  module _ (F : AlmostFumula f fℓ) where
    private
      module F = AlmostFumula F

    doubleAlmostFumulaExtrusion : DoubleAlmostFumulaExtrusion F F f fℓ
    doubleAlmostFumulaExtrusion = record
      { Carrier = F.Carrier
      ; _≈_ = F._≈_
      ; ❲_❳⤙_⤚_ = F._⤙_⤚_
      ; _⤙_⤚❲_❳ = F._⤙_⤚_
      ; isDoubleAlmostFumulaExtrusion = record
        { isEquivalence = F.isEquivalence
        ; ❲❳⤙⤚-cong = F.⤙⤚-cong
        ; ❲❳⤙⤚-double-exchange = F.double-exchange
        ; ⤙⤚❲❳-cong = F.⤙⤚-cong
        ; ⤙⤚❲❳-double-exchange = F.double-exchange
        ; ❲❳⤙⤚-⤙⤚❲❳-double-exchange = F.double-exchange
        }
      }
    open DoubleAlmostFumulaExtrusion doubleAlmostFumulaExtrusion public
      using (isDoubleAlmostFumulaExtrusion)
      renaming (❲❳⤙⤚-leftAlmostFumulaExtrusion to leftAlmostFumulaExtrusion;
                ❲❳⤙⤚-isLeftAlmostFumulaExtrusion to isLeftAlmostFumulaExtrusion;
                ⤙⤚❲❳-rightAlmostFumulaExtrusion to rightAlmostFumulaExtrusion;
                ⤙⤚❲❳-isRightAlmostFumulaExtrusion to isRightAlmostFumulaExtrusion)

  module _ (F : Fumula f fℓ) where
    private
      module F = Fumula F

    doubleFumulaExtrusion : DoubleFumulaExtrusion F F f fℓ
    doubleFumulaExtrusion = record
      { Carrier = F.Carrier
      ; _≈_ = F._≈_
      ; ❲_❳⤙_⤚_ = F._⤙_⤚_
      ; _⤙_⤚❲_❳ = F._⤙_⤚_
      ; ◆ = F.◆
      ; isDoubleFumulaExtrusion = record
        { isDoubleAlmostFumulaExtrusion = isDoubleAlmostFumulaExtrusion F.almostFumula
        ; ❲❳⤙⤚-●ᶠ-inner-commuteʳ = F.●-inner-commuteʳ
        ; ❲❳⤙⤚-◆ᶠ-pulloutˡ = F.◆-pulloutˡ
        ; ❲❳⤙⤚-◆-pulloutʳ = F.◆-pulloutʳ
        ; ❲❳⤙⤚-■ᶠ-collapse-dupʳ = F.■-collapse-dupˡ
        ; ❲❳⤙⤚-◆ᶠ-collapse-middleˡ = F.◆-collapse-middleˡ
        ; ❲❳⤙⤚-◆-collapse-middleʳ = F.◆-collapse-middleʳ
        ; ❲❳⤙⤚-◆ᶠ-◆-outer-associate = F.◆-outer-associate
        ; ⤙⤚❲❳-●ᶠ-inner-commuteˡ = F.●-inner-commuteˡ
        ; ⤙⤚❲❳-◆-pulloutˡ = F.◆-pulloutˡ
        ; ⤙⤚❲❳-◆ᶠ-pulloutʳ = F.◆-pulloutʳ
        ; ⤙⤚❲❳-■ᶠ-collapse-dupˡ = F.■-collapse-dupʳ
        ; ⤙⤚❲❳-◆-collapse-middleˡ = F.◆-collapse-middleˡ
        ; ⤙⤚❲❳-◆ᶠ-collapse-middleʳ = F.◆-collapse-middleʳ
        ; ⤙⤚❲❳-◆ᶠ-◆-outer-associate = F.◆-outer-associate
        ; ⤙⤚❲❳-❲❳⤙⤚-◆-pulloutˡ = F.◆-pulloutˡ
        ; ❲❳⤙⤚-⤙⤚❲❳-◆-pulloutʳ = F.◆-pulloutʳ
        ; ■ᶠ-outer-commute = λ x z → F.■-outer-commute x z
        ; ◆ᶠ-outer-commute = λ x z → F.◆-outer-commute x z
        ; ●ᶠ-outer-commute = λ x z → F.●-outer-commute x z
        ; ◆-outer-associate = F.◆-outer-associate
        }
      }
    open DoubleFumulaExtrusion doubleFumulaExtrusion public
      using (isDoubleFumulaExtrusion)
      renaming (❲❳⤙⤚-leftFumulaExtrusion to leftFumulaExtrusion;
                ❲❳⤙⤚-isLeftFumulaExtrusion to isLeftFumulaExtrusion;
                ⤙⤚❲❳-rightFumulaExtrusion to rightFumulaExtrusion;
                ⤙⤚❲❳-isRightFumulaExtrusion to isRightFumulaExtrusion)
