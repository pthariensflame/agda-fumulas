module Algebra.Fumula.Construct where
open import Level using (Level; _⊔_)
open import Data.Empty.Polymorphic
open import Data.Unit.Polymorphic
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (Pointwise; ×-isEquivalence)
open import Algebra.Fumula.Core
open import Algebra.Fumula.Definitions
open import Algebra.Fumula.Structures
open import Algebra.Fumula.Bundles

module Terminal {c ℓ} where

  module 𝕆ne where

    Carrier : Set c
    Carrier = ⊤

    infix  4 _≈_
    _≈_ : Rel Carrier ℓ
    _ ≈ _ = ⊤

  open 𝕆ne

  rawAlmostFumula : RawAlmostFumula c ℓ
  rawAlmostFumula = record { 𝕆ne }

  rawFumula : RawFumula c ℓ
  rawFumula = record { 𝕆ne }

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record { 𝕆ne }

  almostFumula : AlmostFumula c ℓ
  almostFumula = record { 𝕆ne }
  open AlmostFumula almostFumula public using (isAlmostFumula)

  reversibleAlmostFumula : ReversibleAlmostFumula c ℓ
  reversibleAlmostFumula = record { 𝕆ne }
  open ReversibleAlmostFumula reversibleAlmostFumula public using (isReversibleAlmostFumula)

  fumula : Fumula c ℓ
  fumula = record { 𝕆ne }
  open Fumula fumula public using (isFumula)

  reversibleFumula : ReversibleFumula c ℓ
  reversibleFumula = record { 𝕆ne }
  open ReversibleFumula reversibleFumula public using (isReversibleFumula)

module Initial {c ℓ} where

  module ℤero where

    Carrier : Set c
    Carrier = ⊥

    infix 4 _≈_
    _≈_ : Rel Carrier ℓ
    _≈_ ()

    infix 7 _⤙_⤚_
    _⤙_⤚_ : Op₃ Carrier
    _⤙_⤚_ ()

    refl : Reflexive _≈_
    refl {x = ()}

    sym : Symmetric _≈_
    sym {x = ()}

  open ℤero

  rawAlmostFumula : RawAlmostFumula c ℓ
  rawAlmostFumula = record { ℤero }

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record { ℤero ; trans = λ {i = i} → ⊥-elim i }

  isAlmostFumula : IsAlmostFumula _≈_ _⤙_⤚_
  isAlmostFumula = record { isEquivalence = isEquivalence ; ⤙⤚-cong = λ {x = x} → ⊥-elim x ; double-exchange = λ () }

  isReversibleAlmostFumula : IsReversibleAlmostFumula _≈_ _⤙_⤚_
  isReversibleAlmostFumula = record { isAlmostFumula = isAlmostFumula ; outer-commute = λ () }

  almostFumula : AlmostFumula c ℓ
  almostFumula = record { isAlmostFumula = isAlmostFumula }

  reversibleAlmostFumula : ReversibleAlmostFumula c ℓ
  reversibleAlmostFumula = record { isReversibleAlmostFumula = isReversibleAlmostFumula }

  open Terminal {c} {ℓ} public
    hiding (module 𝕆ne; rawAlmostFumula; isEquivalence;
           isAlmostFumula; almostFumula;
           isReversibleAlmostFumula; reversibleAlmostFumula)

module Reverse where

  reverse : ∀{c} {Carrier : Set c} → Op₃ Carrier → Op₃ Carrier
  reverse _⤙_⤚_ x z y = y ⤙ z ⤚ x

  preserves₃ : ∀{c ℓ} {Carrier : Set c} (∼ ≈ ≋ ≂ : Rel Carrier ℓ) {_⤙_⤚_ : Op₃ Carrier}
             → _⤙_⤚_ Preserves₃ ∼ ⟶ ≈ ⟶ ≋ ⟶ ≂ → reverse _⤙_⤚_ Preserves₃ ≋ ⟶ ≈ ⟶ ∼ ⟶ ≂
  preserves₃ _ _ _ _ pres x≋y u≈v n∼m = pres n∼m u≈v x≋y

  module _ {c ℓ} {Carrier : Set c} (_≈_ : Rel Carrier ℓ) (_⤙_⤚_ : Op₃ Carrier) where

    outer-commute-with : Symmetric _≈_ → ∀ e → OuterCommutativeWith _≈_ _⤙_⤚_ e → OuterCommutativeWith _≈_ (reverse _⤙_⤚_) e
    outer-commute-with sym e ⤙⤚-outer-commute x z = sym (⤙⤚-outer-commute x z)

    outer-commute : OuterCommutative _≈_ _⤙_⤚_ → OuterCommutative _≈_ (reverse _⤙_⤚_)
    outer-commute ⤙⤚-outer-commute x z y = ⤙⤚-outer-commute z x y

    left→right-inner-commute-with : ∀ e → LeftInnerCommutativeWith _≈_ _⤙_⤚_ e → RightInnerCommutativeWith _≈_ (reverse _⤙_⤚_) e
    left→right-inner-commute-with e ⤙⤚-inner-commuteˡ x y = ⤙⤚-inner-commuteˡ y x

    right→left-inner-commute-with : ∀ e → RightInnerCommutativeWith _≈_ _⤙_⤚_ e → LeftInnerCommutativeWith _≈_ (reverse _⤙_⤚_) e
    right→left-inner-commute-with e ⤙⤚-inner-commuteʳ x y = ⤙⤚-inner-commuteʳ y x

    inner-commute-with : ∀ e → InnerCommutativeWith _≈_ _⤙_⤚_ e → InnerCommutativeWith _≈_ (reverse _⤙_⤚_) e
    inner-commute-with e (⤙⤚-inner-commuteˡ , ⤙⤚-inner-commuteʳ) =
      right→left-inner-commute-with e ⤙⤚-inner-commuteʳ , left→right-inner-commute-with e ⤙⤚-inner-commuteˡ

    double-exchange : MiddleNestedDoubleExchange _≈_ _⤙_⤚_ → MiddleNestedDoubleExchange _≈_ (reverse _⤙_⤚_)
    double-exchange ⤙⤚-double-exchange v w x y z = ⤙⤚-double-exchange w v y x z

    outer-associate-with : Symmetric _≈_ → ∀ e → OuterAssociativeWith _≈_ _⤙_⤚_ e → OuterAssociativeWith _≈_ (reverse _⤙_⤚_) e
    outer-associate-with sym e ⤙⤚-outer-associate w x y z = sym (⤙⤚-outer-associate y x w z)

    left→right-pullout-with : ∀ e → LeftPulloutWith _≈_ _⤙_⤚_ e → RightPulloutWith _≈_ (reverse _⤙_⤚_) e
    left→right-pullout-with e ⤙⤚-pulloutˡ v w x y z = ⤙⤚-pulloutˡ z y x w v

    right→left-pullout-with : ∀ e → RightPulloutWith _≈_ _⤙_⤚_ e → LeftPulloutWith _≈_ (reverse _⤙_⤚_) e
    right→left-pullout-with e ⤙⤚-pulloutʳ v w x y z = ⤙⤚-pulloutʳ z y x w v

    pullout-with : ∀ e → PulloutWith _≈_ _⤙_⤚_ e → PulloutWith _≈_ (reverse _⤙_⤚_) e
    pullout-with e (⤙⤚-pulloutˡ , ⤙⤚-pulloutʳ) =
      right→left-pullout-with e ⤙⤚-pulloutʳ , left→right-pullout-with e ⤙⤚-pulloutˡ

  module _ {c ℓ} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {_⤙_⤚_ : Op₃ Carrier} where
  
    isAlmostFumula : IsAlmostFumula _≈_ _⤙_⤚_ → IsAlmostFumula _≈_ (reverse _⤙_⤚_)
    isAlmostFumula F = record
      { isEquivalence = F.isEquivalence
      ; ⤙⤚-cong = preserves₃ _≈_ _≈_ _≈_ _≈_ F.⤙⤚-cong
      ; double-exchange = double-exchange _≈_ _⤙_⤚_ F.double-exchange
      }
      where module F = IsAlmostFumula F

    isReversibleAlmostFumula : IsReversibleAlmostFumula _≈_ _⤙_⤚_ → IsReversibleAlmostFumula _≈_ (reverse _⤙_⤚_)
    isReversibleAlmostFumula F = record
      { isAlmostFumula = isAlmostFumula F.isAlmostFumula
      ; outer-commute = outer-commute _≈_ _⤙_⤚_ F.outer-commute
      }
      where module F = IsReversibleAlmostFumula F

  module _ {c ℓ} {Carrier : Set c} {_≈_ : Rel Carrier ℓ} {_⤙_⤚_ : Op₃ Carrier} {■ : Carrier} where
  
    isFumula : IsFumula _≈_ _⤙_⤚_ ■ → IsFumula _≈_ (reverse _⤙_⤚_) ■
    isFumula F = record
      { isAlmostFumula = isAlmostFumula F.isAlmostFumula
      ; ■-outer-commute = outer-commute-with _≈_ _⤙_⤚_ F.sym ■ F.■-outer-commute
      ; ■-collapse-dup = F.■-collapse-dupʳ , F.■-collapse-dupˡ
      ; ◆-outer-commute = outer-commute-with _≈_ _⤙_⤚_ F.sym (RawFumula.◆ F.rawFumula) F.◆-outer-commute
      ; ◆-collapse-middle = F.◆-collapse-middleʳ , F.◆-collapse-middleˡ
      ; ●-outer-commute = outer-commute-with _≈_ _⤙_⤚_ F.sym (RawFumula.● F.rawFumula) F.●-outer-commute
      ; ●-inner-commute = inner-commute-with _≈_ _⤙_⤚_ (RawFumula.● F.rawFumula) F.●-inner-commute
      ; ◆-outer-associate = outer-associate-with _≈_ _⤙_⤚_ F.sym (RawFumula.◆ F.rawFumula) F.◆-outer-associate
      ; ◆-pullout = pullout-with _≈_ _⤙_⤚_ (RawFumula.◆ F.rawFumula) F.◆-pullout
      }
      where module F = IsFumula F

    isReversibleFumula : IsReversibleFumula _≈_ _⤙_⤚_ ■ → IsReversibleFumula _≈_ (reverse _⤙_⤚_) ■
    isReversibleFumula F = record
      { isFumula = isFumula F.isFumula
      ; outer-commute = outer-commute _≈_ _⤙_⤚_ F.outer-commute
      }
      where module F = IsReversibleFumula F

  module _ {c ℓ} where

    rawAlmostFumula : RawAlmostFumula c ℓ → RawAlmostFumula c ℓ
    rawAlmostFumula F = record { _≈_ = F._≈_ ; _⤙_⤚_ = reverse F._⤙_⤚_ }
      where module F = RawAlmostFumula F

    rawFumula : RawFumula c ℓ → RawFumula c ℓ
    rawFumula F = record { _≈_ = F._≈_ ; _⤙_⤚_ = reverse F._⤙_⤚_ ; ■ = F.■ }
      where module F = RawFumula F

    almostFumula : AlmostFumula c ℓ → AlmostFumula c ℓ
    almostFumula F = record { isAlmostFumula = isAlmostFumula F.isAlmostFumula }
      where module F = AlmostFumula F

    reversibleAlmostFumula : ReversibleAlmostFumula c ℓ → ReversibleAlmostFumula c ℓ
    reversibleAlmostFumula F = record { isReversibleAlmostFumula = isReversibleAlmostFumula F.isReversibleAlmostFumula }
      where module F = ReversibleAlmostFumula F

    fumula : Fumula c ℓ → Fumula c ℓ
    fumula F = record { isFumula = isFumula F.isFumula }
      where module F = Fumula F

    reversibleFumula : ReversibleFumula c ℓ → ReversibleFumula c ℓ
    reversibleFumula F = record { isReversibleFumula = isReversibleFumula F.isReversibleFumula }
      where module F = ReversibleFumula F

module DirectProduct {c₁ ℓ₁ c₂ ℓ₂} where

  rawAlmostFumula : RawAlmostFumula c₁ ℓ₁ → RawAlmostFumula c₂ ℓ₂ → RawAlmostFumula (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂)
  rawAlmostFumula F₁ F₂ = record
    { Carrier = F₁.Carrier × F₂.Carrier
    ; _≈_ = Pointwise F₁._≈_ F₂._≈_
    ; _⤙_⤚_ = λ (x₁ , x₂) (z₁ , z₂) (y₁ , y₂) → (x₁ F₁.⤙ z₁ ⤚ y₁) , (x₂ F₂.⤙ z₂ ⤚ y₂)
    }
    where
      module F₁ = RawAlmostFumula F₁
      module F₂ = RawAlmostFumula F₂

  rawFumula : RawFumula c₁ ℓ₁ → RawFumula c₂ ℓ₂ → RawFumula (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂)
  rawFumula F₁ F₂ = record
    { Carrier = Almost.Carrier
    ; _≈_ = Almost._≈_
    ; _⤙_⤚_ = Almost._⤙_⤚_
    ; ■ = F₁.■ , F₂.■
    }
    where
      module F₁ = RawFumula F₁
      module F₂ = RawFumula F₂
      module Almost = RawAlmostFumula (rawAlmostFumula F₁.rawAlmostFumula F₂.rawAlmostFumula)

  almostFumula : AlmostFumula c₁ ℓ₁ → AlmostFumula c₂ ℓ₂ → AlmostFumula (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂)
  almostFumula F₁ F₂ = record
    { Carrier = Raw.Carrier
    ; _≈_ = Raw._≈_
    ; _⤙_⤚_ = Raw._⤙_⤚_
    ; isAlmostFumula = record
      { isEquivalence = ×-isEquivalence F₁.isEquivalence F₂.isEquivalence
      ; ⤙⤚-cong = λ (x₁≈ , x₂≈) (z₁≈ , z₂≈) (y₁≈ , y₂≈) → F₁.⤙⤚-cong x₁≈ z₁≈ y₁≈ , F₂.⤙⤚-cong x₂≈ z₂≈ y₂≈
      ; double-exchange = λ (v₁ , v₂) (w₁ , w₂) (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) →
        F₁.double-exchange v₁ w₁ x₁ y₁ z₁ , F₂.double-exchange v₂ w₂ x₂ y₂ z₂
      }
    }
    where
      module F₁ = AlmostFumula F₁
      module F₂ = AlmostFumula F₂
      module Raw = RawAlmostFumula (rawAlmostFumula F₁.rawAlmostFumula F₂.rawAlmostFumula)
  module _ F₁ F₂ where
    open AlmostFumula (almostFumula F₁ F₂) public using (isAlmostFumula)

  reversibleAlmostFumula : ReversibleAlmostFumula c₁ ℓ₁ → ReversibleAlmostFumula c₂ ℓ₂ → ReversibleAlmostFumula (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂)
  reversibleAlmostFumula F₁ F₂ = record
    { Carrier = Unrev.Carrier
    ; _≈_ = Unrev._≈_
    ; _⤙_⤚_ = Unrev._⤙_⤚_
    ; isReversibleAlmostFumula = record
      { isAlmostFumula = Unrev.isAlmostFumula
      ; outer-commute = λ (y₁ , y₂) (x₁ , x₂) (z₁ , z₂) → F₁.outer-commute y₁ x₁ z₁ , F₂.outer-commute y₂ x₂ z₂
      }
    }
    where
      module F₁ = ReversibleAlmostFumula F₁
      module F₂ = ReversibleAlmostFumula F₂
      module Unrev = AlmostFumula (almostFumula F₁.almostFumula F₂.almostFumula)
  module _ F₁ F₂ where
    open ReversibleAlmostFumula (reversibleAlmostFumula F₁ F₂) public using (isReversibleAlmostFumula)

  fumula : Fumula c₁ ℓ₁ → Fumula c₂ ℓ₂ → Fumula (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂)
  fumula F₁ F₂ = record
    { Carrier = Raw.Carrier
    ; _≈_ = Raw._≈_
    ; _⤙_⤚_ = Raw._⤙_⤚_
    ; ■ = Raw.■
    ; isFumula = record
      { isAlmostFumula = Almost.isAlmostFumula
      ; ■-outer-commute = λ (x₁ , x₂) (z₁ , z₂) → F₁.■-outer-commute x₁ z₁ , F₂.■-outer-commute x₂ z₂
      ; ■-collapse-dup =
        (λ (x₁ , x₂) → F₁.■-collapse-dupˡ x₁ , F₂.■-collapse-dupˡ x₂) ,
        (λ (x₁ , x₂) → F₁.■-collapse-dupʳ x₁ , F₂.■-collapse-dupʳ x₂)
      ; ◆-outer-commute = λ (x₁ , x₂) (z₁ , z₂) → F₁.◆-outer-commute x₁ z₁ , F₂.◆-outer-commute x₂ z₂
      ; ◆-collapse-middle =
        (λ (x₁ , x₂) (z₁ , z₂) → F₁.◆-collapse-middleˡ x₁ z₁ , F₂.◆-collapse-middleˡ x₂ z₂) ,
        (λ (x₁ , x₂) (z₁ , z₂) → F₁.◆-collapse-middleʳ x₁ z₁ , F₂.◆-collapse-middleʳ x₂ z₂)
      ; ●-outer-commute = λ (x₁ , x₂) (z₁ , z₂) → F₁.●-outer-commute x₁ z₁ , F₂.●-outer-commute x₂ z₂
      ; ●-inner-commute =
        (λ (x₁ , x₂) (y₁ , y₂) → F₁.●-inner-commuteˡ x₁ y₁ , F₂.●-inner-commuteˡ x₂ y₂) ,
        (λ (x₁ , x₂) (y₁ , y₂) → F₁.●-inner-commuteʳ x₁ y₁ , F₂.●-inner-commuteʳ x₂ y₂)
      ; ◆-outer-associate = λ (w₁ , w₂) (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) →
        F₁.◆-outer-associate w₁ x₁ y₁ z₁ , F₂.◆-outer-associate w₂ x₂ y₂ z₂
      ; ◆-pullout =
        (λ (v₁ , v₂) (w₁ , w₂) (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) →
          F₁.◆-pulloutˡ v₁ w₁ x₁ y₁ z₁ , F₂.◆-pulloutˡ v₂ w₂ x₂ y₂ z₂) ,
        (λ (v₁ , v₂) (w₁ , w₂) (x₁ , x₂) (y₁ , y₂) (z₁ , z₂) →
          F₁.◆-pulloutʳ v₁ w₁ x₁ y₁ z₁ , F₂.◆-pulloutʳ v₂ w₂ x₂ y₂ z₂)
      }
    }
    where
      module F₁ = Fumula F₁
      module F₂ = Fumula F₂
      module Raw = RawFumula (rawFumula F₁.rawFumula F₂.rawFumula)
      module Almost = AlmostFumula (almostFumula F₁.almostFumula F₂.almostFumula)
  module _ F₁ F₂ where
    open Fumula (fumula F₁ F₂) public using (isFumula)

  reversibleFumula : ReversibleFumula c₁ ℓ₁ → ReversibleFumula c₂ ℓ₂ → ReversibleFumula (c₁ ⊔ c₂) (ℓ₁ ⊔ ℓ₂)
  reversibleFumula F₁ F₂ = record
    { Carrier = Unrev.Carrier
    ; _≈_ = Unrev._≈_
    ; _⤙_⤚_ = Unrev._⤙_⤚_
    ; ■ = Unrev.■
    ; isReversibleFumula = record
      { isFumula = Unrev.isFumula
      ; outer-commute = Almost.outer-commute
      }
    }
    where
      module F₁ = ReversibleFumula F₁
      module F₂ = ReversibleFumula F₂
      module Unrev = Fumula (fumula F₁.fumula F₂.fumula)
      module Almost = ReversibleAlmostFumula (reversibleAlmostFumula F₁.reversibleAlmostFumula F₂.reversibleAlmostFumula)
  module _ F₁ F₂ where
    open ReversibleFumula (reversibleFumula F₁ F₂) public using (isReversibleFumula)

module Pointwise {a} (A : Set a) where
  private
    variable
      c ℓ : Level
      C : Set c
      _≈_ : Rel C ℓ
      ■ ◆ ● : C
      _⤙_⤚_ : Op₃ C

    lift₀ : C → A → C
    lift₀ x _ = x

    lift₃ : Op₃ C → Op₃ (A → C)
    lift₃ _⤙_⤚_ x z y i = x i ⤙ z i ⤚ y i

    liftRel : Rel C ℓ → Rel (A → C) (a ⊔ ℓ)
    liftRel _≈_ g h = ∀{x} → (g x) ≈ (h x)

    isEquivalence : IsEquivalence _≈_ → IsEquivalence (liftRel _≈_)
    isEquivalence E = record
      { refl = λ {x} {i} → E.refl {x i}
      ; sym = λ x≈y → E.sym x≈y
      ; trans = λ x≈y y≈z → E.trans x≈y y≈z
      }
      where module E = IsEquivalence E

  rawAlmostFumula : RawAlmostFumula c ℓ → RawAlmostFumula (a ⊔ c) (a ⊔ ℓ)
  rawAlmostFumula F = record
    { Carrier = A → F.Carrier
    ; _≈_ = liftRel F._≈_
    ; _⤙_⤚_ = lift₃ F._⤙_⤚_
    }
    where module F = RawAlmostFumula F

  rawFumula : RawFumula c ℓ → RawFumula (a ⊔ c) (a ⊔ ℓ)
  rawFumula F = record
    { Carrier = A → F.Carrier
    ; _≈_ = liftRel F._≈_
    ; _⤙_⤚_ = lift₃ F._⤙_⤚_
    ; ■ = lift₀ F.■
    }
    where module F = RawFumula F

  isAlmostFumula : IsAlmostFumula _≈_ _⤙_⤚_ → IsAlmostFumula (liftRel _≈_) (lift₃ _⤙_⤚_)
  isAlmostFumula F = record
    { isEquivalence = isEquivalence F.isEquivalence
    ; ⤙⤚-cong = λ x≈y u≈v n≈m → F.⤙⤚-cong x≈y u≈v n≈m
    ; double-exchange = λ v w x y z {i} → F.double-exchange (v i) (w i) (x i) (y i) (z i)
    }
    where module F = IsAlmostFumula F

  isReversibleAlmostFumula : IsReversibleAlmostFumula _≈_ _⤙_⤚_ → IsReversibleAlmostFumula (liftRel _≈_) (lift₃ _⤙_⤚_)
  isReversibleAlmostFumula F = record
    { isAlmostFumula = isAlmostFumula F.isAlmostFumula
    ; outer-commute = λ y x z {i} → F.outer-commute (y i) (x i) (z i)
    }
    where module F = IsReversibleAlmostFumula F

  isFumula : IsFumula _≈_ _⤙_⤚_ ■ → IsFumula (liftRel _≈_) (lift₃ _⤙_⤚_) (lift₀ ■)
  isFumula F = record
    { isAlmostFumula = isAlmostFumula F.isAlmostFumula
    ; ■-outer-commute = λ x z {i} → F.■-outer-commute (x i) (z i)
    ; ■-collapse-dup = (λ x {i} → F.■-collapse-dupˡ (x i)) , (λ x {i} → F.■-collapse-dupʳ (x i))
    ; ◆-outer-commute = λ x z {i} → F.◆-outer-commute (x i) (z i)
    ; ◆-collapse-middle = (λ x z {i} → F.◆-collapse-middleˡ (x i) (z i)) , (λ x z {i} → F.◆-collapse-middleʳ (x i) (z i))
    ; ●-outer-commute = λ x z {i} → F.●-outer-commute (x i) (z i)
    ; ●-inner-commute = (λ x y {i} → F.●-inner-commuteˡ (x i) (y i)) , (λ x y {i} → F.●-inner-commuteʳ (x i) (y i))
    ; ◆-outer-associate = λ w x y z {i} → F.◆-outer-associate (w i) (x i) (y i) (z i)
    ; ◆-pullout = (λ v w x y z {i} → F.◆-pulloutˡ (v i) (w i) (x i) (y i) (z i)) , (λ v w x y z {i} → F.◆-pulloutʳ (v i) (w i) (x i) (y i) (z i))
    }
    where module F = IsFumula F

  isReversibleFumula : IsReversibleFumula _≈_ _⤙_⤚_ ■ → IsReversibleFumula (liftRel _≈_) (lift₃ _⤙_⤚_) (lift₀ ■)
  isReversibleFumula F = record
    { isFumula = isFumula F.isFumula
    ; outer-commute = λ y x z {i} → F.outer-commute (y i) (x i) (z i)
    }
    where module F = IsReversibleFumula F

  almostFumula : AlmostFumula c ℓ → AlmostFumula (a ⊔ c) (a ⊔ ℓ)
  almostFumula F = record { isAlmostFumula = isAlmostFumula F.isAlmostFumula }
    where module F = AlmostFumula F

  reversibleAlmostFumula : ReversibleAlmostFumula c ℓ → ReversibleAlmostFumula (a ⊔ c) (a ⊔ ℓ)
  reversibleAlmostFumula F = record { isReversibleAlmostFumula = isReversibleAlmostFumula F.isReversibleAlmostFumula }
    where module F = ReversibleAlmostFumula F

  fumula : Fumula c ℓ → Fumula (a ⊔ c) (a ⊔ ℓ)
  fumula F = record { isFumula = isFumula F.isFumula }
    where module F = Fumula F

  reversibleFumula : ReversibleFumula c ℓ → ReversibleFumula (a ⊔ c) (a ⊔ ℓ)
  reversibleFumula F = record { isReversibleFumula = isReversibleFumula F.isReversibleFumula }
    where module F = ReversibleFumula F
