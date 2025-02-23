module Algebra.Fumula.Extrusion.Morphism where

open import Level using (_⊔_)
open import Function.Definitions
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Morphism.Structures
import Algebra.Morphism.Definitions
open import Algebra.Fumula.Bundles.Raw
open import Algebra.Fumula.Extrusion.Core
open import Algebra.Fumula.Extrusion.Bundles.Raw

module MorphismDefinitions {a x y ℓ} (A : Set a) (X : Set x) (Y : Set y) (_≈_ : Rel Y ℓ) where

  Homomorphic₃ₗ : (X → Y) → Op₃ₗ A X → Op₃ₗ A Y → Set _
  Homomorphic₃ₗ ⟦_⟧ ❲_❳⤙_⤚_ ❲_❳⟪_⟫_ =
    ∀ x y z → ⟦ ❲ x ❳⤙ y ⤚ z ⟧ ≈ (❲ x ❳⟪ ⟦ y ⟧ ⟫ ⟦ z ⟧)
  
  Homomorphic₃ᵣ : (X → Y) → Op₃ᵣ A X → Op₃ᵣ A Y → Set _
  Homomorphic₃ᵣ ⟦_⟧ _⤙_⤚❲_❳ _⟪_⟫❲_❳ =
    ∀ x y z → ⟦ x ⤙ y ⤚❲ z ❳ ⟧ ≈ (⟦ x ⟧ ⟪ ⟦ y ⟧ ⟫❲ z ❳)
  
  Homomorphic₃ₘ : (X → Y) → Op₃ₘ A X → Op₃ₘ A Y → Set _
  Homomorphic₃ₘ ⟦_⟧ _⤙❲_❳⤚_ _⟪❲_❳⟫_ =
    ∀ x y z → ⟦ x ⤙❲ y ❳⤚ z ⟧ ≈ (⟦ x ⟧ ⟪❲ y ❳⟫ ⟦ z ⟧)

module LeftAlmostFumulaExtrusionMorphisms {ℓfc ℓfe ℓxc₁ ℓxc₂ ℓxe₁ ℓxe₂} {F : RawAlmostFumula ℓfc ℓfe}
  (X₁ : RawLeftAlmostFumulaExtrusion F ℓxc₁ ℓxe₁) (X₂ : RawLeftAlmostFumulaExtrusion F ℓxc₂ ℓxe₂)
  where

  private
    open module F = RawAlmostFumula F using ()
      renaming (Carrier to V)
    open module X₁ = RawLeftAlmostFumulaExtrusion X₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_; ❲_❳⤙_⤚_ to ❲_❳⤙_⤚_)
    open module X₂ = RawLeftAlmostFumulaExtrusion X₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_; ❲_❳⤙_⤚_ to ❲_❳⟪_⟫_)
    open MorphismDefinitions V A B _≈₂_

  record IsLeftAlmostFumulaExtrusionHomomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where 
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      homo              : Homomorphic₃ₗ ⟦_⟧ ❲_❳⤙_⤚_ ❲_❳⟪_⟫_

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)

  record IsLeftAlmostFumulaExtrusionMonomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isLeftAlmostFumulaExtrusionHomomorphism : IsLeftAlmostFumulaExtrusionHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsLeftAlmostFumulaExtrusionHomomorphism isLeftAlmostFumulaExtrusionHomomorphism public

    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = isRelHomomorphism
      ; injective      = injective
      }

  record IsLeftAlmostFumulaExtrusionIsomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxc₂ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isLeftAlmostFumulaExtrusionMonomorphism : IsLeftAlmostFumulaExtrusionMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsLeftAlmostFumulaExtrusionMonomorphism isLeftAlmostFumulaExtrusionMonomorphism public

    isRelIsomorphism : IsRelIsomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelIsomorphism = record
      { isMonomorphism = isRelMonomorphism
      ; surjective     = surjective
      }

module RightAlmostFumulaExtrusionMorphisms {ℓfc ℓfe ℓxc₁ ℓxc₂ ℓxe₁ ℓxe₂} {F : RawAlmostFumula ℓfc ℓfe}
  (X₁ : RawRightAlmostFumulaExtrusion F ℓxc₁ ℓxe₁) (X₂ : RawRightAlmostFumulaExtrusion F ℓxc₂ ℓxe₂)
  where

  private
    open module F = RawAlmostFumula F using ()
      renaming (Carrier to V)
    open module X₁ = RawRightAlmostFumulaExtrusion X₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_; _⤙_⤚❲_❳ to _⤙_⤚❲_❳)
    open module X₂ = RawRightAlmostFumulaExtrusion X₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_; _⤙_⤚❲_❳ to _⟪_⟫❲_❳)
    open MorphismDefinitions V A B _≈₂_

  record IsRightAlmostFumulaExtrusionHomomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where 
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      homo              : Homomorphic₃ᵣ ⟦_⟧ _⤙_⤚❲_❳ _⟪_⟫❲_❳

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)

  record IsRightAlmostFumulaExtrusionMonomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isRightAlmostFumulaExtrusionHomomorphism : IsRightAlmostFumulaExtrusionHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsRightAlmostFumulaExtrusionHomomorphism isRightAlmostFumulaExtrusionHomomorphism public

    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = isRelHomomorphism
      ; injective      = injective
      }

  record IsRightAlmostFumulaExtrusionIsomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxc₂ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isRightAlmostFumulaExtrusionMonomorphism : IsRightAlmostFumulaExtrusionMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsRightAlmostFumulaExtrusionMonomorphism isRightAlmostFumulaExtrusionMonomorphism public

    isRelIsomorphism : IsRelIsomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelIsomorphism = record
      { isMonomorphism = isRelMonomorphism
      ; surjective     = surjective
      }

module DoubleAlmostFumulaExtrusionMorphisms {ℓfcₗ ℓfcᵣ ℓfeₗ ℓfeᵣ ℓxc₁ ℓxc₂ ℓxe₁ ℓxe₂}
  {Fₗ : RawAlmostFumula ℓfcₗ ℓfeₗ} {Fᵣ : RawAlmostFumula ℓfcᵣ ℓfeᵣ}
  (X₁ : RawDoubleAlmostFumulaExtrusion Fₗ Fᵣ ℓxc₁ ℓxe₁) (X₂ : RawDoubleAlmostFumulaExtrusion Fₗ Fᵣ ℓxc₂ ℓxe₂)
  where

  private
    open module Fₗ = RawAlmostFumula Fₗ using ()
      renaming (Carrier to Vₗ)
    open module Fᵣ = RawAlmostFumula Fᵣ using ()
      renaming (Carrier to Vᵣ)
    open module X₁ = RawDoubleAlmostFumulaExtrusion X₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_; ❲_❳⤙_⤚_ to ❲_❳⤙_⤚_; _⤙_⤚❲_❳ to _⤙_⤚❲_❳)
    open module X₂ = RawDoubleAlmostFumulaExtrusion X₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_; ❲_❳⤙_⤚_ to ❲_❳⟪_⟫_; _⤙_⤚❲_❳ to _⟪_⟫❲_❳)
    open module Defsₗ = MorphismDefinitions Vₗ A B _≈₂_ using (Homomorphic₃ₗ)
    open module Defsᵣ = MorphismDefinitions Vᵣ A B _≈₂_ using (Homomorphic₃ᵣ)
    open LeftAlmostFumulaExtrusionMorphisms X₁.❲❳⤙⤚-rawLeftAlmostFumulaExtrusion X₂.❲❳⤙⤚-rawLeftAlmostFumulaExtrusion
    open RightAlmostFumulaExtrusionMorphisms X₁.⤙⤚❲❳-rawRightAlmostFumulaExtrusion X₂.⤙⤚❲❳-rawRightAlmostFumulaExtrusion

  record IsDoubleAlmostFumulaExtrusionHomomorphism (⟦_⟧ : A → B) : Set (ℓfcₗ ⊔ ℓfcᵣ ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      ❲❳⤙⤚-homo             : Homomorphic₃ₗ ⟦_⟧ ❲_❳⤙_⤚_ ❲_❳⟪_⟫_
      ⤙⤚❲❳-homo             : Homomorphic₃ᵣ ⟦_⟧ _⤙_⤚❲_❳ _⟪_⟫❲_❳

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)

    isLeftAlmostFumulaExtrusionHomomorphism : IsLeftAlmostFumulaExtrusionHomomorphism ⟦_⟧
    isLeftAlmostFumulaExtrusionHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; homo = ❲❳⤙⤚-homo
      }

    isRightAlmostFumulaExtrusionHomomorphism : IsRightAlmostFumulaExtrusionHomomorphism ⟦_⟧
    isRightAlmostFumulaExtrusionHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; homo = ⤙⤚❲❳-homo
      }

  record IsDoubleAlmostFumulaExtrusionMonomorphism (⟦_⟧ : A → B) : Set (ℓfcₗ ⊔ ℓfcᵣ ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isDoubleAlmostFumulaExtrusionHomomorphism : IsDoubleAlmostFumulaExtrusionHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsDoubleAlmostFumulaExtrusionHomomorphism isDoubleAlmostFumulaExtrusionHomomorphism public

    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = isRelHomomorphism
      ; injective      = injective
      }

    isLeftAlmostFumulaExtrusionMonomorphism : IsLeftAlmostFumulaExtrusionMonomorphism ⟦_⟧
    isLeftAlmostFumulaExtrusionMonomorphism = record
      { isLeftAlmostFumulaExtrusionHomomorphism = isLeftAlmostFumulaExtrusionHomomorphism
      ; injective = injective
      }

    isRightAlmostFumulaExtrusionMonomorphism : IsRightAlmostFumulaExtrusionMonomorphism ⟦_⟧
    isRightAlmostFumulaExtrusionMonomorphism = record
      { isRightAlmostFumulaExtrusionHomomorphism = isRightAlmostFumulaExtrusionHomomorphism
      ; injective = injective
      }

  record IsDoubleAlmostFumulaExtrusionIsomorphism (⟦_⟧ : A → B) : Set (ℓfcₗ ⊔ ℓfcᵣ ⊔ ℓxc₁ ⊔ ℓxc₂ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isDoubleAlmostFumulaExtrusionMonomorphism : IsDoubleAlmostFumulaExtrusionMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsDoubleAlmostFumulaExtrusionMonomorphism isDoubleAlmostFumulaExtrusionMonomorphism public

    isRelIsomorphism : IsRelIsomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelIsomorphism = record
      { isMonomorphism = isRelMonomorphism
      ; surjective     = surjective
      }

    isLeftAlmostFumulaExtrusionIsomorphism : IsLeftAlmostFumulaExtrusionIsomorphism ⟦_⟧
    isLeftAlmostFumulaExtrusionIsomorphism = record
      { isLeftAlmostFumulaExtrusionMonomorphism = isLeftAlmostFumulaExtrusionMonomorphism
      ; surjective = surjective
      }

    isRightAlmostFumulaExtrusionIsomorphism : IsRightAlmostFumulaExtrusionIsomorphism ⟦_⟧
    isRightAlmostFumulaExtrusionIsomorphism = record
      { isRightAlmostFumulaExtrusionMonomorphism = isRightAlmostFumulaExtrusionMonomorphism
      ; surjective = surjective
      }

module AlmostFumulaExtrusionMorphisms {ℓfc ℓfe ℓxc₁ ℓxc₂ ℓxe₁ ℓxe₂} {F : RawAlmostFumula ℓfc ℓfe}
  (X₁ : RawAlmostFumulaExtrusion F ℓxc₁ ℓxe₁) (X₂ : RawAlmostFumulaExtrusion F ℓxc₂ ℓxe₂)
  where

  private
    open module F = RawAlmostFumula F using ()
      renaming (Carrier to V)
    open module X₁ = RawAlmostFumulaExtrusion X₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_; ❲_❳⤙_⤚_ to ❲_❳⤙_⤚_; _⤙_⤚❲_❳ to _⤙_⤚❲_❳)
    open module X₂ = RawAlmostFumulaExtrusion X₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_; ❲_❳⤙_⤚_ to ❲_❳⟪_⟫_; _⤙_⤚❲_❳ to _⟪_⟫❲_❳)
    open MorphismDefinitions V A B _≈₂_
    open DoubleAlmostFumulaExtrusionMorphisms X₁.rawDoubleAlmostFumulaExtrusion X₂.rawDoubleAlmostFumulaExtrusion

  record IsAlmostFumulaExtrusionHomomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where 
    field
      isDoubleAlmostFumulaExtrusionHomomorphism : IsDoubleAlmostFumulaExtrusionHomomorphism ⟦_⟧

    open IsDoubleAlmostFumulaExtrusionHomomorphism isDoubleAlmostFumulaExtrusionHomomorphism public

  record IsAlmostFumulaExtrusionMonomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isAlmostFumulaExtrusionHomomorphism : IsAlmostFumulaExtrusionHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsAlmostFumulaExtrusionHomomorphism isAlmostFumulaExtrusionHomomorphism public

  record IsAlmostFumulaExtrusionIsomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxc₂ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isAlmostFumulaExtrusionMonomorphism : IsAlmostFumulaExtrusionMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsAlmostFumulaExtrusionMonomorphism isAlmostFumulaExtrusionMonomorphism public

module LeftFumulaExtrusionMorphisms {ℓfc ℓfe ℓxc₁ ℓxc₂ ℓxe₁ ℓxe₂} {F : RawFumula ℓfc ℓfe}
  (X₁ : RawLeftFumulaExtrusion F ℓxc₁ ℓxe₁) (X₂ : RawLeftFumulaExtrusion F ℓxc₂ ℓxe₂)
  where

  private
    open module F = RawFumula F using ()
      renaming (Carrier to V)
    open module X₁ = RawLeftFumulaExtrusion X₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_; ❲_❳⤙_⤚_ to ❲_❳⤙_⤚_; ◆ to ◆)
    open module X₂ = RawLeftFumulaExtrusion X₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_; ❲_❳⤙_⤚_ to ❲_❳⟪_⟫_; ◆ to ◇)
    open Algebra.Morphism.Definitions A B _≈₂_
    open MorphismDefinitions V A B _≈₂_
    open LeftAlmostFumulaExtrusionMorphisms X₁.rawLeftAlmostFumulaExtrusion X₂.rawLeftAlmostFumulaExtrusion

  record IsLeftFumulaExtrusionHomomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isLeftAlmostFumulaExtrusionHomomorphism : IsLeftAlmostFumulaExtrusionHomomorphism ⟦_⟧
      ◆-homo              : Homomorphic₀ ⟦_⟧ ◆ ◇

    open IsLeftAlmostFumulaExtrusionHomomorphism isLeftAlmostFumulaExtrusionHomomorphism public
      renaming (homo to ❲❳⤙⤚-homo)

  record IsLeftFumulaExtrusionMonomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isLeftFumulaExtrusionHomomorphism : IsLeftFumulaExtrusionHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsLeftFumulaExtrusionHomomorphism isLeftFumulaExtrusionHomomorphism public

    isLeftAlmostFumulaExtrusionMonomorphism : IsLeftAlmostFumulaExtrusionMonomorphism ⟦_⟧
    isLeftAlmostFumulaExtrusionMonomorphism = record
      { isLeftAlmostFumulaExtrusionHomomorphism = isLeftAlmostFumulaExtrusionHomomorphism
      ; injective = injective
      }

  record IsLeftFumulaExtrusionIsomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxc₂ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isLeftFumulaExtrusionMonomorphism : IsLeftFumulaExtrusionMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsLeftFumulaExtrusionMonomorphism isLeftFumulaExtrusionMonomorphism public

    isLeftAlmostFumulaExtrusionIsomorphism : IsLeftAlmostFumulaExtrusionIsomorphism ⟦_⟧
    isLeftAlmostFumulaExtrusionIsomorphism = record
      { isLeftAlmostFumulaExtrusionMonomorphism = isLeftAlmostFumulaExtrusionMonomorphism
      ; surjective = surjective
      }

module RightFumulaExtrusionMorphisms {ℓfc ℓfe ℓxc₁ ℓxc₂ ℓxe₁ ℓxe₂} {F : RawFumula ℓfc ℓfe}
  (X₁ : RawRightFumulaExtrusion F ℓxc₁ ℓxe₁) (X₂ : RawRightFumulaExtrusion F ℓxc₂ ℓxe₂)
  where

  private
    open module F = RawFumula F using ()
      renaming (Carrier to V)
    open module X₁ = RawRightFumulaExtrusion X₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_; _⤙_⤚❲_❳ to _⤙_⤚❲_❳; ◆ to ◆)
    open module X₂ = RawRightFumulaExtrusion X₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_; _⤙_⤚❲_❳ to _⟪_⟫❲_❳; ◆ to ◇)
    open Algebra.Morphism.Definitions A B _≈₂_
    open MorphismDefinitions V A B _≈₂_
    open RightAlmostFumulaExtrusionMorphisms X₁.rawRightAlmostFumulaExtrusion X₂.rawRightAlmostFumulaExtrusion

  record IsRightFumulaExtrusionHomomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isRightAlmostFumulaExtrusionHomomorphism : IsRightAlmostFumulaExtrusionHomomorphism ⟦_⟧
      ◆-homo              : Homomorphic₀ ⟦_⟧ ◆ ◇

    open IsRightAlmostFumulaExtrusionHomomorphism isRightAlmostFumulaExtrusionHomomorphism public
      renaming (homo to ⤙⤚❲❳-homo)

  record IsRightFumulaExtrusionMonomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isRightFumulaExtrusionHomomorphism : IsRightFumulaExtrusionHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsRightFumulaExtrusionHomomorphism isRightFumulaExtrusionHomomorphism public

    isRightAlmostFumulaExtrusionMonomorphism : IsRightAlmostFumulaExtrusionMonomorphism ⟦_⟧
    isRightAlmostFumulaExtrusionMonomorphism = record
      { isRightAlmostFumulaExtrusionHomomorphism = isRightAlmostFumulaExtrusionHomomorphism
      ; injective = injective
      }

  record IsRightFumulaExtrusionIsomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxc₂ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isRightFumulaExtrusionMonomorphism : IsRightFumulaExtrusionMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsRightFumulaExtrusionMonomorphism isRightFumulaExtrusionMonomorphism public

    isRightAlmostFumulaExtrusionIsomorphism : IsRightAlmostFumulaExtrusionIsomorphism ⟦_⟧
    isRightAlmostFumulaExtrusionIsomorphism = record
      { isRightAlmostFumulaExtrusionMonomorphism = isRightAlmostFumulaExtrusionMonomorphism
      ; surjective = surjective
      }

module DoubleFumulaExtrusionMorphisms {ℓfcₗ ℓfcᵣ ℓfeₗ ℓfeᵣ ℓxc₁ ℓxc₂ ℓxe₁ ℓxe₂}
  {Fₗ : RawFumula ℓfcₗ ℓfeₗ} {Fᵣ : RawFumula ℓfcᵣ ℓfeᵣ}
  (X₁ : RawDoubleFumulaExtrusion Fₗ Fᵣ ℓxc₁ ℓxe₁) (X₂ : RawDoubleFumulaExtrusion Fₗ Fᵣ ℓxc₂ ℓxe₂)
  where

  private
    open module Fₗ = RawFumula Fₗ using ()
      renaming (Carrier to Vₗ)
    open module Fᵣ = RawFumula Fᵣ using ()
      renaming (Carrier to Vᵣ)
    open module X₁ = RawDoubleFumulaExtrusion X₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_; ❲_❳⤙_⤚_ to ❲_❳⤙_⤚_; _⤙_⤚❲_❳ to _⤙_⤚❲_❳; ◆ to ◆)
    open module X₂ = RawDoubleFumulaExtrusion X₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_; ❲_❳⤙_⤚_ to ❲_❳⟪_⟫_; _⤙_⤚❲_❳ to _⟪_⟫❲_❳; ◆ to ◇)
    open Algebra.Morphism.Definitions A B _≈₂_
    open module Defsₗ = MorphismDefinitions Vₗ A B _≈₂_ using (Homomorphic₃ₗ)
    open module Defsᵣ = MorphismDefinitions Vᵣ A B _≈₂_ using (Homomorphic₃ᵣ)
    open LeftFumulaExtrusionMorphisms X₁.❲❳⤙⤚-rawLeftFumulaExtrusion X₂.❲❳⤙⤚-rawLeftFumulaExtrusion
    open RightFumulaExtrusionMorphisms X₁.⤙⤚❲❳-rawRightFumulaExtrusion X₂.⤙⤚❲❳-rawRightFumulaExtrusion
    open DoubleAlmostFumulaExtrusionMorphisms X₁.rawDoubleAlmostFumulaExtrusion X₂.rawDoubleAlmostFumulaExtrusion

  record IsDoubleFumulaExtrusionHomomorphism (⟦_⟧ : A → B) : Set (ℓfcₗ ⊔ ℓfcᵣ ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      ❲❳⤙⤚-homo             : Homomorphic₃ₗ ⟦_⟧ ❲_❳⤙_⤚_ ❲_❳⟪_⟫_
      ⤙⤚❲❳-homo             : Homomorphic₃ᵣ ⟦_⟧ _⤙_⤚❲_❳ _⟪_⟫❲_❳
      ◆-homo              : Homomorphic₀ ⟦_⟧ ◆ ◇

    isDoubleAlmostFumulaExtrusionHomomorphism : IsDoubleAlmostFumulaExtrusionHomomorphism ⟦_⟧
    isDoubleAlmostFumulaExtrusionHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; ❲❳⤙⤚-homo = ❲❳⤙⤚-homo
      ; ⤙⤚❲❳-homo = ⤙⤚❲❳-homo
      }

    open IsDoubleAlmostFumulaExtrusionHomomorphism isDoubleAlmostFumulaExtrusionHomomorphism public
      hiding (isRelHomomorphism; ❲❳⤙⤚-homo; ⤙⤚❲❳-homo)

    isLeftFumulaExtrusionHomomorphism : IsLeftFumulaExtrusionHomomorphism ⟦_⟧
    isLeftFumulaExtrusionHomomorphism = record
      { isLeftAlmostFumulaExtrusionHomomorphism = isLeftAlmostFumulaExtrusionHomomorphism
      ; ◆-homo = ◆-homo
      }

    isRightFumulaExtrusionHomomorphism : IsRightFumulaExtrusionHomomorphism ⟦_⟧
    isRightFumulaExtrusionHomomorphism = record
      { isRightAlmostFumulaExtrusionHomomorphism = isRightAlmostFumulaExtrusionHomomorphism
      ; ◆-homo = ◆-homo
      }

  record IsDoubleFumulaExtrusionMonomorphism (⟦_⟧ : A → B) : Set (ℓfcₗ ⊔ ℓfcᵣ ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isDoubleFumulaExtrusionHomomorphism : IsDoubleFumulaExtrusionHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsDoubleFumulaExtrusionHomomorphism isDoubleFumulaExtrusionHomomorphism public

    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = isRelHomomorphism
      ; injective      = injective
      }

    isLeftFumulaExtrusionMonomorphism : IsLeftFumulaExtrusionMonomorphism ⟦_⟧
    isLeftFumulaExtrusionMonomorphism = record
      { isLeftFumulaExtrusionHomomorphism = isLeftFumulaExtrusionHomomorphism
      ; injective = injective
      }

    open IsLeftFumulaExtrusionMonomorphism isLeftFumulaExtrusionMonomorphism public
      using (isLeftAlmostFumulaExtrusionMonomorphism)

    isRightFumulaExtrusionMonomorphism : IsRightFumulaExtrusionMonomorphism ⟦_⟧
    isRightFumulaExtrusionMonomorphism = record
      { isRightFumulaExtrusionHomomorphism = isRightFumulaExtrusionHomomorphism
      ; injective = injective
      }

    open IsRightFumulaExtrusionMonomorphism isRightFumulaExtrusionMonomorphism public
      using (isRightAlmostFumulaExtrusionMonomorphism)

    isDoubleAlmostFumulaExtrusionMonomorphism : IsDoubleAlmostFumulaExtrusionMonomorphism ⟦_⟧
    isDoubleAlmostFumulaExtrusionMonomorphism = record
      { isDoubleAlmostFumulaExtrusionHomomorphism = isDoubleAlmostFumulaExtrusionHomomorphism
      ; injective = injective
      }

  record IsDoubleFumulaExtrusionIsomorphism (⟦_⟧ : A → B) : Set (ℓfcₗ ⊔ ℓfcᵣ ⊔ ℓxc₁ ⊔ ℓxc₂ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isDoubleFumulaExtrusionMonomorphism : IsDoubleFumulaExtrusionMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsDoubleFumulaExtrusionMonomorphism isDoubleFumulaExtrusionMonomorphism public

    isRelIsomorphism : IsRelIsomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelIsomorphism = record
      { isMonomorphism = isRelMonomorphism
      ; surjective     = surjective
      }

    isLeftFumulaExtrusionIsomorphism : IsLeftFumulaExtrusionIsomorphism ⟦_⟧
    isLeftFumulaExtrusionIsomorphism = record
      { isLeftFumulaExtrusionMonomorphism = isLeftFumulaExtrusionMonomorphism
      ; surjective = surjective
      }

    open IsLeftFumulaExtrusionIsomorphism isLeftFumulaExtrusionIsomorphism public
      using (isLeftAlmostFumulaExtrusionIsomorphism)

    isRightFumulaExtrusionIsomorphism : IsRightFumulaExtrusionIsomorphism ⟦_⟧
    isRightFumulaExtrusionIsomorphism = record
      { isRightFumulaExtrusionMonomorphism = isRightFumulaExtrusionMonomorphism
      ; surjective = surjective
      }

    open IsRightFumulaExtrusionIsomorphism isRightFumulaExtrusionIsomorphism public
      using (isRightAlmostFumulaExtrusionIsomorphism)

    isDoubleAlmostFumulaExtrusionIsomorphism : IsDoubleAlmostFumulaExtrusionIsomorphism ⟦_⟧
    isDoubleAlmostFumulaExtrusionIsomorphism = record
      { isDoubleAlmostFumulaExtrusionMonomorphism = isDoubleAlmostFumulaExtrusionMonomorphism
      ; surjective = surjective
      }

module FumulaExtrusionMorphisms {ℓfc ℓfe ℓxc₁ ℓxc₂ ℓxe₁ ℓxe₂} {F : RawFumula ℓfc ℓfe}
  (X₁ : RawFumulaExtrusion F ℓxc₁ ℓxe₁) (X₂ : RawFumulaExtrusion F ℓxc₂ ℓxe₂)
  where

  private
    open module F = RawFumula F using ()
      renaming (Carrier to V)
    open module X₁ = RawFumulaExtrusion X₁ using ()
      renaming (Carrier to A; _≈_ to _≈₁_; ❲_❳⤙_⤚_ to ❲_❳⤙_⤚_; _⤙_⤚❲_❳ to _⤙_⤚❲_❳; ◆ to ◆)
    open module X₂ = RawFumulaExtrusion X₂ using ()
      renaming (Carrier to B; _≈_ to _≈₂_; ❲_❳⤙_⤚_ to ❲_❳⟪_⟫_; _⤙_⤚❲_❳ to _⟪_⟫❲_❳; ◆ to ◇)
    open Algebra.Morphism.Definitions A B _≈₂_
    open MorphismDefinitions V A B _≈₂_
    open DoubleFumulaExtrusionMorphisms X₁.rawDoubleFumulaExtrusion X₂.rawDoubleFumulaExtrusion
    open AlmostFumulaExtrusionMorphisms X₁.rawAlmostFumulaExtrusion X₂.rawAlmostFumulaExtrusion

  record IsFumulaExtrusionHomomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isDoubleFumulaExtrusionHomomorphism : IsDoubleFumulaExtrusionHomomorphism ⟦_⟧

    open IsDoubleFumulaExtrusionHomomorphism isDoubleFumulaExtrusionHomomorphism public

    isAlmostFumulaExtrusionHomomorphism : IsAlmostFumulaExtrusionHomomorphism ⟦_⟧
    isAlmostFumulaExtrusionHomomorphism = record
      { isDoubleAlmostFumulaExtrusionHomomorphism = isDoubleAlmostFumulaExtrusionHomomorphism
      }

  record IsFumulaExtrusionMonomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isFumulaExtrusionHomomorphism : IsFumulaExtrusionHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsFumulaExtrusionHomomorphism isFumulaExtrusionHomomorphism public

    isDoubleFumulaExtrusionMonomorphism : IsDoubleFumulaExtrusionMonomorphism ⟦_⟧
    isDoubleFumulaExtrusionMonomorphism = record
      { isDoubleFumulaExtrusionHomomorphism = isDoubleFumulaExtrusionHomomorphism
      ; injective = injective
      }

    isAlmostFumulaExtrusionMonomorphism : IsAlmostFumulaExtrusionMonomorphism ⟦_⟧
    isAlmostFumulaExtrusionMonomorphism = record
      { isAlmostFumulaExtrusionHomomorphism = isAlmostFumulaExtrusionHomomorphism
      ; injective = injective
      }

  record IsFumulaExtrusionIsomorphism (⟦_⟧ : A → B) : Set (ℓfc ⊔ ℓxc₁ ⊔ ℓxc₂ ⊔ ℓxe₁ ⊔ ℓxe₂) where
    field
      isFumulaExtrusionMonomorphism : IsFumulaExtrusionMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsFumulaExtrusionMonomorphism isFumulaExtrusionMonomorphism public

    isDoubleFumulaExtrusionIsomorphism : IsDoubleFumulaExtrusionIsomorphism ⟦_⟧
    isDoubleFumulaExtrusionIsomorphism = record
      { isDoubleFumulaExtrusionMonomorphism = isDoubleFumulaExtrusionMonomorphism
      ; surjective = surjective
      }

    isAlmostFumulaExtrusionIsomorphism : IsAlmostFumulaExtrusionIsomorphism ⟦_⟧
    isAlmostFumulaExtrusionIsomorphism = record
      { isAlmostFumulaExtrusionMonomorphism = isAlmostFumulaExtrusionMonomorphism
      ; surjective = surjective
      }
