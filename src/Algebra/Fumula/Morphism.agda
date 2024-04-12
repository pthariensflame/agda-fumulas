------------------------------------------------------------------------
-- Morphisms of fumulas.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.

module Algebra.Fumula.Morphism where

open import Level using (_⊔_)
open import Function.Definitions
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Morphism.Structures
open import Algebra.Fumula.Core
open import Algebra.Fumula.Bundles.Raw

module MorphismDefinitions {a b ℓ} (A : Set a) (B : Set b) (_≈_ : Rel B ℓ) where

  open import Algebra.Morphism.Definitions A B _≈_ public

  Homomorphic₃ : (A → B) → Op₃ A → Op₃ B → Set _
  Homomorphic₃ ⟦_⟧ _⤙_⤚_ _⟪_⟫_ = ∀ x y z → ⟦ x ⤙ y ⤚ z ⟧ ≈ (⟦ x ⟧ ⟪ ⟦ y ⟧ ⟫ ⟦ z ⟧)

module AlmostFumulaMorphisms {a b ℓ₁ ℓ₂} (F₁ : RawAlmostFumula a ℓ₁) (F₂ : RawAlmostFumula b ℓ₂) where

  private
    open module F₁ = RawAlmostFumula F₁ using () renaming (Carrier to A; _≈_ to _≈₁_; _⤙_⤚_ to _⤙_⤚_)
    open module F₂ = RawAlmostFumula F₂ using () renaming (Carrier to B; _≈_ to _≈₂_; _⤙_⤚_ to _⟪_⟫_)
    open MorphismDefinitions A B _≈₂_

  record IsAlmostFumulaHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isRelHomomorphism : IsRelHomomorphism _≈₁_ _≈₂_ ⟦_⟧
      homo              : Homomorphic₃ ⟦_⟧ _⤙_⤚_ _⟪_⟫_

    open IsRelHomomorphism isRelHomomorphism public
      renaming (cong to ⟦⟧-cong)


  record IsAlmostFumulaMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isAlmostFumulaHomomorphism : IsAlmostFumulaHomomorphism ⟦_⟧
      injective           : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsAlmostFumulaHomomorphism isAlmostFumulaHomomorphism public

    isRelMonomorphism : IsRelMonomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelMonomorphism = record
      { isHomomorphism = isRelHomomorphism
      ; injective      = injective
      }


  record IsAlmostFumulaIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isAlmostFumulaMonomorphism : IsAlmostFumulaMonomorphism ⟦_⟧
      surjective          : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsAlmostFumulaMonomorphism isAlmostFumulaMonomorphism public

    isRelIsomorphism : IsRelIsomorphism _≈₁_ _≈₂_ ⟦_⟧
    isRelIsomorphism = record
      { isMonomorphism = isRelMonomorphism
      ; surjective     = surjective
      }

module FumulaMorphisms {a b ℓ₁ ℓ₂} (F₁ : RawFumula a ℓ₁) (F₂ : RawFumula b ℓ₂) where

  private
    open module F₁ = RawFumula F₁ using () renaming (Carrier to A; _≈_ to _≈₁_; _⤙_⤚_ to _⤙_⤚_; ■ to ■)
    open module F₂ = RawFumula F₂ using () renaming (Carrier to B; _≈_ to _≈₂_; _⤙_⤚_ to _⟪_⟫_; ■ to □)
    open MorphismDefinitions A B _≈₂_
    open AlmostFumulaMorphisms F₁.rawAlmostFumula F₂.rawAlmostFumula

  record IsFumulaHomomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isAlmostFumulaHomomorphism : IsAlmostFumulaHomomorphism ⟦_⟧
      ■-homo              : Homomorphic₀ ⟦_⟧ ■ □

    open IsAlmostFumulaHomomorphism isAlmostFumulaHomomorphism public
      renaming (homo to ⤙⤚-homo)


  record IsFumulaMonomorphism (⟦_⟧ : A → B) : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isFumulaHomomorphism : IsFumulaHomomorphism ⟦_⟧
      injective            : Injective _≈₁_ _≈₂_ ⟦_⟧

    open IsFumulaHomomorphism isFumulaHomomorphism public

    isAlmostFumulaMonomorphism : IsAlmostFumulaMonomorphism ⟦_⟧
    isAlmostFumulaMonomorphism = record
      { isAlmostFumulaHomomorphism = isAlmostFumulaHomomorphism
      ; injective           = injective
      }

    open IsAlmostFumulaMonomorphism isAlmostFumulaMonomorphism public
      using (isRelMonomorphism)


  record IsFumulaIsomorphism (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      isFumulaMonomorphism : IsFumulaMonomorphism ⟦_⟧
      surjective           : Surjective _≈₁_ _≈₂_ ⟦_⟧

    open IsFumulaMonomorphism isFumulaMonomorphism public

    isAlmostFumulaIsomorphism : IsAlmostFumulaIsomorphism ⟦_⟧
    isAlmostFumulaIsomorphism = record
      { isAlmostFumulaMonomorphism = isAlmostFumulaMonomorphism
      ; surjective          = surjective
      }

    open IsAlmostFumulaIsomorphism isAlmostFumulaIsomorphism public
      using (isRelIsomorphism)

------------------------------------------------------------------------
-- Re-export contents of modules publicly

open AlmostFumulaMorphisms public
open FumulaMorphisms public
