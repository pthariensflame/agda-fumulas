------------------------------------------------------------------------
-- Properties of nonuniform ternary operations on setoids
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Definitions where

open import Data.Product.Base using (_×_)
open import Relation.Binary.Core using (Rel)
open import Algebra.Fumula.Core
open import Algebra.Fumula.Extrusion.Core

module LeftDefs {a b ℓb} {A : Set a} {B : Set b} (❲_❳⤙_⤚_ : Op₃ₗ A B) (_≈ᵇ_ : Rel B ℓb) where

  Congruent₃ : ∀{ℓa} → Rel A ℓa → Set _
  Congruent₃ _≈ᵃ_ = ❲_❳⤙_⤚_ Preserves₃ _≈ᵃ_ ⟶ _≈ᵇ_ ⟶ _≈ᵇ_ ⟶ _≈ᵇ_

  RightInnerCommutativeWith : A → Set _
  RightInnerCommutativeWith e = ∀ x y → (❲ e ❳⤙ x ⤚ y) ≈ᵇ (❲ e ❳⤙ y ⤚ x)

  MiddleNestedDoubleExchange : Set _
  MiddleNestedDoubleExchange = ∀ v w x y z → (❲ v ❳⤙ ❲ x ❳⤙ z ⤚ y ⤚ w) ≈ᵇ (❲ x ❳⤙ ❲ v ❳⤙ z ⤚ w ⤚ y)

  OuterAssociativeWith : (_⤙_⤚_ : Op₃ A) → A → B → Set _
  OuterAssociativeWith _⤙_⤚_ eᶠ e = ∀ w x y z → (❲ w ⤙ eᶠ ⤚ x ❳⤙ z ⤚ y) ≈ᵇ (❲ w ❳⤙ z ⤚ ❲ x ❳⤙ e ⤚ y)

  LeftPulloutWith : (_⤙_⤚_ : Op₃ A) → A → Set _
  LeftPulloutWith _⤙_⤚_ e = ∀ v w x y z → (❲ w ⤙ v ⤚ x ❳⤙ z ⤚ y) ≈ᵇ (❲ w ⤙ e ⤚ x ❳⤙ ❲ v ❳⤙ z ⤚ y ⤚ y)

  RightPulloutWith : B → Set _
  RightPulloutWith e = ∀ v w x y z → (❲ w ❳⤙ v ⤚ (❲ x ❳⤙ z ⤚ y)) ≈ᵇ (❲ w ❳⤙ ❲ w ❳⤙ v ⤚ z ⤚ (❲ x ❳⤙ e ⤚ y))

module RightDefs {a b ℓb} {A : Set a} {B : Set b} (_⤙_⤚❲_❳ : Op₃ᵣ A B) (_≈ᵇ_ : Rel B ℓb) where

  Congruent₃ : ∀{ℓa} → Rel A ℓa → Set _
  Congruent₃ _≈ᵃ_ = _⤙_⤚❲_❳ Preserves₃ _≈ᵇ_ ⟶ _≈ᵇ_ ⟶ _≈ᵃ_ ⟶ _≈ᵇ_

  LeftInnerCommutativeWith : A → Set _
  LeftInnerCommutativeWith e = ∀ x y → (x ⤙ y ⤚❲ e ❳) ≈ᵇ (y ⤙ x ⤚❲ e ❳)

  MiddleNestedDoubleExchange : Set _
  MiddleNestedDoubleExchange = ∀ v w x y z → (v ⤙ x ⤙ z ⤚❲ y ❳ ⤚❲ w ❳) ≈ᵇ (x ⤙ v ⤙ z ⤚❲ w ❳ ⤚❲ y ❳)

  OuterAssociativeWith : Op₃ A → A → B → Set _
  OuterAssociativeWith _⤙_⤚_ eᶠ e = ∀ w x y z → (w ⤙ e ⤚❲ x ❳ ⤙ z ⤚❲ y ❳) ≈ᵇ (w ⤙ z ⤚❲ x ⤙ eᶠ ⤚ y ❳)

  LeftPulloutWith : B → Set _
  LeftPulloutWith e = ∀ v w x y z → ((w ⤙ v ⤚❲ x ❳) ⤙ z ⤚❲ y ❳) ≈ᵇ ((w ⤙ e ⤚❲ x ❳) ⤙ v ⤙ z ⤚❲ y ❳ ⤚❲ y ❳)

  RightPulloutWith : Op₃ A → A → Set _
  RightPulloutWith _⤙_⤚_ e = ∀ v w x y z → (w ⤙ v ⤚❲ x ⤙ z ⤚ y ❳) ≈ᵇ (w ⤙ w ⤙ v ⤚❲ z ❳ ⤚❲ x ⤙ e ⤚ y ❳)

module BiDefs {aₗ aᵣ b ℓb} {Aₗ : Set aₗ} {Aᵣ : Set aᵣ} {B : Set b} (❲_❳⤙_⤚_ : Op₃ₗ Aₗ B) (_⤙_⤚❲_❳ : Op₃ᵣ Aᵣ B) (_≈ᵇ_ : Rel B ℓb) where
  private
    module L = LeftDefs ❲_❳⤙_⤚_ _≈ᵇ_
    module R = RightDefs _⤙_⤚❲_❳ _≈ᵇ_

  MiddleNestedDoubleExchange : Set _
  MiddleNestedDoubleExchange = ∀ v w x y z → (❲ v ❳⤙ x ⤙ z ⤚❲ y ❳ ⤚ w) ≈ᵇ (x ⤙ ❲ v ❳⤙ z ⤚ w ⤚❲ y ❳)

  OuterAssociativeWith : B → Set _
  OuterAssociativeWith e = ∀ w x y z → ((❲ w ❳⤙ e ⤚ x) ⤙ z ⤚❲ y ❳) ≈ᵇ (❲ w ❳⤙ z ⤚ (x ⤙ e ⤚❲ y ❳))

  PulloutWith : B → Set _
  PulloutWith e = R.LeftPulloutWith e × L.RightPulloutWith e

module SimultaneousBiDefs {a b ℓb} {A : Set a} {B : Set b} (❲_❳⤙_⤚_ : Op₃ₗ A B) (_⤙_⤚❲_❳ : Op₃ᵣ A B) (_≈ᵇ_ : Rel B ℓb) where
  private
    module L = LeftDefs ❲_❳⤙_⤚_ _≈ᵇ_
    module R = RightDefs _⤙_⤚❲_❳ _≈ᵇ_

  OuterCommutativeWithUnderlying : A → Set _
  OuterCommutativeWithUnderlying e = ∀ x z → (x ⤙ z ⤚❲ e ❳) ≈ᵇ (❲ e ❳⤙ z ⤚ x)

  OuterCommutativeWith : B → Set _
  OuterCommutativeWith e = ∀ x z → (❲ x ❳⤙ z ⤚ e) ≈ᵇ (e ⤙ z ⤚❲ x ❳)

  OuterCommutative : Set _
  OuterCommutative = ∀ y → OuterCommutativeWith y

  InnerCommutativeWith : A → Set _
  InnerCommutativeWith e = R.LeftInnerCommutativeWith e × L.RightInnerCommutativeWith e

  PulloutWith : Op₃ A → A → Set _
  PulloutWith _⤙_⤚_ e = L.LeftPulloutWith _⤙_⤚_ e × R.RightPulloutWith _⤙_⤚_ e
