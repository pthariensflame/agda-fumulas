------------------------------------------------------------------------
-- Properties of ternary operations on setoids
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`, unless
-- you want to parameterise it via the equality relation and/or the ternary
-- operator.

open import Level using (Level)
open import Relation.Binary.Core using (Rel)
open import Algebra.Fumula.Core

module Algebra.Fumula.Definitions
  {a ℓ} {A : Set a}   -- The underlying set
  (_≈_ : Rel A ℓ)     -- The underlying equality
  (_⤙_⤚_ : Op₃ A)   -- The core ternary operator
  where

open import Data.Product.Base using (_×_)

Congruent₃ : Set _
Congruent₃ = _⤙_⤚_ Preserves₃ _≈_ ⟶ _≈_ ⟶ _≈_ ⟶ _≈_

OuterCommutativeWith : A → Set _
OuterCommutativeWith e = ∀ x z → (x ⤙ z ⤚ e) ≈ (e ⤙ z ⤚ x)

OuterCommutative : Set _
OuterCommutative = ∀ y → OuterCommutativeWith y

LeftInnerCommutativeWith : A → Set _
LeftInnerCommutativeWith e = ∀ x y → (x ⤙ y ⤚ e) ≈ (y ⤙ x ⤚ e)

RightInnerCommutativeWith : A → Set _
RightInnerCommutativeWith e = ∀ x y → (e ⤙ x ⤚ y) ≈ (e ⤙ y ⤚ x)

InnerCommutativeWith : A → Set _
InnerCommutativeWith e = LeftInnerCommutativeWith e × RightInnerCommutativeWith e

MiddleNestedDoubleExchange : Set _
MiddleNestedDoubleExchange = ∀ v w x y z → (v ⤙ x ⤙ z ⤚ y ⤚ w) ≈ (x ⤙ v ⤙ z ⤚ w ⤚ y)

OuterAssociativeWith : A → Set _
OuterAssociativeWith e = ∀ w x y z → ((w ⤙ e ⤚ x) ⤙ z ⤚ y) ≈ (w ⤙ z ⤚ (x ⤙ e ⤚ y))

LeftPulloutWith : A → Set _
LeftPulloutWith e = ∀ v w x y z → ((w ⤙ v ⤚ x) ⤙ z ⤚ y) ≈ ((w ⤙ e ⤚ x) ⤙ v ⤙ z ⤚ y ⤚ y)

RightPulloutWith : A → Set _
RightPulloutWith e = ∀ v w x y z → (w ⤙ v ⤚ (x ⤙ z ⤚ y)) ≈ (w ⤙ w ⤙ v ⤚ z ⤚ (x ⤙ e ⤚ y))

PulloutWith : A → Set _
PulloutWith e = LeftPulloutWith e × RightPulloutWith e
