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

_OuterCommutativeWith_ : A → Set _
_OuterCommutativeWith_ e = ∀ x z → (x ⤙ z ⤚ e) ≈ (e ⤙ z ⤚ x)

OuterCommutative : Set _
OuterCommutative = ∀ y → _OuterCommutativeWith_ y

_LeftInnerCommutativeWith_ : A → Set _
_LeftInnerCommutativeWith_ e = ∀ x y → (x ⤙ y ⤚ e) ≈ (y ⤙ x ⤚ e)

_RightInnerCommutativeWith_ : A → Set _
_RightInnerCommutativeWith_ e = ∀ x y → (e ⤙ x ⤚ y) ≈ (e ⤙ y ⤚ x)

_InnerCommutativeWith_ : A → Set _
_InnerCommutativeWith_ e = _LeftInnerCommutativeWith_ e × _RightInnerCommutativeWith_ e

MiddleNestedDoubleExchange : Set _
MiddleNestedDoubleExchange = ∀ v w x y z → (v ⤙ x ⤙ z ⤚ y ⤚ w) ≈ (x ⤙ v ⤙ z ⤚ w ⤚ y)

_OuterAssociativeWith_ : A → Set _
_OuterAssociativeWith_ e = ∀ w x y z → ((w ⤙ e ⤚ x) ⤙ z ⤚ y) ≈ (w ⤙ z ⤚ (x ⤙ e ⤚ y))

_LeftPulloutWith_ : A → Set _
_LeftPulloutWith_ e = ∀ v w x y z → ((w ⤙ v ⤚ x) ⤙ z ⤚ y) ≈ ((w ⤙ e ⤚ x) ⤙ v ⤙ z ⤚ y ⤚ y)

_RightPulloutWith_ : A → Set _
_RightPulloutWith_ e = ∀ v w x y z → (w ⤙ v ⤚ (x ⤙ z ⤚ y)) ≈ (w ⤙ w ⤙ v ⤚ z ⤚ (x ⤙ e ⤚ y))

_PulloutWith_ : A → Set _
_PulloutWith_ e = _LeftPulloutWith_ e × _RightPulloutWith_ e
