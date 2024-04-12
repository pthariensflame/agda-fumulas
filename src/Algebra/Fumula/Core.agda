------------------------------------------------------------------------
-- Basic definitions about ternary operations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.

module Algebra.Fumula.Core where

open import Level using (Level)
open import Relation.Binary.Core using (Rel)

private
  variable
    a b c d ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

-- A ternary variant of _Preserves_⟶_.

_Preserves₃_⟶_⟶_⟶_ : (A → B → C → D) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Rel D ℓ₄ → Set _
_⤙_⤚_ Preserves₃ P ⟶ Q ⟶ R ⟶ S = ∀ {x y u v n m} → P x y → Q u v → R n m → S (x ⤙ u ⤚ n) (y ⤙ v ⤚ m)

-- Ternary operations.

Op₃ : Set ℓ → Set ℓ
Op₃ A = A → A → A → A
