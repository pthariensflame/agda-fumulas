------------------------------------------------------------------------
-- Additional properties of fumulas.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.

open import Algebra.Bundles.Fumula using (Fumula)

module Algebra.Properties.Fumula {c ℓ} (F : Fumula c ℓ) where

open Fumula F
open import Relation.Binary.Reasoning.Setoid setoid

●-◆-pull-apartˡ : ∀ x y z → (x ⤙ ◆ ⤚ y) ⤙ z ⤚ ● ≈ x ⤙ z ⤚ y
●-◆-pull-apartˡ x y z = begin
  (x ⤙ ◆ ⤚ y) ⤙ z ⤚ ● ≈⟨  ◆-outer-associate x y ● z  ⟩
  x ⤙ z ⤚ (y ⤙ ◆ ⤚ ●) ≈⟨ cong refl refl (●-◆-collapse-sideʳ y) ⟩
  x ⤙ z ⤚ y ∎

●-◆-pull-apartʳ : ∀ x y z → ● ⤙ z ⤚ (x ⤙ ◆ ⤚ y) ≈ x ⤙ z ⤚ y
●-◆-pull-apartʳ x y z = begin
  ● ⤙ z ⤚ (x ⤙ ◆ ⤚ y) ≈⟨ sym (◆-outer-associate ● x y z) ⟩
  ● ⤙ ◆ ⤚ x ⤙ z ⤚ y ≈⟨ cong (●-◆-collapse-sideˡ x) refl refl ⟩
  x ⤙ z ⤚ y ∎

  
