------------------------------------------------------------------------
-- Basic definitions about nonuniform ternary operations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extension`.

module Algebra.Fumula.Extrusion.Core where

open import Level using (_⊔_)

Op₃ₗ : ∀{a b} → Set a → Set b → Set (a ⊔ b)
Op₃ₗ A B = A → B → B → B → B

Op₃ₘ : ∀{a b} → Set a → Set b → Set (a ⊔ b)
Op₃ₘ A B = B → A → B → B

Op₃ᵣ : ∀{a b} → Set a → Set b → Set (a ⊔ b)
Op₃ᵣ A B = B → B → A → B
