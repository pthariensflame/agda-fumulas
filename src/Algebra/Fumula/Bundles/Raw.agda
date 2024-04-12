------------------------------------------------------------------------
-- Definitions of "raw" bundles for fumulas.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.

module Algebra.Fumula.Bundles.Raw where

open import Level using (suc; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Nullary.Negation.Core using (¬_)
open import Algebra.Core using (Op₁)
open import Algebra.Fumula.Core using (Op₃)

------------------------------------------------------------------------
-- Raw bundles with 1 ternary operation
------------------------------------------------------------------------

record RawAlmostFumula c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _⤙_⤚_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _⤙_⤚_   : Op₃ Carrier

  infix 4 _≉_
  _≉_ : Rel Carrier _
  x ≉ y = ¬ (x ≈ y)

------------------------------------------------------------------------
-- Raw bundles with 1 ternary operation and 1 element
------------------------------------------------------------------------

record RawFumula c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _⤙_⤚_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _⤙_⤚_   : Op₃ Carrier
    ■       : Carrier

  infix 8 _↑
  _↑ : Op₁ Carrier
  x ↑ = ■ ⤙ x ⤚ ■

  ◆ : Carrier
  ◆ = ■ ↑

  ● : Carrier
  ● = ◆ ↑

  infix 8 _↓
  _↓ : Op₁ Carrier
  x ↓ = ■ ⤙ x ⤚ ●

  infix 8 _↓′
  _↓′ : Op₁ Carrier
  x ↓′ = ● ⤙ x ⤚ ●

  infix 8 _↑′
  _↑′ : Op₁ Carrier
  x ↑′ = ● ⤙ x ⤚ ■

  invert : Op₁ Carrier
  invert x = ■ ⤙ ◆ ⤚ x

  invert′ : Op₁ Carrier
  invert′ x = ■ ⤙ ◆ ⤚ x

  rawAlmostFumula : RawAlmostFumula c ℓ
  rawAlmostFumula = record
    { _≈_ = _≈_
    ; _⤙_⤚_ = _⤙_⤚_
    }

  open RawAlmostFumula rawAlmostFumula public
    using (_≉_)
