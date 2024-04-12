------------------------------------------------------------------------
-- Definitions of fumulas (bundled).
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.

module Algebra.Fumula.Bundles where

open import Level using (suc; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Algebra.Fumula.Core
open import Algebra.Fumula.Structures
open import Algebra.Fumula.Bundles.Raw

record AlmostFumula c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _⤙_⤚_
  infix  4 _≈_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ
    _⤙_⤚_          : Op₃ Carrier
    isAlmostFumula : IsAlmostFumula _≈_ _⤙_⤚_

  open IsAlmostFumula isAlmostFumula public

  open RawAlmostFumula rawAlmostFumula public
    using (_≉_)

record Fumula c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _⤙_⤚_
  infix  4 _≈_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ
    _⤙_⤚_          : Op₃ Carrier
    ■              : Carrier
    isFumula : IsFumula _≈_ _⤙_⤚_ ■

  open IsFumula isFumula public

  open RawFumula rawFumula public
    using ( _≉_
          ; ◆
          ; ●
          ; _↑
          ; _↓
          ; invert
          ; _↑′
          ; _↓′
          ; invert′
          )
