------------------------------------------------------------------------
-- Additional properties of raw fumulas.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.

open import Algebra.Fumula.Bundles.Raw using (RawFumula)
module Algebra.Fumula.Properties.Raw {c ℓ} (F : RawFumula c ℓ) where
open import Data.Nat.Base using (zero; suc)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open RawFumula F

------------------------------------------------------------------------
-- The heartline of a fumula: the shadow of the integers
------------------------------------------------------------------------

heartline : ℤ → Carrier
heartline (+ zero) = ◆ -- ≈ ■ ↑
heartline (+ suc n) = heartline (+ n) ↑
heartline -[1+ zero ] = ■
heartline -[1+ suc n ] = heartline -[1+ n ] ↓
