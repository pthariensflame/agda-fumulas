------------------------------------------------------------------------
-- "Unbiased" versions of fumula operations
------------------------------------------------------------------------

open import Algebra.Fumula.Bundles using (Fumula)
module Algebra.Fumula.UnbiasedOps {f fℓ} (F : Fumula f fℓ) where
open import Data.Nat using (zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_]; -_)
open import Data.List using (List; []; _∷_; map; [_])
open Fumula F

infix 7 collapseInner_over_
collapseInner_over_ : List Carrier → Carrier → Carrier
collapseInner [] over z = z ↑
collapseInner x ∷ [] over z = x ⤙ z ⤚ ●
collapseInner x ∷ y ∷ xs over z = x ⤙ z ⤚ (collapseInner y ∷ xs over ◆)

collapseInner : List Carrier → Carrier
collapseInner xs = collapseInner xs over ◆

infix 7 collapse_over_
collapse_over_ : List (List Carrier) → Carrier → Carrier
collapse [] over z = z
collapse xs ∷ xss over z = collapseInner xs over (collapse xss over z)

collapse : List (List Carrier) → Carrier
collapse xss = collapse xss over ◆

infix 4 collapseOuter_over_
collapseOuter_over_ : List Carrier → Carrier → Carrier
collapseOuter xs over z = collapse (map [_] xs)

collapseOuter : List Carrier → Carrier
collapseOuter xs = collapseOuter xs over ◆

-- coefficients listed in ascending rank order, no gaps, starting at 0
infix 7 evalPoly_at_
evalPoly_at_ : List Carrier → Carrier → Carrier
evalPoly [] at var = ◆
evalPoly coeff ∷ coeffs at var = var ⤙ coeff ⤚ (evalPoly coeffs at var)

infix 4 advance_by_
advance_by_ : Carrier → ℤ → Carrier
advance x by + zero = x
advance x by + suc n = (advance x by + n) ↑
advance x by -[1+ zero ] = x ↓
advance x by -[1+ suc n ] = (advance x by -[1+ n ]) ↓

infix 4 retreat_by_
retreat_by_ : Carrier → ℤ → Carrier
retreat x by i = advance x by - i
