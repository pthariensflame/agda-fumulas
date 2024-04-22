------------------------------------------------------------------------
-- Additional properties of fumulas.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.

open import Algebra.Fumula.Bundles using (Fumula)

module Algebra.Fumula.Properties {c ℓ} (F : Fumula c ℓ) where

open import Function.Definitions using (Inverseˡ; Inverseʳ; Inverseᵇ)
open import Data.Product.Base using (_,_)
open Fumula F
open import Algebra.Definitions _≈_ using (Involutive)
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- The "pull apart" property: a way of separating the two ring
-- operators from within a fumula, or of melding them again.
------------------------------------------------------------------------

●-◆-pull-apartˡ : ∀ x y z → (x ⤙ ◆ ⤚ y) ⤙ z ⤚ ● ≈ x ⤙ z ⤚ y
●-◆-pull-apartˡ x y z = begin
  (x ⤙ ◆ ⤚ y) ⤙ z ⤚ ● ≈⟨  ◆-outer-associate x y ● z  ⟩
  x ⤙ z ⤚ (y ⤙ ◆ ⤚ ●) ≈⟨ ⤙⤚-cong refl refl (●-◆-collapse-sideʳ y) ⟩
  x ⤙ z ⤚ y ∎

●-◆-pull-apartʳ : ∀ x y z → ● ⤙ z ⤚ (x ⤙ ◆ ⤚ y) ≈ x ⤙ z ⤚ y
●-◆-pull-apartʳ x y z = begin
  ● ⤙ z ⤚ (x ⤙ ◆ ⤚ y) ≈⟨ sym (◆-outer-associate ● x y z) ⟩
  (● ⤙ ◆ ⤚ x) ⤙ z ⤚ y ≈⟨ ⤙⤚-cong (●-◆-collapse-sideˡ x) refl refl ⟩
  x ⤙ z ⤚ y ∎

------------------------------------------------------------------------
-- Properties of the successor and predecessor operations.
------------------------------------------------------------------------

↑-↓-inverseˡ : Inverseˡ _≈_ _≈_ _↑ _↓
↑-↓-inverseˡ {x} {y} y≈x↓ = begin
  y ↑ ≈⟨ ↑-cong y≈x↓ ⟩
  x ↓ ↑ ≡⟨⟩
  ■ ⤙ ■ ⤙ x ⤚ ● ⤚ ■ ≈⟨ ↑-cong (●-inner-commuteˡ ■ x) ⟩
  ■ ⤙ x ⤙ ■ ⤚ ● ⤚ ■ ≈⟨ double-exchange ■ ■ x ● ■ ⟩
  x ⤙ ■ ⤙ ■ ⤚ ■ ⤚ ● ≡⟨⟩
  x ⤙ ◆ ⤚ ● ≈⟨ ●-◆-collapse-sideʳ x ⟩
  x ∎

↑-↓-inverseʳ : Inverseʳ _≈_ _≈_ _↑ _↓
↑-↓-inverseʳ {x} {y} y≈x↑ = begin
  y ↓ ≈⟨ ↓-cong y≈x↑ ⟩
  x ↑ ↓ ≡⟨⟩
  ■ ⤙ ■ ⤙ x ⤚ ■ ⤚ ● ≈⟨ double-exchange ■ ● ■ ■ x ⟩
  ■ ⤙ ■ ⤙ x ⤚ ● ⤚ ■ ≈⟨ ↑-↓-inverseˡ refl ⟩
  x ∎

↑-↓-inverse : Inverseᵇ _≈_ _≈_ _↑ _↓
↑-↓-inverse = ↑-↓-inverseˡ , ↑-↓-inverseʳ

↑′≈↑ : ∀ x → x ↑′ ≈ x ↑
↑′≈↑ x = begin
  x ↑′ ≡⟨⟩
  ● ⤙ x ⤚ ● ≈⟨ ●-inner-commuteˡ ● x ⟩
  x ⤙ ● ⤚ ● ≈⟨ double-exchange x ● ■ ■ ◆ ⟩
  ■ ⤙ x ⤙ ◆ ⤚ ● ⤚ ■ ≈⟨ ↑-cong (●-◆-collapse-sideʳ x) ⟩
  ■ ⤙ x ⤚ ■ ≡⟨⟩
  x ↑ ∎

↓′≈↓ : ∀ x → x ↓′ ≈ x ↓
↓′≈↓ x = sym (●-outer-commute ■ x)

------------------------------------------------------------------------
-- Properties of the invert operation.
------------------------------------------------------------------------

invert-involutive : Involutive invert
invert-involutive x = begin
  invert (invert x) ≡⟨⟩
  ■ ⤙ ◆ ⤚ (■ ⤙ ◆ ⤚ x) ≈⟨ sym (◆-outer-associate ■ ■ x ◆) ⟩
  ● ⤙ ◆ ⤚ x ≈⟨ ●-◆-collapse-sideˡ x ⟩
  x ∎
