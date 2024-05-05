------------------------------------------------------------------------
-- Additional properties of fumula extrusions.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Properties where
open import Relation.Binary.Bundles using (Setoid)
open import Algebra.Fumula.Bundles
open import Algebra.Fumula.Extrusion.Bundles
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module LeftProperties {f fℓ x xℓ} (F : Fumula f fℓ) (X : LeftFumulaExtrusion F x xℓ) where
  private
    module F = Fumula F
  open LeftFumulaExtrusion X
  open Setoid setoid using (refl)
  open SetoidReasoning setoid

  ❲❳⤙⤚-●ᶠ-◆-pull-apartʳ : ∀ x y z → (❲ F.● ❳⤙ z ⤚ ❲ x ❳⤙ ◆ ⤚ y) ≈ ❲ x ❳⤙ z ⤚ y
  ❲❳⤙⤚-●ᶠ-◆-pull-apartʳ x y z = begin
    ❲ F.● ❳⤙ z ⤚ ❲ x ❳⤙ ◆ ⤚ y ≈⟨ ❲❳⤙⤚-◆ᶠ-◆-outer-associate F.● x y z ⟨
    ❲ F.● F.⤙ F.◆ ⤚ x ❳⤙ z ⤚ y ≈⟨ ❲❳⤙⤚-cong (F.●-◆-collapse-sideˡ x) refl refl ⟩
    ❲ x ❳⤙ z ⤚ y ∎

module RightProperties {f fℓ x xℓ} (F : Fumula f fℓ) (X : RightFumulaExtrusion F x xℓ) where
  private
    module F = Fumula F
  open RightFumulaExtrusion X
  open Setoid setoid using (refl)
  open SetoidReasoning setoid

  ⤙⤚❲❳-●ᶠ-◆-pull-apartˡ : ∀ x y z → (x ⤙ ◆ ⤚❲ y ❳ ⤙ z ⤚❲ F.● ❳) ≈ x ⤙ z ⤚❲ y ❳
  ⤙⤚❲❳-●ᶠ-◆-pull-apartˡ x y z = begin
    x ⤙ ◆ ⤚❲ y ❳ ⤙ z ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-◆ᶠ-◆-outer-associate x y F.● z ⟩
    x ⤙ z ⤚❲ y F.⤙ F.◆ ⤚ F.● ❳ ≈⟨ ⤙⤚❲❳-cong refl refl (F.●-◆-collapse-sideʳ y) ⟩
    x ⤙ z ⤚❲ y ❳ ∎
