------------------------------------------------------------------------
-- Additional properties of fumula extrusions.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Properties where
open import Relation.Binary.Bundles using (Setoid)
open import Algebra.Fumula.Bundles
import Algebra.Fumula.Properties as FumulaProperties
open import Algebra.Fumula.Extrusion.Bundles
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module LeftProperties {f fℓ x xℓ} (F : Fumula f fℓ) (X : LeftFumulaExtrusion F x xℓ) where
  private
    module F where
      open Fumula F public
      open FumulaProperties F public
  open LeftFumulaExtrusion X
  open Setoid setoid using (refl)
  open SetoidReasoning setoid

  ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ : ∀ x → (❲ F.● ❳⤙ ◆ ⤚ x) ≈ x
  ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ x = begin
    ❲ F.● ❳⤙ ◆ ⤚ x ≈⟨ ❲❳⤙⤚-●ᶠ-inner-commuteʳ ◆ x ⟩
    ❲ F.● ❳⤙ x ⤚ ◆ ≈⟨ ❲❳⤙⤚-◆-collapse-middleʳ F.● x ⟩
    x ∎

  ❲❳⤙⤚-●ᶠ-◆-pull-apartʳ : ∀ x y z → (❲ F.● ❳⤙ z ⤚ ❲ x ❳⤙ ◆ ⤚ y) ≈ ❲ x ❳⤙ z ⤚ y
  ❲❳⤙⤚-●ᶠ-◆-pull-apartʳ x y z = begin
    ❲ F.● ❳⤙ z ⤚ ❲ x ❳⤙ ◆ ⤚ y ≈⟨ ❲❳⤙⤚-◆ᶠ-◆-outer-associate F.● x y z ⟨
    ❲ F.● F.⤙ F.◆ ⤚ x ❳⤙ z ⤚ y ≈⟨ ❲❳⤙⤚-cong (F.●-◆-collapse-sideˡ x) refl refl ⟩
    ❲ x ❳⤙ z ⤚ y ∎

module RightProperties {f fℓ x xℓ} (F : Fumula f fℓ) (X : RightFumulaExtrusion F x xℓ) where
  private
    module F where
      open Fumula F public
      open FumulaProperties F public
  open RightFumulaExtrusion X
  open Setoid setoid using (refl)
  open SetoidReasoning setoid

  ⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ : ∀ x → (x ⤙ ◆ ⤚❲ F.● ❳) ≈ x
  ⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ x = begin
    x ⤙ ◆ ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-●ᶠ-inner-commuteˡ x ◆ ⟩
    ◆ ⤙ x ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-◆-collapse-middleˡ F.● x ⟩
    x ∎

  ⤙⤚❲❳-●ᶠ-◆-pull-apartˡ : ∀ x y z → (x ⤙ ◆ ⤚❲ y ❳ ⤙ z ⤚❲ F.● ❳) ≈ x ⤙ z ⤚❲ y ❳
  ⤙⤚❲❳-●ᶠ-◆-pull-apartˡ x y z = begin
    x ⤙ ◆ ⤚❲ y ❳ ⤙ z ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-◆ᶠ-◆-outer-associate x y F.● z ⟩
    x ⤙ z ⤚❲ y F.⤙ F.◆ ⤚ F.● ❳ ≈⟨ ⤙⤚❲❳-cong refl refl (F.●-◆-collapse-sideʳ y) ⟩
    x ⤙ z ⤚❲ y ❳ ∎
