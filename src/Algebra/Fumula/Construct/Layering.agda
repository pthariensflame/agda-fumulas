------------------------------------------------------------------------
-- Layering of fumulas extrusions on their fumulas.
-- (The fumula view of Nagata's idealization.)
------------------------------------------------------------------------

open import Algebra.Fumula.Bundles
open import Algebra.Fumula.Extrusion.Bundles
module Algebra.Fumula.Construct.Layering {f ℓf x ℓx} (F : Fumula f ℓf) (X : DoubleFumulaExtrusion F F x ℓx) where
open import Level using (_⊔_)
open import Data.Product using (_,_)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Algebra.Fumula.Core using (Op₃)
open import Algebra.Fumula.Extrusion.Construct using (module DirectProduct; module TensorUnit)

private
  module F = Fumula F
  module X where
    open DoubleFumulaExtrusion X public
    open Setoid setoid public using (refl)
  module F⊗X = DoubleFumulaExtrusion (DirectProduct.doubleFumulaExtrusion F F (TensorUnit.doubleFumulaExtrusion F) X)
open F⊗X using (Carrier; _≈_)
open SetoidReasoning X.setoid

ιᶠ : F.Carrier → Carrier
ιᶠ x = x , X.◆

ιˣ : X.Carrier → Carrier
ιˣ x′ = F.◆ , x′

private
  _⤙_⤚_ : Op₃ Carrier
  (x , x′) ⤙ z , z′ ⤚ (y , y′) = x F.⤙ z ⤚ y , X.❲ x ❳⤙ (x′ X.⤙ z′ ⤚❲ y ❳) ⤚ y′

fumula : Fumula (f ⊔ x) (ℓf ⊔ ℓx)
fumula = record
  { Carrier = Carrier
  ; _≈_ = _≈_
  ; _⤙_⤚_ = _⤙_⤚_
  ; ■ = ιᶠ F.■
  ; isFumula = record
    { isAlmostFumula = record
      { isEquivalence = F⊗X.isEquivalence
      ; ⤙⤚-cong = λ (x≈y , x′≈y′) (u≈v , u′≈v′) (n≈m , n′≈m′) →
        F.⤙⤚-cong x≈y u≈v n≈m , X.❲❳⤙⤚-cong x≈y (X.⤙⤚❲❳-cong x′≈y′ u′≈v′ n≈m) n′≈m′
      ; double-exchange = λ (v , v′) (w , w′) (x , x′) (y , y′) (z , z′) → F.double-exchange v w x y z , (begin
        X.❲ v ❳⤙ v′ X.⤙ X.❲ x ❳⤙ x′ X.⤙ z′ ⤚❲ y ❳ ⤚ y′ ⤚❲ w ❳ ⤚ w′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-⤙⤚❲❳-double-exchange x y′ v′ w (x′ X.⤙ z′ ⤚❲ y ❳)) X.refl ⟨
        X.❲ v ❳⤙ X.❲ x ❳⤙ v′ X.⤙ x′ X.⤙ z′ ⤚❲ y ❳ ⤚❲ w ❳ ⤚ y′ ⤚ w′ ≈⟨ X.❲❳⤙⤚-double-exchange v w′ x y′ (v′ X.⤙ x′ X.⤙ z′ ⤚❲ y ❳ ⤚❲ w ❳) ⟩
        X.❲ x ❳⤙ X.❲ v ❳⤙ v′ X.⤙ x′ X.⤙ z′ ⤚❲ y ❳ ⤚❲ w ❳ ⤚ w′ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-double-exchange v′ w x′ y z′) X.refl) X.refl ⟩
        X.❲ x ❳⤙ X.❲ v ❳⤙ x′ X.⤙ v′ X.⤙ z′ ⤚❲ w ❳ ⤚❲ y ❳ ⤚ w′ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-⤙⤚❲❳-double-exchange v w′ x′ y (v′ X.⤙ z′ ⤚❲ w ❳)) X.refl ⟩
        X.❲ x ❳⤙ x′ X.⤙ X.❲ v ❳⤙ v′ X.⤙ z′ ⤚❲ w ❳ ⤚ w′ ⤚❲ y ❳ ⤚ y′ ∎)
      }
    ; ■-outer-commute = λ (x , x′) (z , z′) → F.■-outer-commute x z , (begin
      X.❲ x ❳⤙ x′ X.⤙ z′ ⤚❲ F.■ ❳ ⤚ X.◆ ≈⟨ X.❲❳⤙⤚-⤙⤚❲❳-double-exchange x X.◆ x′ F.■ z′ ⟩
      x′ X.⤙ X.❲ x ❳⤙ z′ ⤚ X.◆ ⤚❲ F.■ ❳ ≈⟨ X.■ᶠ-outer-commute x′ (X.❲ x ❳⤙ z′ ⤚ X.◆) ⟩
      X.❲ F.■ ❳⤙ X.❲ x ❳⤙ z′ ⤚ X.◆ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-◆-collapse-middleʳ x z′) X.refl ⟩
      X.❲ F.■ ❳⤙ z′ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆-collapse-middleˡ x z′) X.refl ⟨
      X.❲ F.■ ❳⤙ X.◆ X.⤙ z′ ⤚❲ x ❳ ⤚ x′ ∎)
    ; ■-collapse-dup =
      (λ (x , x′) → F.■-collapse-dupˡ x , (begin
        X.❲ F.■ ❳⤙ X.◆ X.⤙ x′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆-collapse-middleˡ x x′) X.refl ⟩
        X.❲ F.■ ❳⤙ x′ ⤚ x′ ≈⟨ X.❲❳⤙⤚-■ᶠ-collapse-dupʳ x′ ⟩
        X.◆ ≈⟨ X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆ ⟨
        X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ≈⟨ X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) ⟨
        X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ∎)) ,
      (λ (x , x′) → F.■-collapse-dupʳ x , (begin
        X.❲ x ❳⤙ x′ X.⤙ x′ ⤚❲ F.■ ❳ ⤚ X.◆ ≈⟨ X.❲❳⤙⤚-◆-collapse-middleʳ x (x′ X.⤙ x′ ⤚❲ F.■ ❳) ⟩
        x′ X.⤙ x′ ⤚❲ F.■ ❳ ≈⟨ X.⤙⤚❲❳-■ᶠ-collapse-dupˡ x′ ⟩
        X.◆ ≈⟨ X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆ ⟨
        X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ≈⟨ X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) ⟨
        X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ∎))
    ; ◆-outer-commute = λ (x , x′) (z , z′) → F.◆-outer-commute x z , (begin
      X.❲ x ❳⤙ x′ X.⤙ z′ ⤚❲ F.◆ ❳ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) ⟩
      X.❲ x ❳⤙ x′ X.⤙ z′ ⤚❲ F.◆ ❳ ⤚ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) ⟩
      X.❲ x ❳⤙ x′ X.⤙ z′ ⤚❲ F.◆ ❳ ⤚ X.◆ ≈⟨ X.❲❳⤙⤚-◆-collapse-middleʳ x (x′ X.⤙ z′ ⤚❲ F.◆ ❳) ⟩
      x′ X.⤙ z′ ⤚❲ F.◆ ❳ ≈⟨ X.⤙⤚❲❳-◆ᶠ-collapse-middleʳ x′ z′ ⟩
      z′ ≈⟨ X.❲❳⤙⤚-◆ᶠ-collapse-middleˡ x′ z′ ⟨
      X.❲ F.◆ ❳⤙ z′ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆-collapse-middleˡ x z′) X.refl ⟨
      X.❲ F.◆ ❳⤙ X.◆ X.⤙ z′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) X.refl F.refl) X.refl ⟨
      X.❲ F.◆ ❳⤙ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) X.⤙ z′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) X.refl F.refl) X.refl ⟨
      X.❲ F.◆ ❳⤙ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) X.⤙ z′ ⤚❲ x ❳ ⤚ x′ ∎)
    ; ◆-collapse-middle =
      (λ (x , x′) (z , z′) → F.◆-collapse-middleˡ x z , (begin
        X.❲ F.◆ ❳⤙ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) X.⤙ z′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-◆ᶠ-collapse-middleˡ x′ ((X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) X.⤙ z′ ⤚❲ x ❳) ⟩
        (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) X.⤙ z′ ⤚❲ x ❳ ≈⟨ X.⤙⤚❲❳-cong (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) X.refl F.refl ⟩
        (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) X.⤙ z′ ⤚❲ x ❳ ≈⟨ X.⤙⤚❲❳-cong (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) X.refl F.refl ⟩
        X.◆ X.⤙ z′ ⤚❲ x ❳ ≈⟨ X.⤙⤚❲❳-◆-collapse-middleˡ x z′ ⟩
        z′ ∎)) ,
      (λ (x , x′) (z , z′) → F.◆-collapse-middleʳ x z , (begin
        X.❲ x ❳⤙ x′ X.⤙ z′ ⤚❲ F.◆ ❳ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆ᶠ-collapse-middleʳ x′ z′) (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) ⟩
        X.❲ x ❳⤙ z′ ⤚ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) ⟩
        X.❲ x ❳⤙ z′ ⤚ X.◆ ≈⟨ X.❲❳⤙⤚-◆-collapse-middleʳ x z′ ⟩
        z′ ∎))
    ; ●-outer-commute = λ (x , x′) (z , z′) → F.●-outer-commute x z , (begin
      X.❲ x ❳⤙ x′ X.⤙ z′ ⤚❲ F.● ❳ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) ≈⟨ X.❲❳⤙⤚-⤙⤚❲❳-double-exchange x (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) x′ F.● z′ ⟩
      x′ X.⤙ X.❲ x ❳⤙ z′ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) ⤚❲ F.● ❳ ≈⟨ X.●ᶠ-outer-commute x′ (X.❲ x ❳⤙ z′ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆)) ⟩
      X.❲ F.● ❳⤙ X.❲ x ❳⤙ z′ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-cong F.refl X.refl (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳))) X.refl ⟩
      X.❲ F.● ❳⤙ X.❲ x ❳⤙ z′ ⤚ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳) ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-cong F.refl X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆))) X.refl ⟩
      X.❲ F.● ❳⤙ X.❲ x ❳⤙ z′ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-cong F.refl X.refl (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳))) X.refl ⟩
      X.❲ F.● ❳⤙ X.❲ x ❳⤙ z′ ⤚ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-cong F.refl X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆)) X.refl ⟩
      X.❲ F.● ❳⤙ X.❲ x ❳⤙ z′ ⤚ X.◆ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-◆-collapse-middleʳ x z′) X.refl ⟩
      X.❲ F.● ❳⤙ z′ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆-collapse-middleˡ x z′) X.refl ⟨
      X.❲ F.● ❳⤙ X.◆ X.⤙ z′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) X.refl F.refl) X.refl ⟨
      X.❲ F.● ❳⤙ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) X.⤙ z′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) X.refl F.refl) X.refl ⟨
      X.❲ F.● ❳⤙ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) X.⤙ z′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆)) X.refl F.refl) X.refl ⟨
      X.❲ F.● ❳⤙ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳) X.⤙ z′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳)) X.refl F.refl) X.refl ⟨
      X.❲ F.● ❳⤙ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) X.⤙ z′ ⤚❲ x ❳ ⤚ x′ ∎)
    ; ●-inner-commute =
      (λ (x , x′) (y , y′) → F.●-inner-commuteˡ x y , (begin
        X.❲ x ❳⤙ x′ X.⤙ y′ ⤚❲ F.● ❳ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-●ᶠ-inner-commuteˡ x′ y′) (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳)) ⟩
        X.❲ x ❳⤙ y′ X.⤙ x′ ⤚❲ F.● ❳ ⤚ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆)) ⟩
        X.❲ x ❳⤙ y′ X.⤙ x′ ⤚❲ F.● ❳ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) ⟩
        X.❲ x ❳⤙ y′ X.⤙ x′ ⤚❲ F.● ❳ ⤚ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) ⟩
        X.❲ x ❳⤙ y′ X.⤙ x′ ⤚❲ F.● ❳ ⤚ X.◆ ≈⟨ X.❲❳⤙⤚-◆-collapse-middleʳ x (y′ X.⤙ x′ ⤚❲ F.● ❳) ⟩
        y′ X.⤙ x′ ⤚❲ F.● ❳ ≈⟨ X.❲❳⤙⤚-◆-collapse-middleʳ y (y′ X.⤙ x′ ⤚❲ F.● ❳) ⟨
        X.❲ y ❳⤙ y′ X.⤙ x′ ⤚❲ F.● ❳ ⤚ X.◆ ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) ⟨
        X.❲ y ❳⤙ y′ X.⤙ x′ ⤚❲ F.● ❳ ⤚ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) ⟨
        X.❲ y ❳⤙ y′ X.⤙ x′ ⤚❲ F.● ❳ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆)) ⟨
        X.❲ y ❳⤙ y′ X.⤙ x′ ⤚❲ F.● ❳ ⤚ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳)) ⟨
        X.❲ y ❳⤙ y′ X.⤙ x′ ⤚❲ F.● ❳ ⤚ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) ∎)) ,
      (λ (x , x′) (y , y′) → F.●-inner-commuteʳ x y , (begin
        X.❲ F.● ❳⤙ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) X.⤙ x′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳)) X.refl F.refl) X.refl ⟩
        X.❲ F.● ❳⤙ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳) X.⤙ x′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆)) X.refl F.refl) X.refl ⟩
        X.❲ F.● ❳⤙ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) X.⤙ x′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) X.refl F.refl) X.refl ⟩
        X.❲ F.● ❳⤙ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) X.⤙ x′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) X.refl F.refl) X.refl ⟩
        X.❲ F.● ❳⤙ X.◆ X.⤙ x′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆-collapse-middleˡ y x′) X.refl ⟩
        X.❲ F.● ❳⤙ x′ ⤚ y′ ≈⟨ X.❲❳⤙⤚-●ᶠ-inner-commuteʳ x′ y′ ⟩
        X.❲ F.● ❳⤙ y′ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆-collapse-middleˡ x y′) X.refl ⟨
        X.❲ F.● ❳⤙ X.◆ X.⤙ y′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) X.refl F.refl) X.refl ⟨
        X.❲ F.● ❳⤙ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳) X.⤙ y′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) X.refl F.refl) X.refl ⟨
        X.❲ F.● ❳⤙ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) X.⤙ y′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆)) X.refl F.refl) X.refl ⟨
        X.❲ F.● ❳⤙ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳) X.⤙ y′ ⤚❲ x ❳ ⤚ x′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳)) X.refl F.refl) X.refl ⟨
        X.❲ F.● ❳⤙ (X.❲ F.■ ❳⤙ X.◆ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆) X.⤙ y′ ⤚❲ x ❳ ⤚ x′ ∎))
    ; ◆-outer-associate = λ (w , w′) (x , x′) (y , y′) (z , z′) → F.◆-outer-associate w x y z , (begin
      X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (X.❲ w ❳⤙ w′ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ x ❳ ⤚ x′) X.⤙ z′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong X.refl (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) F.refl) X.refl) X.refl F.refl) X.refl ⟩
      X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (X.❲ w ❳⤙ w′ X.⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚❲ x ❳ ⤚ x′) X.⤙ z′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) F.refl) X.refl) X.refl F.refl) X.refl ⟩
      X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (X.❲ w ❳⤙ w′ X.⤙ X.◆ ⤚❲ x ❳ ⤚ x′) X.⤙ z′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-⤙⤚❲❳-double-exchange (w F.⤙ F.◆ ⤚ x) y′ (X.❲ w ❳⤙ w′ X.⤙ X.◆ ⤚❲ x ❳ ⤚ x′) y z′ ⟩
      (X.❲ w ❳⤙ w′ X.⤙ X.◆ ⤚❲ x ❳ ⤚ x′) X.⤙ X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ z′ ⤚ y′ ⤚❲ y ❳ ≈⟨ X.⤙⤚❲❳-cong (X.❲❳⤙⤚-⤙⤚❲❳-double-exchange w x′ w′ x X.◆) (X.❲❳⤙⤚-◆ᶠ-◆-outer-associate w x y′ z′) F.refl ⟩
      (w′ X.⤙ X.❲ w ❳⤙ X.◆ ⤚ x′ ⤚❲ x ❳) X.⤙ X.❲ w ❳⤙ z′ ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′) ⤚❲ y ❳ ≈⟨ X.⤙⤚❲❳-◆-pulloutˡ (X.❲ w ❳⤙ X.◆ ⤚ x′) w′ x y (X.❲ w ❳⤙ z′ ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′)) ⟩
      (w′ X.⤙ X.◆ ⤚❲ x ❳) X.⤙ (X.❲ w ❳⤙ X.◆ ⤚ x′) X.⤙ X.❲ w ❳⤙ z′ ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′) ⤚❲ y ❳ ⤚❲ y ❳ ≈⟨ X.⤙⤚❲❳-double-exchange (w′ X.⤙ X.◆ ⤚❲ x ❳) y (X.❲ w ❳⤙ X.◆ ⤚ x′) y (X.❲ w ❳⤙ z′ ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′)) ⟩
      (X.❲ w ❳⤙ X.◆ ⤚ x′) X.⤙ (w′ X.⤙ X.◆ ⤚❲ x ❳) X.⤙ X.❲ w ❳⤙ z′ ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′) ⤚❲ y ❳ ⤚❲ y ❳ ≈⟨ X.⤙⤚❲❳-cong X.refl (X.❲❳⤙⤚-⤙⤚❲❳-double-exchange w (X.❲ x ❳⤙ X.◆ ⤚ y′) (w′ X.⤙ X.◆ ⤚❲ x ❳) y z′) F.refl ⟨
      (X.❲ w ❳⤙ X.◆ ⤚ x′) X.⤙ X.❲ w ❳⤙ (w′ X.⤙ X.◆ ⤚❲ x ❳) X.⤙ z′ ⤚❲ y ❳ ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′) ⤚❲ y ❳ ≈⟨ X.◆-outer-associate w x′ y (X.❲ w ❳⤙ (w′ X.⤙ X.◆ ⤚❲ x ❳) X.⤙ z′ ⤚❲ y ❳ ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′)) ⟩
      X.❲ w ❳⤙ X.❲ w ❳⤙ (w′ X.⤙ X.◆ ⤚❲ x ❳) X.⤙ z′ ⤚❲ y ❳ ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′) ⤚ (x′ X.⤙ X.◆ ⤚❲ y ❳) ≈⟨ X.❲❳⤙⤚-double-exchange w (X.❲ x ❳⤙ X.◆ ⤚ y′) w (x′ X.⤙ X.◆ ⤚❲ y ❳) ((w′ X.⤙ X.◆ ⤚❲ x ❳) X.⤙ z′ ⤚❲ y ❳) ⟨
      X.❲ w ❳⤙ X.❲ w ❳⤙ (w′ X.⤙ X.◆ ⤚❲ x ❳) X.⤙ z′ ⤚❲ y ❳ ⤚ (x′ X.⤙ X.◆ ⤚❲ y ❳) ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′) ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆ᶠ-◆-outer-associate w′ x y z′) X.refl)  X.refl ⟩
      X.❲ w ❳⤙ X.❲ w ❳⤙ w′ X.⤙ z′ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ (x′ X.⤙ X.◆ ⤚❲ y ❳) ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′) ≈⟨ X.❲❳⤙⤚-◆-pulloutʳ (w′ X.⤙ z′ ⤚❲ x F.⤙ F.◆ ⤚ y ❳) w x y′ (x′ X.⤙ X.◆ ⤚❲ y ❳) ⟨
      X.❲ w ❳⤙ w′ X.⤙ z′ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ (X.❲ x ❳⤙ x′ X.⤙ X.◆ ⤚❲ y ❳ ⤚ y′) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) F.refl) X.refl) ⟨
      X.❲ w ❳⤙ w′ X.⤙ z′ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ (X.❲ x ❳⤙ x′ X.⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚❲ y ❳ ⤚ y′) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong X.refl (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) F.refl) X.refl) ⟨
      X.❲ w ❳⤙ w′ X.⤙ z′ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ (X.❲ x ❳⤙ x′ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ y ❳ ⤚ y′) ∎)
    ; ◆-pullout =
      (λ (v , v′) (w , w′) (x , x′) (y , y′) (z , z′) → F.◆-pulloutˡ v w x y z , (begin
        X.❲ w F.⤙ v ⤚ x ❳⤙ (X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ x ❳ ⤚ x′) X.⤙ z′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-◆ᶠ-pulloutˡ v w x y′ ((X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ x ❳ ⤚ x′) X.⤙ z′ ⤚❲ y ❳) ⟩
        X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ X.❲ v ❳⤙ (X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ x ❳ ⤚ x′) X.⤙ z′ ⤚❲ y ❳ ⤚ y′ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-⤙⤚❲❳-double-exchange v y′ (X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ x ❳ ⤚ x′) y z′) X.refl ⟩
        X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ x ❳ ⤚ x′) X.⤙ X.❲ v ❳⤙ z′ ⤚ y′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-⤙⤚❲❳-double-exchange w x′ w′ x v′) X.refl F.refl) X.refl ⟩
        X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (w′ X.⤙ X.❲ w ❳⤙ v′ ⤚ x′ ⤚❲ x ❳) X.⤙ X.❲ v ❳⤙ z′ ⤚ y′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆-pulloutˡ (X.❲ w ❳⤙ v′ ⤚ x′) w′ x y (X.❲ v ❳⤙ z′ ⤚ y′)) X.refl ⟩
        X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (w′ X.⤙ X.◆ ⤚❲ x ❳) X.⤙ (X.❲ w ❳⤙ v′ ⤚ x′) X.⤙ X.❲ v ❳⤙ z′ ⤚ y′ ⤚❲ y ❳ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong X.refl (X.⤙⤚❲❳-❲❳⤙⤚-◆-pulloutˡ v′ w x′ y (X.❲ v ❳⤙ z′ ⤚ y′)) F.refl) X.refl ⟩
        X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (w′ X.⤙ X.◆ ⤚❲ x ❳) X.⤙ (X.❲ w ❳⤙ X.◆ ⤚ x′) X.⤙ v′ X.⤙ X.❲ v ❳⤙ z′ ⤚ y′ ⤚❲ y ❳ ⤚❲ y ❳ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆-pulloutˡ (X.❲ w ❳⤙ X.◆ ⤚ x′) w′ x y (v′ X.⤙ X.❲ v ❳⤙ z′ ⤚ y′ ⤚❲ y ❳)) X.refl ⟨
        X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (w′ X.⤙ X.❲ w ❳⤙ X.◆ ⤚ x′ ⤚❲ x ❳) X.⤙ v′ X.⤙ X.❲ v ❳⤙ z′ ⤚ y′ ⤚❲ y ❳ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-⤙⤚❲❳-double-exchange w x′ w′ x X.◆) (X.❲❳⤙⤚-⤙⤚❲❳-double-exchange v y′ v′ y z′) F.refl) X.refl ⟨
        X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (X.❲ w ❳⤙ w′ X.⤙ X.◆ ⤚❲ x ❳ ⤚ x′) X.⤙ X.❲ v ❳⤙ v′ X.⤙ z′ ⤚❲ y ❳ ⤚ y′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) F.refl) X.refl) X.refl F.refl) X.refl ⟨
        X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (X.❲ w ❳⤙ w′ X.⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚❲ x ❳ ⤚ x′) X.⤙ X.❲ v ❳⤙ v′ X.⤙ z′ ⤚❲ y ❳ ⤚ y′ ⤚❲ y ❳ ⤚ y′ ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong (X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong X.refl (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) F.refl) X.refl) X.refl F.refl) X.refl ⟨
        X.❲ w F.⤙ F.◆ ⤚ x ❳⤙ (X.❲ w ❳⤙ w′ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ x ❳ ⤚ x′) X.⤙ X.❲ v ❳⤙ v′ X.⤙ z′ ⤚❲ y ❳ ⤚ y′ ⤚❲ y ❳ ⤚ y′ ∎)) ,
      (λ (v , v′) (w , w′) (x , x′) (y , y′) (z , z′) → F.◆-pulloutʳ v w x y z , (begin
        X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ x F.⤙ z ⤚ y ❳ ⤚ (X.❲ x ❳⤙ x′ X.⤙ z′ ⤚❲ y ❳ ⤚ y′) ≈⟨ X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-◆ᶠ-pulloutʳ v′ w′ x y z) X.refl ⟩
        X.❲ w ❳⤙ w′ X.⤙ w′ X.⤙ v′ ⤚❲ z ❳ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ (X.❲ x ❳⤙ x′ X.⤙ z′ ⤚❲ y ❳ ⤚ y′) ≈⟨ X.❲❳⤙⤚-◆-pulloutʳ (w′ X.⤙ w′ X.⤙ v′ ⤚❲ z ❳ ⤚❲ x F.⤙ F.◆ ⤚ y ❳) w x y′ (x′ X.⤙ z′ ⤚❲ y ❳) ⟩
        X.❲ w ❳⤙ X.❲ w ❳⤙ w′ X.⤙ w′ X.⤙ v′ ⤚❲ z ❳ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ (x′ X.⤙ z′ ⤚❲ y ❳) ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′) ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-⤙⤚❲❳-◆-pulloutʳ (w′ X.⤙ w′ X.⤙ v′ ⤚❲ z ❳ ⤚❲ x F.⤙ F.◆ ⤚ y ❳) w x′ y z′) X.refl ⟩
        X.❲ w ❳⤙ X.❲ w ❳⤙ X.❲ w ❳⤙ w′ X.⤙ w′ X.⤙ v′ ⤚❲ z ❳ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ z′ ⤚ (x′ X.⤙ X.◆ ⤚❲ y ❳) ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′) ≈⟨ X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-cong F.refl (X.❲❳⤙⤚-⤙⤚❲❳-double-exchange w z′ w′ (x F.⤙ F.◆ ⤚ y) (w′ X.⤙ v′ ⤚❲ z ❳)) X.refl) X.refl ⟩
        X.❲ w ❳⤙ X.❲ w ❳⤙ w′ X.⤙ X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ z ❳ ⤚ z′ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ (x′ X.⤙ X.◆ ⤚❲ y ❳) ⤚ (X.❲ x ❳⤙ X.◆ ⤚ y′) ≈⟨ X.❲❳⤙⤚-◆-pulloutʳ (w′ X.⤙ X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ z ❳ ⤚ z′ ⤚❲ x F.⤙ F.◆ ⤚ y ❳) w x y′ (x′ X.⤙ X.◆ ⤚❲ y ❳) ⟨
        X.❲ w ❳⤙ w′ X.⤙ X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ z ❳ ⤚ z′ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ (X.❲ x ❳⤙ x′ X.⤙ X.◆ ⤚❲ y ❳ ⤚ y′) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong X.refl (X.⤙⤚❲❳-◆-collapse-middleˡ F.■ X.◆) F.refl) X.refl) ⟨
        X.❲ w ❳⤙ w′ X.⤙ X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ z ❳ ⤚ z′ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ (X.❲ x ❳⤙ x′ X.⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚❲ y ❳ ⤚ y′) ≈⟨ X.❲❳⤙⤚-cong F.refl X.refl (X.❲❳⤙⤚-cong F.refl (X.⤙⤚❲❳-cong X.refl (X.❲❳⤙⤚-◆-collapse-middleʳ F.■ (X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳)) F.refl) X.refl) ⟨
        X.❲ w ❳⤙ w′ X.⤙ X.❲ w ❳⤙ w′ X.⤙ v′ ⤚❲ z ❳ ⤚ z′ ⤚❲ x F.⤙ F.◆ ⤚ y ❳ ⤚ (X.❲ x ❳⤙ x′ X.⤙ X.❲ F.■ ❳⤙ X.◆ X.⤙ X.◆ ⤚❲ F.■ ❳ ⤚ X.◆ ⤚❲ y ❳ ⤚ y′) ∎))
    }
  }
open Fumula fumula public
  using (isFumula; almostFumula; isAlmostFumula; rawFumula; rawAlmostFumula)

infixl 4 _⋉_
_⋉_ : Fumula (f ⊔ x) (ℓf ⊔ ℓx)
_⋉_ = fumula
