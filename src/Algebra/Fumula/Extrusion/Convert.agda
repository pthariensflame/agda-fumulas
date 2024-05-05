------------------------------------------------------------------------
-- Conversion of fumula extrusions to and from modules over rings.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Convert where

open import Data.Product using (_,_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Algebra.Core
open import Algebra.Bundles
import Algebra.Properties.Ring as RingProperties
open import Algebra.Module.Core
open import Algebra.Module.Structures
open import Algebra.Module.Bundles
import Algebra.Module.Properties as ModuleProperties
open import Algebra.Module.Morphism.Structures
import Algebra.Module.Morphism.ModuleHomomorphism as ModuleHomomorphismProperties
open import Algebra.Fumula.Core using (Op₃)
open import Algebra.Fumula.Bundles
import Algebra.Fumula.Properties as FumulaProperties
open import Algebra.Fumula.Convert
open import Algebra.Fumula.Extrusion.Core
open import Algebra.Fumula.Extrusion.Structures
open import Algebra.Fumula.Extrusion.Bundles
open import Algebra.Fumula.Extrusion.Properties

module FromModule where

  module _ {r m rℓ mℓ} (R : Ring r rℓ) {Carrier : Set m} (_≈_ : Rel Carrier mℓ)
           (_+_ : Op₂ Carrier) (0# : Carrier) (-_ : Op₁ Carrier) (_*ₗ_ : Opₗ (Ring.Carrier R) Carrier) where
    private
      F : Fumula r rℓ
      F = FromRing.fumula R
      module R where
        open Ring R public
        open RingProperties R public
        open RingHelpers R public
      module F where
        open Fumula F public
        open FumulaProperties F public

      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      ❲ s ❳⤙ z ⤚ x = (s *ₗ x) + z

      ◆ : Carrier
      ◆ = 0#

    isLeftFumulaExtrusion : (M : IsLeftModule R _≈_ _+_ 0# -_ _*ₗ_) → IsLeftFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ ◆
    isLeftFumulaExtrusion M = record
      { ❲❳⤙⤚-isLeftAlmostFumulaExtrusion = record
        { isEquivalence = ≈ᴹ-isEquivalence
        ; ❲❳⤙⤚-cong = λ s≈ z≈ x≈ → +ᴹ-cong (*ₗ-cong s≈ x≈) z≈
        ; ❲❳⤙⤚-double-exchange = λ v w x y z → begin
          (v *ₗ w) + ((x *ₗ y) + z) ≈⟨ +ᴹ-assoc (v *ₗ w) (x *ₗ y) z ⟨
          ((v *ₗ w) + (x *ₗ y)) + z ≈⟨ +ᴹ-congʳ (+ᴹ-comm (v *ₗ w) (x *ₗ y)) ⟩
          ((x *ₗ y) + (v *ₗ w)) + z ≈⟨ +ᴹ-assoc (x *ₗ y) (v *ₗ w) z ⟩
          (x *ₗ y) + ((v *ₗ w) + z) ∎
        }
      ; ❲❳⤙⤚-●ᶠ-inner-commuteᵣ = λ x y → begin
        ((R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) *ₗ y) + x ≈⟨ +ᴹ-congʳ (*ₗ-congʳ R.1≈-1*-1+[-1*-1+-1]) ⟨
        (R.1# *ₗ y) + x ≈⟨ +ᴹ-congʳ (*ₗ-identityˡ y) ⟩
        y + x ≈⟨ +ᴹ-congˡ (*ₗ-identityˡ x) ⟨
        y + (R.1# *ₗ x) ≈⟨ +ᴹ-comm y (R.1# *ₗ x) ⟩
        (R.1# *ₗ x) + y ≈⟨ +ᴹ-congʳ (*ₗ-congʳ R.1≈-1*-1+[-1*-1+-1]) ⟩
        ((R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) *ₗ x) + y ∎
      ; ❲❳⤙⤚-◆ᶠ-pulloutₗ = λ v w x y z → begin
        ((w R.* x R.+ v) *ₗ y) + z ≈⟨ +ᴹ-congʳ (*ₗ-distribʳ y (w R.* x) v) ⟩
        (((w R.* x) *ₗ y) + (v *ₗ y)) + z ≈⟨ +ᴹ-assoc ((w R.* x) *ₗ y) (v *ₗ y) z ⟩
        ((w R.* x) *ₗ y) + ((v *ₗ y) + z) ≈⟨ +ᴹ-congʳ (*ₗ-congʳ (R.+-identityʳ (w R.* x))) ⟨
        ((w R.* x R.+ R.0#) *ₗ y) + ((v *ₗ y) + z) ≈⟨ +ᴹ-congʳ (*ₗ-congʳ (R.+-congˡ R.0≈-1*-1+-1)) ⟩
        ((w R.* x R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) *ₗ y) + ((v *ₗ y) + z) ∎
      ; ❲❳⤙⤚-◆-pulloutᵣ = λ v w x y z → begin
        (w *ₗ ((x *ₗ y) + z)) + v ≈⟨ +ᴹ-congʳ (*ₗ-distribˡ w (x *ₗ y) z) ⟩
        ((w *ₗ (x *ₗ y)) + (w *ₗ z)) + v ≈⟨ +ᴹ-assoc (w *ₗ (x *ₗ y)) (w *ₗ z) v ⟩
        (w *ₗ (x *ₗ y)) + ((w *ₗ z) + v) ≈⟨ +ᴹ-congʳ (*ₗ-congˡ (+ᴹ-identityʳ (x *ₗ y))) ⟨
        (w *ₗ ((x *ₗ y) + 0#)) + ((w *ₗ z) + v) ∎
      ; ❲❳⤙⤚-■ᶠ-collapse-dupʳ = λ x → begin
        ((R.- R.1#) *ₗ x) + x ≈⟨ +ᴹ-congˡ (*ₗ-identityˡ x) ⟨
        ((R.- R.1#) *ₗ x) + (R.1# *ₗ x) ≈⟨ *ₗ-distribʳ x (R.- R.1#) R.1# ⟨
        (R.- R.1# R.+ R.1#) *ₗ x ≈⟨ *ₗ-congʳ (R.-‿inverseˡ R.1#) ⟩
        R.0# *ₗ x ≈⟨ *ₗ-zeroˡ x ⟩
        0# ∎
      ; ❲❳⤙⤚-◆ᶠ-collapse-middleˡ = λ x z → begin
        ((R.- R.1# R.* R.- R.1# R.+ R.- R.1#) *ₗ x) + z ≈⟨ +ᴹ-congʳ (*ₗ-congʳ R.0≈-1*-1+-1) ⟨
        ((R.0# *ₗ x) + z) ≈⟨ +ᴹ-congʳ (*ₗ-zeroˡ x) ⟩
        (0# + z) ≈⟨ +ᴹ-identityˡ z ⟩
        z ∎
      ; ❲❳⤙⤚-◆-collapse-middleʳ = λ x z → begin
        (x *ₗ 0#) + z ≈⟨ +ᴹ-congʳ (*ₗ-zeroʳ x) ⟩
        0# + z ≈⟨ +ᴹ-identityˡ z ⟩
        z ∎
      ; ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ = λ x → begin
        ((R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) *ₗ x) + 0# ≈⟨ +ᴹ-congʳ (*ₗ-congʳ R.1≈-1*-1+[-1*-1+-1]) ⟨
        (R.1# *ₗ x) + 0# ≈⟨ +ᴹ-identityʳ (R.1# *ₗ x) ⟩
        R.1# *ₗ x ≈⟨ *ₗ-identityˡ x ⟩
        x ∎
      ; ❲❳⤙⤚-◆ᶠ-◆-outer-associate = λ w x y _ → +ᴹ-congʳ (begin
        (w R.* x R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) *ₗ y ≈⟨ *ₗ-congʳ (R.+-congˡ R.0≈-1*-1+-1) ⟨
        (w R.* x R.+ R.0#) *ₗ y ≈⟨ *ₗ-congʳ (R.+-identityʳ (w R.* x)) ⟩
        (w R.* x) *ₗ y ≈⟨ *ₗ-assoc w x y ⟩
        (w *ₗ (x *ₗ y)) ≈⟨ *ₗ-congˡ (+ᴹ-identityʳ (x *ₗ y)) ⟨
        w *ₗ ((x *ₗ y) + 0#) ∎)
      }
      where
        open IsLeftModule M
        open IsEquivalence ≈ᴹ-isEquivalence using (refl)
        open SetoidReasoning record { isEquivalence = ≈ᴹ-isEquivalence }

  module _ {r m rℓ mℓ} (R : Ring r rℓ) {Carrier : Set m} (_≈_ : Rel Carrier mℓ)
           (_+_ : Op₂ Carrier) (0# : Carrier) (-_ : Op₁ Carrier) (_*ᵣ_ : Opᵣ (Ring.Carrier R) Carrier) where
    private
      F : Fumula r rℓ
      F = FromRing.fumula R
      module R where
        open Ring R public
        open RingProperties R public
        open RingHelpers R public
      module F where
        open Fumula F public
        open FumulaProperties F public

      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      x ⤙ z ⤚❲ s ❳ = (x *ᵣ s) + z

      ◆ : Carrier
      ◆ = 0#

    isRightFumulaExtrusion : (M : IsRightModule R _≈_ _+_ 0# -_ _*ᵣ_) → IsRightFumulaExtrusion F _≈_ _⤙_⤚❲_❳ ◆
    isRightFumulaExtrusion M = record
      { ⤙⤚❲❳-isRightAlmostFumulaExtrusion = record
        { isEquivalence = ≈ᴹ-isEquivalence
        ; ⤙⤚❲❳-cong = λ x≈ z≈ s≈ → +ᴹ-cong (*ᵣ-cong x≈ s≈) z≈
        ; ⤙⤚❲❳-double-exchange = λ v w x y z → begin
          (v *ᵣ w) + ((x *ᵣ y) + z) ≈⟨ +ᴹ-assoc (v *ᵣ w) (x *ᵣ y) z ⟨
          ((v *ᵣ w) + (x *ᵣ y)) + z ≈⟨ +ᴹ-congʳ (+ᴹ-comm (v *ᵣ w) (x *ᵣ y)) ⟩
          ((x *ᵣ y) + (v *ᵣ w)) + z ≈⟨ +ᴹ-assoc (x *ᵣ y) (v *ᵣ w) z ⟩
          (x *ᵣ y) + ((v *ᵣ w) + z) ∎
        }
      ; ⤙⤚❲❳-●ᶠ-inner-commuteₗ = λ x y → begin
        (x *ᵣ (R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#))) + y ≈⟨ +ᴹ-congʳ (*ᵣ-congˡ R.1≈-1*-1+[-1*-1+-1]) ⟨
        (x *ᵣ R.1#) + y ≈⟨ +ᴹ-congʳ (*ᵣ-identityʳ x) ⟩
        x + y ≈⟨ +ᴹ-comm x y ⟩
        y + x ≈⟨ +ᴹ-congʳ (*ᵣ-identityʳ y) ⟨
        (y *ᵣ R.1#) + x ≈⟨ +ᴹ-congʳ (*ᵣ-congˡ R.1≈-1*-1+[-1*-1+-1]) ⟩
        (y *ᵣ (R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#))) + x ∎
      ; ⤙⤚❲❳-◆-pulloutₗ = λ v w x y z → begin
        (((w *ᵣ x) + v) *ᵣ y) + z ≈⟨ +ᴹ-congʳ (*ᵣ-distribʳ y (w *ᵣ x) v) ⟩
        (((w *ᵣ x) *ᵣ y) + (v *ᵣ y)) + z ≈⟨ +ᴹ-assoc ((w *ᵣ x) *ᵣ y) (v *ᵣ y) z ⟩
        ((w *ᵣ x) *ᵣ y) + ((v *ᵣ y) + z) ≈⟨ +ᴹ-congʳ (*ᵣ-congʳ (+ᴹ-identityʳ (w *ᵣ x))) ⟨
        (((w *ᵣ x) + 0#) *ᵣ y) + ((v *ᵣ y) + z) ∎
      ; ⤙⤚❲❳-◆ᶠ-pulloutᵣ = λ v w x y z → begin
        (w *ᵣ (x R.* y R.+ z)) + v ≈⟨ +ᴹ-congʳ (*ᵣ-distribˡ w (x R.* y) z) ⟩
        ((w *ᵣ (x R.* y)) + (w *ᵣ z)) + v ≈⟨ +ᴹ-assoc (w *ᵣ (x R.* y)) (w *ᵣ z) v ⟩
        (w *ᵣ (x R.* y)) + ((w *ᵣ z) + v) ≈⟨ +ᴹ-congʳ (*ᵣ-congˡ (R.+-identityʳ (x R.* y))) ⟨
        (w *ᵣ (x R.* y R.+ R.0#)) + ((w *ᵣ z) + v) ≈⟨ +ᴹ-congʳ (*ᵣ-congˡ (R.+-congˡ R.0≈-1*-1+-1)) ⟩
        (w *ᵣ (x R.* y R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#))) + ((w *ᵣ z) + v) ∎
      ; ⤙⤚❲❳-■ᶠ-collapse-dupˡ = λ x → begin
        (x *ᵣ (R.- R.1#)) + x ≈⟨ +ᴹ-congˡ (*ᵣ-identityʳ x) ⟨
        (x *ᵣ (R.- R.1#)) + (x *ᵣ R.1#) ≈⟨ *ᵣ-distribˡ x (R.- R.1#) R.1# ⟨
        x *ᵣ (R.- R.1# R.+ R.1#) ≈⟨ *ᵣ-congˡ (R.-‿inverseˡ R.1#) ⟩
        (x *ᵣ R.0#) ≈⟨ *ᵣ-zeroʳ x ⟩
        0# ∎
      ; ⤙⤚❲❳-◆-collapse-middleˡ = λ x z → begin
        (0# *ᵣ x) + z ≈⟨ +ᴹ-congʳ (*ᵣ-zeroˡ x) ⟩
        0# + z ≈⟨ +ᴹ-identityˡ z ⟩
        z ∎
      ; ⤙⤚❲❳-◆ᶠ-collapse-middleʳ = λ x z → begin
        (x *ᵣ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) + z ≈⟨ +ᴹ-congʳ (*ᵣ-congˡ R.0≈-1*-1+-1) ⟨
        (x *ᵣ R.0#) + z ≈⟨ +ᴹ-congʳ (*ᵣ-zeroʳ x) ⟩
        0# + z ≈⟨ +ᴹ-identityˡ z ⟩
        z ∎
      ; ⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ = λ x → begin
        (x *ᵣ (R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#))) + 0# ≈⟨ +ᴹ-identityʳ (x *ᵣ (R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#))) ⟩
        x *ᵣ (R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) ≈⟨ *ᵣ-congˡ R.1≈-1*-1+[-1*-1+-1] ⟨
        x *ᵣ R.1# ≈⟨ *ᵣ-identityʳ x ⟩
        x ∎
      ; ⤙⤚❲❳-◆ᶠ-◆-outer-associate = λ w x y _ → +ᴹ-congʳ (begin
        ((w *ᵣ x) + 0#) *ᵣ y ≈⟨ *ᵣ-congʳ (+ᴹ-identityʳ (w *ᵣ x)) ⟩
        ((w *ᵣ x) *ᵣ y) ≈⟨ *ᵣ-assoc w x y ⟩
        (w *ᵣ (x R.* y)) ≈⟨ *ᵣ-congˡ (R.+-identityʳ (x R.* y)) ⟨
        w *ᵣ (x R.* y R.+ R.0#) ≈⟨ *ᵣ-congˡ (R.+-congˡ R.0≈-1*-1+-1) ⟩
        w *ᵣ (x R.* y R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) ∎)
      }
      where
        open IsRightModule M
        open IsEquivalence ≈ᴹ-isEquivalence using (refl)
        open SetoidReasoning record { isEquivalence = ≈ᴹ-isEquivalence }

module FromFumulaExtrusion where

  module _ {f x fℓ xℓ} (F : Fumula f fℓ) {Carrier : Set x} (_≈_ : Rel Carrier xℓ)
           (❲_❳⤙_⤚_ : Op₃ₗ (Fumula.Carrier F) Carrier) (◆ : Carrier) where
    private
      R : Ring f fℓ
      R = FromFumula.ring F
      module F where
        open Fumula F public
        open FumulaProperties F public
      module R where
        open Ring R public
        open RingProperties R public
        open RingHelpers R public

      _+_ : Op₂ Carrier
      x + y = ❲ F.● ❳⤙ x ⤚ y

      0# : Carrier
      0# = ◆

      -_ : Op₁ Carrier
      - x = ❲ F.■ ❳⤙ ◆ ⤚ x

      _*ₗ_ : Opₗ R.Carrier Carrier
      s *ₗ x = ❲ s ❳⤙ ◆ ⤚ x

    isLeftModule : (X : IsLeftFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ ◆) → IsLeftModule R _≈_ _+_ 0# -_ _*ₗ_
    isLeftModule X = record
      { isLeftSemimodule = record
        { +ᴹ-isCommutativeMonoid = record
          { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence
              ; ∙-cong = ❲❳⤙⤚-cong F.refl
              }
            ; assoc = λ x y z → begin
              ❲ F.● ❳⤙ ❲ F.● ❳⤙ x ⤚ y ⤚ z ≈⟨ ❲❳⤙⤚-double-exchange F.● z F.● y x ⟩
              ❲ F.● ❳⤙ ❲ F.● ❳⤙ x ⤚ z ⤚ y ≈⟨ ❲❳⤙⤚-cong F.refl (❲❳⤙⤚-●ᶠ-inner-commuteᵣ x z) refl ⟩
              ❲ F.● ❳⤙ ❲ F.● ❳⤙ z ⤚ x ⤚ y ≈⟨ ❲❳⤙⤚-double-exchange F.● y F.● x z ⟩
              ❲ F.● ❳⤙ ❲ F.● ❳⤙ z ⤚ y ⤚ x ≈⟨ ❲❳⤙⤚-●ᶠ-inner-commuteᵣ (❲ F.● ❳⤙ z ⤚ y) x ⟩
              ❲ F.● ❳⤙ x ⤚ ❲ F.● ❳⤙ z ⤚ y ≈⟨ ❲❳⤙⤚-cong F.refl refl (❲❳⤙⤚-●ᶠ-inner-commuteᵣ z y) ⟩
              ❲ F.● ❳⤙ x ⤚ ❲ F.● ❳⤙ y ⤚ z ∎
            }
          ; identity = ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ , ❲❳⤙⤚-◆-collapse-middleʳ F.●
          }
          ; comm = ❲❳⤙⤚-●ᶠ-inner-commuteᵣ
          }
        ; isPreleftSemimodule = record
          { *ₗ-cong = λ x≈ → ❲❳⤙⤚-cong x≈ refl
          ; *ₗ-zeroˡ = λ x → ❲❳⤙⤚-◆ᶠ-collapse-middleˡ x ◆
          ; *ₗ-distribʳ = λ x s r → begin
            ❲ F.● F.⤙ s ⤚ r ❳⤙ ◆ ⤚ x ≈⟨ ❲❳⤙⤚-◆ᶠ-pulloutₗ s F.● r x ◆ ⟩
            ❲ F.● F.⤙ F.◆ ⤚ r ❳⤙ ❲ s ❳⤙ ◆ ⤚ x ⤚ x ≈⟨ ❲❳⤙⤚-◆ᶠ-◆-outer-associate F.● r x (❲ s ❳⤙ ◆ ⤚ x) ⟩
            ❲ F.● ❳⤙ ❲ s ❳⤙ ◆ ⤚ x ⤚ ❲ r ❳⤙ ◆ ⤚ x ∎
          ; *ₗ-identityˡ = ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ
          ; *ₗ-assoc = λ s r x → ❲❳⤙⤚-◆ᶠ-◆-outer-associate s r x ◆
          ; *ₗ-zeroʳ = λ x → ❲❳⤙⤚-◆-collapse-middleʳ x ◆
          ; *ₗ-distribˡ = λ s x y → begin
            ❲ s ❳⤙ ◆ ⤚ ❲ F.● ❳⤙ x ⤚ y ≈⟨ ❲❳⤙⤚-◆-pulloutᵣ ◆ s F.● y x ⟩
            ❲ s ❳⤙ ❲ s ❳⤙ ◆ ⤚ x ⤚ ❲ F.● ❳⤙ ◆ ⤚ y ≈⟨ ❲❳⤙⤚-cong F.refl (sym (❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ (❲ s ❳⤙ ◆ ⤚ x))) (❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ y) ⟩
            ❲ s ❳⤙ ❲ F.● ❳⤙ ◆ ⤚ ❲ s ❳⤙ ◆ ⤚ x ⤚ y ≈⟨ ❲❳⤙⤚-double-exchange s y F.● (❲ s ❳⤙ ◆ ⤚ x) ◆ ⟩
            ❲ F.● ❳⤙ ❲ s ❳⤙ ◆ ⤚ y ⤚ ❲ s ❳⤙ ◆ ⤚ x ≈⟨ ❲❳⤙⤚-●ᶠ-inner-commuteᵣ (❲ s ❳⤙ ◆ ⤚ y) (❲ s ❳⤙ ◆ ⤚ x) ⟩
            ❲ F.● ❳⤙ ❲ s ❳⤙ ◆ ⤚ x ⤚ ❲ s ❳⤙ ◆ ⤚ y ∎
          }
        }
      ; -ᴹ‿cong = ❲❳⤙⤚-cong F.refl refl
      ; -ᴹ‿inverse =
        (λ x → begin
          ❲ F.● ❳⤙ ❲ F.■ ❳⤙ ◆ ⤚ x ⤚ x ≈⟨ ❲❳⤙⤚-●ᶠ-inner-commuteᵣ (❲ F.■ ❳⤙ ◆ ⤚ x) x ⟩
          ❲ F.● ❳⤙ x ⤚ ❲ F.■ ❳⤙ ◆ ⤚ x ≈⟨ ❲❳⤙⤚-◆ᶠ-◆-outer-associate F.● F.■ x x ⟨
          ❲ F.● F.⤙ F.◆ ⤚ F.■ ❳⤙ x ⤚ x ≈⟨ ❲❳⤙⤚-cong (F.●-◆-collapse-sideˡ F.■) refl refl ⟩
          (❲ F.■ ❳⤙ x ⤚ x) ≈⟨ ❲❳⤙⤚-■ᶠ-collapse-dupʳ x ⟩
          ◆ ∎) ,
        (λ x → begin
          ❲ F.● ❳⤙ x ⤚ ❲ F.■ ❳⤙ ◆ ⤚ x ≈⟨ ❲❳⤙⤚-◆ᶠ-◆-outer-associate F.● F.■ x x ⟨
          ❲ F.● F.⤙ F.◆ ⤚ F.■ ❳⤙ x ⤚ x ≈⟨ ❲❳⤙⤚-cong (F.●-◆-collapse-sideˡ F.■) refl refl ⟩
          ❲ F.■ ❳⤙ x ⤚ x ≈⟨ ❲❳⤙⤚-■ᶠ-collapse-dupʳ x ⟩
          ◆ ∎)
      }
      where
        open IsLeftFumulaExtrusion X
        open LeftProperties F record { isLeftFumulaExtrusion = X }
        open IsEquivalence isEquivalence using (refl; sym)
        open SetoidReasoning (record { isEquivalence = isEquivalence })

  module _ {f x fℓ xℓ} (F : Fumula f fℓ) {Carrier : Set x} (_≈_ : Rel Carrier xℓ)
           (_⤙_⤚❲_❳ : Op₃ᵣ (Fumula.Carrier F) Carrier) (◆ : Carrier) where
    private
      R : Ring f fℓ
      R = FromFumula.ring F
      module F where
        open Fumula F public
        open FumulaProperties F public
      module R where
        open Ring R public
        open RingProperties R public
        open RingHelpers R public

      _+_ : Op₂ Carrier
      x + y = x ⤙ y ⤚❲ F.● ❳

      0# : Carrier
      0# = ◆

      -_ : Op₁ Carrier
      - x = x ⤙ ◆ ⤚❲ F.■ ❳

      _*ᵣ_ : Opᵣ R.Carrier Carrier
      x *ᵣ s = x ⤙ ◆ ⤚❲ s ❳

    isRightModule : (X : IsRightFumulaExtrusion F _≈_ _⤙_⤚❲_❳ ◆) → IsRightModule R _≈_ _+_ 0# -_ _*ᵣ_
    isRightModule X = record
      { isRightSemimodule = record
        { +ᴹ-isCommutativeMonoid = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = isEquivalence
                ; ∙-cong = λ x≈ y≈ → ⤙⤚❲❳-cong x≈ y≈ F.refl
                }
              ; assoc = λ x y z → begin
                x ⤙ y ⤚❲ F.● ❳ ⤙ z ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-cong (⤙⤚❲❳-●ᶠ-inner-commuteₗ x y) refl F.refl ⟩
                y ⤙ x ⤚❲ F.● ❳ ⤙ z ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-●ᶠ-inner-commuteₗ (y ⤙ x ⤚❲ F.● ❳) z ⟩
                z ⤙ y ⤙ x ⤚❲ F.● ❳ ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-double-exchange z F.● y F.● x ⟩
                y ⤙ z ⤙ x ⤚❲ F.● ❳ ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-cong refl (⤙⤚❲❳-●ᶠ-inner-commuteₗ z x) F.refl ⟩
                y ⤙ x ⤙ z ⤚❲ F.● ❳ ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-double-exchange y F.● x F.● z ⟩
                x ⤙ y ⤙ z ⤚❲ F.● ❳ ⤚❲ F.● ❳ ∎
              }
            ; identity = ⤙⤚❲❳-◆-collapse-middleˡ F.● , ⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ
            }
          ; comm = ⤙⤚❲❳-●ᶠ-inner-commuteₗ
          }
        ; isPrerightSemimodule = record
          { *ᵣ-cong = λ x≈ → ⤙⤚❲❳-cong x≈ refl
          ; *ᵣ-zeroʳ = λ x → ⤙⤚❲❳-◆ᶠ-collapse-middleʳ x ◆
          ; *ᵣ-distribˡ = λ x s r → begin
            x ⤙ ◆ ⤚❲ F.● F.⤙ s ⤚ r ❳ ≈⟨ ⤙⤚❲❳-cong refl refl (F.●-inner-commuteʳ s r) ⟩
            x ⤙ ◆ ⤚❲ F.● F.⤙ r ⤚ s ❳ ≈⟨ ⤙⤚❲❳-◆ᶠ-pulloutᵣ ◆ x F.● s r ⟩
            x ⤙ x ⤙ ◆ ⤚❲ r ❳ ⤚❲ F.● F.⤙ F.◆ ⤚ s ❳ ≈⟨ ⤙⤚❲❳-cong refl refl (F.●-outer-commute s (F.■ F.⤙ F.■ ⤚ F.■)) ⟨
            x ⤙ x ⤙ ◆ ⤚❲ r ❳ ⤚❲ s F.⤙ F.◆ ⤚ F.● ❳ ≈⟨ ⤙⤚❲❳-◆ᶠ-◆-outer-associate x s F.● (x ⤙ ◆ ⤚❲ r ❳) ⟨
            x ⤙ ◆ ⤚❲ s ❳ ⤙ x ⤙ ◆ ⤚❲ r ❳ ⤚❲ F.● ❳ ∎
          ; *ᵣ-identityʳ = ⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ
          ; *ᵣ-assoc = λ x s r → ⤙⤚❲❳-◆ᶠ-◆-outer-associate x s r ◆
          ; *ᵣ-zeroˡ = λ x → ⤙⤚❲❳-◆-collapse-middleˡ x ◆
          ; *ᵣ-distribʳ = λ s x y → begin
            x ⤙ y ⤚❲ F.● ❳ ⤙ ◆ ⤚❲ s ❳ ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            {!!} ≈⟨ {!!} ⟩
            x ⤙ ◆ ⤚❲ s ❳ ⤙ y ⤙ ◆ ⤚❲ s ❳ ⤚❲ F.● ❳ ∎
          }
        }
      ; -ᴹ‿cong = λ x≈ → ⤙⤚❲❳-cong x≈ refl F.refl
      ; -ᴹ‿inverse =
        (λ x → begin
          x ⤙ ◆ ⤚❲ F.■ ❳ ⤙ x ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-●ᶠ-inner-commuteₗ (x ⤙ ◆ ⤚❲ F.■ ❳) x ⟩
          x ⤙ x ⤙ ◆ ⤚❲ F.■ ❳ ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-double-exchange x F.● x F.■ ◆ ⟩
          x ⤙ x ⤙ ◆ ⤚❲ F.● ❳ ⤚❲ F.■ ❳ ≈⟨ ⤙⤚❲❳-cong refl (⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ x) F.refl ⟩
          x ⤙ x ⤚❲ F.■ ❳ ≈⟨ ⤙⤚❲❳-■ᶠ-collapse-dupˡ x ⟩
          ◆ ∎) ,
        (λ x → begin
          x ⤙ x ⤙ ◆ ⤚❲ F.■ ❳ ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-double-exchange x F.● x F.■ ◆ ⟩
          x ⤙ x ⤙ ◆ ⤚❲ F.● ❳ ⤚❲ F.■ ❳ ≈⟨ ⤙⤚❲❳-cong refl (⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ x) F.refl ⟩
          x ⤙ x ⤚❲ F.■ ❳ ≈⟨ ⤙⤚❲❳-■ᶠ-collapse-dupˡ x ⟩
          ◆ ∎)
      }
      where
        open IsRightFumulaExtrusion X
        open RightProperties F record { isRightFumulaExtrusion = X }
        open IsEquivalence isEquivalence using (refl; sym)
        open SetoidReasoning (record { isEquivalence = isEquivalence })
