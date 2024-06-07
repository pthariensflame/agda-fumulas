------------------------------------------------------------------------
-- Conversion of fumula extrusions to and from modules over rings.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Convert where
open import Function using (id)
open import Data.Product using (_,_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Algebra.Core
open import Algebra.Bundles
import Algebra.Properties.Group as GroupProperties
import Algebra.Properties.Ring as RingProperties
open import Algebra.Module.Core
open import Algebra.Module.Structures
open import Algebra.Module.Bundles
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

    isLeftFumulaExtrusion : IsLeftModule R _≈_ _+_ 0# -_ _*ₗ_ → IsLeftFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ ◆
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
      ; ❲❳⤙⤚-●ᶠ-inner-commuteʳ = λ x y → begin
        ((R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) *ₗ y) + x ≈⟨ +ᴹ-congʳ (*ₗ-congʳ R.1≈-1*-1+[-1*-1+-1]) ⟨
        (R.1# *ₗ y) + x ≈⟨ +ᴹ-congʳ (*ₗ-identityˡ y) ⟩
        y + x ≈⟨ +ᴹ-congˡ (*ₗ-identityˡ x) ⟨
        y + (R.1# *ₗ x) ≈⟨ +ᴹ-comm y (R.1# *ₗ x) ⟩
        (R.1# *ₗ x) + y ≈⟨ +ᴹ-congʳ (*ₗ-congʳ R.1≈-1*-1+[-1*-1+-1]) ⟩
        ((R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) *ₗ x) + y ∎
      ; ❲❳⤙⤚-◆ᶠ-pulloutˡ = λ v w x y z → begin
        ((w R.* x R.+ v) *ₗ y) + z ≈⟨ +ᴹ-congʳ (*ₗ-distribʳ y (w R.* x) v) ⟩
        (((w R.* x) *ₗ y) + (v *ₗ y)) + z ≈⟨ +ᴹ-assoc ((w R.* x) *ₗ y) (v *ₗ y) z ⟩
        ((w R.* x) *ₗ y) + ((v *ₗ y) + z) ≈⟨ +ᴹ-congʳ (*ₗ-congʳ (R.+-identityʳ (w R.* x))) ⟨
        ((w R.* x R.+ R.0#) *ₗ y) + ((v *ₗ y) + z) ≈⟨ +ᴹ-congʳ (*ₗ-congʳ (R.+-congˡ R.0≈-1*-1+-1)) ⟩
        ((w R.* x R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) *ₗ y) + ((v *ₗ y) + z) ∎
      ; ❲❳⤙⤚-◆-pulloutʳ = λ v w x y z → begin
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

  module _ {r m rℓ mℓ} (R : Ring r rℓ) where
    private
      F : Fumula r rℓ
      F = FromRing.fumula R

    leftFumulaExtrusion : LeftModule R m mℓ → LeftFumulaExtrusion F m mℓ
    leftFumulaExtrusion M = record { isLeftFumulaExtrusion = isLeftFumulaExtrusion R _≈ᴹ_ _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ isLeftModule }
      where open LeftModule M

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

    isRightFumulaExtrusion : IsRightModule R _≈_ _+_ 0# -_ _*ᵣ_ → IsRightFumulaExtrusion F _≈_ _⤙_⤚❲_❳ ◆
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
      ; ⤙⤚❲❳-●ᶠ-inner-commuteˡ = λ x y → begin
        (x *ᵣ (R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#))) + y ≈⟨ +ᴹ-congʳ (*ᵣ-congˡ R.1≈-1*-1+[-1*-1+-1]) ⟨
        (x *ᵣ R.1#) + y ≈⟨ +ᴹ-congʳ (*ᵣ-identityʳ x) ⟩
        x + y ≈⟨ +ᴹ-comm x y ⟩
        y + x ≈⟨ +ᴹ-congʳ (*ᵣ-identityʳ y) ⟨
        (y *ᵣ R.1#) + x ≈⟨ +ᴹ-congʳ (*ᵣ-congˡ R.1≈-1*-1+[-1*-1+-1]) ⟩
        (y *ᵣ (R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#))) + x ∎
      ; ⤙⤚❲❳-◆-pulloutˡ = λ v w x y z → begin
        (((w *ᵣ x) + v) *ᵣ y) + z ≈⟨ +ᴹ-congʳ (*ᵣ-distribʳ y (w *ᵣ x) v) ⟩
        (((w *ᵣ x) *ᵣ y) + (v *ᵣ y)) + z ≈⟨ +ᴹ-assoc ((w *ᵣ x) *ᵣ y) (v *ᵣ y) z ⟩
        ((w *ᵣ x) *ᵣ y) + ((v *ᵣ y) + z) ≈⟨ +ᴹ-congʳ (*ᵣ-congʳ (+ᴹ-identityʳ (w *ᵣ x))) ⟨
        (((w *ᵣ x) + 0#) *ᵣ y) + ((v *ᵣ y) + z) ∎
      ; ⤙⤚❲❳-◆ᶠ-pulloutʳ = λ v w x y z → begin
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

  module _ {r m rℓ mℓ} (R : Ring r rℓ) where
    private
      F : Fumula r rℓ
      F = FromRing.fumula R

    rightFumulaExtrusion : RightModule R m mℓ → RightFumulaExtrusion F m mℓ
    rightFumulaExtrusion M = record { isRightFumulaExtrusion = isRightFumulaExtrusion R _≈ᴹ_ _+ᴹ_ 0ᴹ -ᴹ_ _*ᵣ_ isRightModule }
      where open RightModule M

  module _ {rₗ rᵣ m rℓₗ rℓᵣ mℓ} (Rₗ : Ring rₗ rℓₗ) (Rᵣ : Ring rᵣ rℓᵣ) {Carrier : Set m}
           (_≈_ : Rel Carrier mℓ) (_+_ : Op₂ Carrier) (0# : Carrier) (-_ : Op₁ Carrier)
           (_*ₗ_ : Opₗ (Ring.Carrier Rₗ) Carrier) (_*ᵣ_ : Opᵣ (Ring.Carrier Rᵣ) Carrier) where
    private
      Fₗ : Fumula rₗ rℓₗ
      Fₗ = FromRing.fumula Rₗ
      module Rₗ where
        open Ring Rₗ public
        open RingProperties Rₗ public
        open RingHelpers Rₗ public
      module Fₗ where
        open Fumula Fₗ public
        open FumulaProperties Fₗ public
      Fᵣ : Fumula rᵣ rℓᵣ
      Fᵣ = FromRing.fumula Rᵣ
      module Rᵣ where
        open Ring Rᵣ public
        open RingProperties Rᵣ public
        open RingHelpers Rᵣ public
      module Fᵣ where
        open Fumula Fᵣ public
        open FumulaProperties Fᵣ public

      ❲_❳⤙_⤚_ : Op₃ₗ Fₗ.Carrier Carrier
      ❲ s ❳⤙ z ⤚ x = (s *ₗ x) + z

      _⤙_⤚❲_❳ : Op₃ᵣ Fᵣ.Carrier Carrier
      x ⤙ z ⤚❲ s ❳ = (x *ᵣ s) + z

      ◆ : Carrier
      ◆ = 0#

    isDoubleFumulaExtrusion : IsBimodule Rₗ Rᵣ _≈_ _+_ 0# -_ _*ₗ_ _*ᵣ_ → IsDoubleFumulaExtrusion Fₗ Fᵣ _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
    isDoubleFumulaExtrusion M = record
      { isDoubleAlmostFumulaExtrusion = record
        { isEquivalence = ≈ᴹ-isEquivalence
        ; ❲❳⤙⤚-cong = ❲❳⤙⤚-cong
        ; ❲❳⤙⤚-double-exchange = ❲❳⤙⤚-double-exchange
        ; ⤙⤚❲❳-cong = ⤙⤚❲❳-cong
        ; ⤙⤚❲❳-double-exchange = ⤙⤚❲❳-double-exchange
        ; ❲❳⤙⤚-⤙⤚❲❳-double-exchange = λ v w x y z → begin
          (v *ₗ w) + ((x *ᵣ y) + z) ≈⟨ +ᴹ-assoc (v *ₗ w) (x *ᵣ y) z ⟨
          ((v *ₗ w) + (x *ᵣ y)) + z ≈⟨ +ᴹ-congʳ (+ᴹ-comm (v *ₗ w) (x *ᵣ y)) ⟩
          ((x *ᵣ y) + (v *ₗ w)) + z ≈⟨ +ᴹ-assoc (x *ᵣ y) (v *ₗ w) z ⟩
          (x *ᵣ y) + ((v *ₗ w) + z) ∎
        }
      ; ❲❳⤙⤚-●ᶠ-inner-commuteʳ = ❲❳⤙⤚-●ᶠ-inner-commuteʳ
      ; ❲❳⤙⤚-◆ᶠ-pulloutˡ = ❲❳⤙⤚-◆ᶠ-pulloutˡ
      ; ❲❳⤙⤚-◆-pulloutʳ = ❲❳⤙⤚-◆-pulloutʳ
      ; ❲❳⤙⤚-■ᶠ-collapse-dupʳ = ❲❳⤙⤚-■ᶠ-collapse-dupʳ
      ; ❲❳⤙⤚-◆ᶠ-collapse-middleˡ = ❲❳⤙⤚-◆ᶠ-collapse-middleˡ
      ; ❲❳⤙⤚-◆-collapse-middleʳ = ❲❳⤙⤚-◆-collapse-middleʳ
      ; ❲❳⤙⤚-◆ᶠ-◆-outer-associate = ❲❳⤙⤚-◆ᶠ-◆-outer-associate
      ; ⤙⤚❲❳-●ᶠ-inner-commuteˡ = ⤙⤚❲❳-●ᶠ-inner-commuteˡ
      ; ⤙⤚❲❳-◆-pulloutˡ = ⤙⤚❲❳-◆-pulloutˡ
      ; ⤙⤚❲❳-◆ᶠ-pulloutʳ = ⤙⤚❲❳-◆ᶠ-pulloutʳ
      ; ⤙⤚❲❳-■ᶠ-collapse-dupˡ = ⤙⤚❲❳-■ᶠ-collapse-dupˡ
      ; ⤙⤚❲❳-◆-collapse-middleˡ = ⤙⤚❲❳-◆-collapse-middleˡ
      ; ⤙⤚❲❳-◆ᶠ-collapse-middleʳ = ⤙⤚❲❳-◆ᶠ-collapse-middleʳ
      ; ⤙⤚❲❳-◆ᶠ-◆-outer-associate = ⤙⤚❲❳-◆ᶠ-◆-outer-associate
      ; ⤙⤚❲❳-❲❳⤙⤚-◆-pulloutˡ = λ v w x y z → begin
        (((w *ₗ x) + v) *ᵣ y) + z ≈⟨ +ᴹ-congʳ (*ᵣ-distribʳ y (w *ₗ x) v) ⟩
        (((w *ₗ x) *ᵣ y) + (v *ᵣ y)) + z ≈⟨ +ᴹ-congʳ (+ᴹ-congʳ (*ᵣ-congʳ (+ᴹ-identityʳ (w *ₗ x)))) ⟨
        ((((w *ₗ x) + 0#) *ᵣ y) + (v *ᵣ y)) + z ≈⟨ +ᴹ-assoc (((w *ₗ x) + 0#) *ᵣ y) (v *ᵣ y) z ⟩
        (((w *ₗ x) + 0#) *ᵣ y) + ((v *ᵣ y) + z) ∎
      ; ❲❳⤙⤚-⤙⤚❲❳-◆-pulloutʳ = λ v w x y z → begin
        (w *ₗ ((x *ᵣ y) + z)) + v ≈⟨ +ᴹ-congʳ (*ₗ-distribˡ w (x *ᵣ y) z) ⟩
        ((w *ₗ (x *ᵣ y)) + (w *ₗ z)) + v ≈⟨ +ᴹ-congʳ (+ᴹ-congʳ (*ₗ-congˡ (+ᴹ-identityʳ (x *ᵣ y)))) ⟨
        ((w *ₗ ((x *ᵣ y) + 0#)) + (w *ₗ z)) + v ≈⟨ +ᴹ-assoc (w *ₗ ((x *ᵣ y) + 0#)) (w *ₗ z) v ⟩
        (w *ₗ ((x *ᵣ y) + 0#)) + ((w *ₗ z) + v) ∎
      ; ■ᶠ-outer-commute = λ x z → +ᴹ-congʳ (begin
        x *ᵣ (Rᵣ.- Rᵣ.1#) ≈⟨ -ᴹ⇒-‿distribʳ-*ᵣ x Rᵣ.1# ⟨
        - (x *ᵣ Rᵣ.1#) ≈⟨ -ᴹ‿cong (*ᵣ-identityʳ x) ⟩
        - x ≈⟨ -ᴹ‿cong (*ₗ-identityˡ x) ⟨
        - (Rₗ.1# *ₗ x) ≈⟨ -ᴹ⇒-‿distribˡ-*ₗ Rₗ.1# x ⟩
        (Rₗ.- Rₗ.1#) *ₗ x ∎)
      ; ◆ᶠ-outer-commute = λ x z → +ᴹ-congʳ (begin
        x *ᵣ (Rᵣ.- Rᵣ.1# Rᵣ.* Rᵣ.- Rᵣ.1# Rᵣ.+ Rᵣ.- Rᵣ.1#) ≈⟨ *ᵣ-congˡ Rᵣ.0≈-1*-1+-1 ⟨
        x *ᵣ Rᵣ.0# ≈⟨ *ᵣ-zeroʳ x ⟩
        0# ≈⟨ *ₗ-zeroˡ x ⟨
        Rₗ.0# *ₗ x ≈⟨ *ₗ-congʳ Rₗ.0≈-1*-1+-1 ⟩
        (Rₗ.- Rₗ.1# Rₗ.* Rₗ.- Rₗ.1# Rₗ.+ Rₗ.- Rₗ.1#) *ₗ x ∎)
      ; ●ᶠ-outer-commute = λ x z → +ᴹ-congʳ (begin
        x *ᵣ (Rᵣ.- Rᵣ.1# Rᵣ.* Rᵣ.- Rᵣ.1# Rᵣ.+ (Rᵣ.- Rᵣ.1# Rᵣ.* Rᵣ.- Rᵣ.1# Rᵣ.+ Rᵣ.- Rᵣ.1#)) ≈⟨ *ᵣ-congˡ Rᵣ.1≈-1*-1+[-1*-1+-1] ⟨
        x *ᵣ Rᵣ.1# ≈⟨ *ᵣ-identityʳ x ⟩
        x ≈⟨ *ₗ-identityˡ x ⟨
        Rₗ.1# *ₗ x ≈⟨ *ₗ-congʳ Rₗ.1≈-1*-1+[-1*-1+-1] ⟩
        (Rₗ.- Rₗ.1# Rₗ.* Rₗ.- Rₗ.1# Rₗ.+ (Rₗ.- Rₗ.1# Rₗ.* Rₗ.- Rₗ.1# Rₗ.+ Rₗ.- Rₗ.1#)) *ₗ x ∎)
      ; ◆-outer-associate = λ w x y z → +ᴹ-congʳ (begin
        ((w *ₗ x) + 0#) *ᵣ y ≈⟨ *ᵣ-congʳ (+ᴹ-identityʳ (w *ₗ x)) ⟩
        (w *ₗ x) *ᵣ y ≈⟨ *ₗ-*ᵣ-assoc w x y ⟩
        (w *ₗ (x *ᵣ y)) ≈⟨ *ₗ-congˡ (+ᴹ-identityʳ (x *ᵣ y)) ⟨
        w *ₗ ((x *ᵣ y) + 0#) ∎)
      }
      where
        open IsBimodule M
        open IsLeftFumulaExtrusion (isLeftFumulaExtrusion Rₗ _≈_ _+_ 0# -_ _*ₗ_ isLeftModule) hiding (isEquivalence)
        open IsRightFumulaExtrusion (isRightFumulaExtrusion Rᵣ _≈_ _+_ 0# -_ _*ᵣ_ isRightModule) hiding (isEquivalence)
        open SetoidReasoning record { isEquivalence = ≈ᴹ-isEquivalence }
        open IsEquivalence ≈ᴹ-isEquivalence using (sym)

        -ᴹ⇒-‿distribˡ-*ₗ : ∀ x y → (- (x *ₗ y)) ≈ ((Rₗ.- x) *ₗ y)
        -ᴹ⇒-‿distribˡ-*ₗ x y = sym (begin
          (Rₗ.- x) *ₗ y ≈⟨ +ᴹ-identityʳ ((Rₗ.- x) *ₗ y) ⟨
          ((Rₗ.- x) *ₗ y) + 0# ≈⟨ +ᴹ-congˡ (-ᴹ‿inverseʳ (x *ₗ y)) ⟨
          ((Rₗ.- x) *ₗ y) + ((x *ₗ y) + (- (x *ₗ y))) ≈⟨ +ᴹ-assoc ((Rₗ.- x) *ₗ y) (x *ₗ y) (- (x *ₗ y)) ⟨
          (((Rₗ.- x) *ₗ y) + (x *ₗ y)) + (- (x *ₗ y)) ≈⟨ +ᴹ-congʳ (*ₗ-distribʳ y (Rₗ.- x) x) ⟨
          ((((Rₗ.- x) Rₗ.+ x) *ₗ y) + (- (x *ₗ y))) ≈⟨ +ᴹ-congʳ (*ₗ-congʳ (Rₗ.-‿inverseˡ x)) ⟩
          ((Rₗ.0# *ₗ y) + (- (x *ₗ y))) ≈⟨ +ᴹ-congʳ (*ₗ-zeroˡ y) ⟩
          (0# + (- (x *ₗ y))) ≈⟨ +ᴹ-identityˡ (- (x *ₗ y)) ⟩
          - (x *ₗ y) ∎)

        -ᴹ⇒-‿distribʳ-*ᵣ : ∀ x y → (- (x *ᵣ y)) ≈ (x *ᵣ (Rᵣ.- y))
        -ᴹ⇒-‿distribʳ-*ᵣ x y = sym (begin
          x *ᵣ (Rᵣ.- y) ≈⟨ +ᴹ-identityˡ (x *ᵣ (Rᵣ.- y)) ⟨
          0# + (x *ᵣ (Rᵣ.- y)) ≈⟨ +ᴹ-congʳ (-ᴹ‿inverseˡ (x *ᵣ y)) ⟨
          ((- (x *ᵣ y)) + (x *ᵣ y)) + (x *ᵣ (Rᵣ.- y)) ≈⟨ +ᴹ-assoc (- (x *ᵣ y)) (x *ᵣ y) (x *ᵣ (Rᵣ.- y)) ⟩
          (- (x *ᵣ y)) + ((x *ᵣ y) + (x *ᵣ (Rᵣ.- y))) ≈⟨ +ᴹ-congˡ (*ᵣ-distribˡ x y (Rᵣ.- y)) ⟨
          (- (x *ᵣ y)) + (x *ᵣ (y Rᵣ.+ Rᵣ.- y)) ≈⟨ +ᴹ-congˡ (*ᵣ-congˡ (Rᵣ.-‿inverseʳ y)) ⟩
          (- (x *ᵣ y)) + (x *ᵣ Rᵣ.0#) ≈⟨ +ᴹ-congˡ (*ᵣ-zeroʳ x) ⟩
          (- (x *ᵣ y)) + 0# ≈⟨ +ᴹ-identityʳ (- (x *ᵣ y)) ⟩
          - (x *ᵣ y) ∎)

  module _ {rₗ rᵣ m rℓₗ rℓᵣ mℓ} (Rₗ : Ring rₗ rℓₗ) (Rᵣ : Ring rᵣ rℓᵣ) where
    private
      Fₗ : Fumula rₗ rℓₗ
      Fₗ = FromRing.fumula Rₗ
      Fᵣ : Fumula rᵣ rℓᵣ
      Fᵣ = FromRing.fumula Rᵣ

    doubleFumulaExtrusion : Bimodule Rₗ Rᵣ m mℓ → DoubleFumulaExtrusion Fₗ Fᵣ m mℓ
    doubleFumulaExtrusion M = record { isDoubleFumulaExtrusion = isDoubleFumulaExtrusion Rₗ Rᵣ _≈ᴹ_ _+ᴹ_ 0ᴹ -ᴹ_ _*ₗ_ _*ᵣ_ isBimodule }
      where open Bimodule M

  module _ {r m rℓ mℓ} (R : CommutativeRing r rℓ) {Carrier : Set m} (_≈_ : Rel Carrier mℓ)
           (_+_ : Op₂ Carrier) (0# : Carrier) (-_ : Op₁ Carrier)
           (_*ₗ_ : Opₗ (CommutativeRing.Carrier R) Carrier) (_*ᵣ_ : Opᵣ (CommutativeRing.Carrier R) Carrier) where
    private
      F : ReversibleFumula r rℓ
      F = FromRing.reversibleFumula R
      module R where
        open CommutativeRing R public
        open RingProperties ring public
        open RingHelpers ring public
      module F where
        open ReversibleFumula F public
        open FumulaProperties fumula public

      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      ❲ s ❳⤙ z ⤚ x = (s *ₗ x) + z

      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      x ⤙ z ⤚❲ s ❳ = (x *ᵣ s) + z

      ◆ : Carrier
      ◆ = 0#

    isFumulaExtrusion : IsModule R _≈_ _+_ 0# -_ _*ₗ_ _*ᵣ_ → IsFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
    isFumulaExtrusion M = record
      { isDoubleFumulaExtrusion = iDFE
      ; outer-commute = λ y x _ → +ᴹ-congʳ (*ₗ-*ᵣ-coincident x y)
      }
      where
        open IsModule M
        iDFE : IsDoubleFumulaExtrusion F.fumula F.fumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
        iDFE = isDoubleFumulaExtrusion R.ring R.ring _≈_ _+_ 0# -_ _*ₗ_ _*ᵣ_ isBimodule
        open IsDoubleFumulaExtrusion iDFE

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

    isLeftModule : IsLeftFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ ◆ → IsLeftModule R _≈_ _+_ 0# -_ _*ₗ_
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
              ❲ F.● ❳⤙ ❲ F.● ❳⤙ x ⤚ z ⤚ y ≈⟨ ❲❳⤙⤚-cong F.refl (❲❳⤙⤚-●ᶠ-inner-commuteʳ x z) refl ⟩
              ❲ F.● ❳⤙ ❲ F.● ❳⤙ z ⤚ x ⤚ y ≈⟨ ❲❳⤙⤚-double-exchange F.● y F.● x z ⟩
              ❲ F.● ❳⤙ ❲ F.● ❳⤙ z ⤚ y ⤚ x ≈⟨ ❲❳⤙⤚-●ᶠ-inner-commuteʳ (❲ F.● ❳⤙ z ⤚ y) x ⟩
              ❲ F.● ❳⤙ x ⤚ ❲ F.● ❳⤙ z ⤚ y ≈⟨ ❲❳⤙⤚-cong F.refl refl (❲❳⤙⤚-●ᶠ-inner-commuteʳ z y) ⟩
              ❲ F.● ❳⤙ x ⤚ ❲ F.● ❳⤙ y ⤚ z ∎
            }
          ; identity = ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ , ❲❳⤙⤚-◆-collapse-middleʳ F.●
          }
          ; comm = ❲❳⤙⤚-●ᶠ-inner-commuteʳ
          }
        ; isPreleftSemimodule = record
          { *ₗ-cong = λ x≈ → ❲❳⤙⤚-cong x≈ refl
          ; *ₗ-zeroˡ = λ x → ❲❳⤙⤚-◆ᶠ-collapse-middleˡ x ◆
          ; *ₗ-distribʳ = λ x s r → begin
            ❲ F.● F.⤙ s ⤚ r ❳⤙ ◆ ⤚ x ≈⟨ ❲❳⤙⤚-◆ᶠ-pulloutˡ s F.● r x ◆ ⟩
            ❲ F.● F.⤙ F.◆ ⤚ r ❳⤙ ❲ s ❳⤙ ◆ ⤚ x ⤚ x ≈⟨ ❲❳⤙⤚-◆ᶠ-◆-outer-associate F.● r x (❲ s ❳⤙ ◆ ⤚ x) ⟩
            ❲ F.● ❳⤙ ❲ s ❳⤙ ◆ ⤚ x ⤚ ❲ r ❳⤙ ◆ ⤚ x ∎
          ; *ₗ-identityˡ = ❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ
          ; *ₗ-assoc = λ s r x → ❲❳⤙⤚-◆ᶠ-◆-outer-associate s r x ◆
          ; *ₗ-zeroʳ = λ x → ❲❳⤙⤚-◆-collapse-middleʳ x ◆
          ; *ₗ-distribˡ = λ s x y → begin
            ❲ s ❳⤙ ◆ ⤚ ❲ F.● ❳⤙ x ⤚ y ≈⟨ ❲❳⤙⤚-◆-pulloutʳ ◆ s F.● y x ⟩
            ❲ s ❳⤙ ❲ s ❳⤙ ◆ ⤚ x ⤚ ❲ F.● ❳⤙ ◆ ⤚ y ≈⟨ ❲❳⤙⤚-cong F.refl (sym (❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ (❲ s ❳⤙ ◆ ⤚ x))) (❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ y) ⟩
            ❲ s ❳⤙ ❲ F.● ❳⤙ ◆ ⤚ ❲ s ❳⤙ ◆ ⤚ x ⤚ y ≈⟨ ❲❳⤙⤚-double-exchange s y F.● (❲ s ❳⤙ ◆ ⤚ x) ◆ ⟩
            ❲ F.● ❳⤙ ❲ s ❳⤙ ◆ ⤚ y ⤚ ❲ s ❳⤙ ◆ ⤚ x ≈⟨ ❲❳⤙⤚-●ᶠ-inner-commuteʳ (❲ s ❳⤙ ◆ ⤚ y) (❲ s ❳⤙ ◆ ⤚ x) ⟩
            ❲ F.● ❳⤙ ❲ s ❳⤙ ◆ ⤚ x ⤚ ❲ s ❳⤙ ◆ ⤚ y ∎
          }
        }
      ; -ᴹ‿cong = ❲❳⤙⤚-cong F.refl refl
      ; -ᴹ‿inverse =
        (λ x → begin
          ❲ F.● ❳⤙ ❲ F.■ ❳⤙ ◆ ⤚ x ⤚ x ≈⟨ ❲❳⤙⤚-●ᶠ-inner-commuteʳ (❲ F.■ ❳⤙ ◆ ⤚ x) x ⟩
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

  module _ {f x fℓ xℓ} (F : Fumula f fℓ) where
    private
      R : Ring f fℓ
      R = FromFumula.ring F

    leftModule : LeftFumulaExtrusion F x xℓ → LeftModule R x xℓ
    leftModule X = record { isLeftModule = isLeftModule F _≈_ ❲_❳⤙_⤚_ ◆ isLeftFumulaExtrusion }
      where open LeftFumulaExtrusion X

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

    isRightModule : IsRightFumulaExtrusion F _≈_ _⤙_⤚❲_❳ ◆ → IsRightModule R _≈_ _+_ 0# -_ _*ᵣ_
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
                x ⤙ y ⤚❲ F.● ❳ ⤙ z ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-cong (⤙⤚❲❳-●ᶠ-inner-commuteˡ x y) refl F.refl ⟩
                y ⤙ x ⤚❲ F.● ❳ ⤙ z ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-●ᶠ-inner-commuteˡ (y ⤙ x ⤚❲ F.● ❳) z ⟩
                z ⤙ y ⤙ x ⤚❲ F.● ❳ ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-double-exchange z F.● y F.● x ⟩
                y ⤙ z ⤙ x ⤚❲ F.● ❳ ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-cong refl (⤙⤚❲❳-●ᶠ-inner-commuteˡ z x) F.refl ⟩
                y ⤙ x ⤙ z ⤚❲ F.● ❳ ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-double-exchange y F.● x F.● z ⟩
                x ⤙ y ⤙ z ⤚❲ F.● ❳ ⤚❲ F.● ❳ ∎
              }
            ; identity = ⤙⤚❲❳-◆-collapse-middleˡ F.● , ⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ
            }
          ; comm = ⤙⤚❲❳-●ᶠ-inner-commuteˡ
          }
        ; isPrerightSemimodule = record
          { *ᵣ-cong = λ x≈ → ⤙⤚❲❳-cong x≈ refl
          ; *ᵣ-zeroʳ = λ x → ⤙⤚❲❳-◆ᶠ-collapse-middleʳ x ◆
          ; *ᵣ-distribˡ = λ x s r → begin
            x ⤙ ◆ ⤚❲ F.● F.⤙ s ⤚ r ❳ ≈⟨ ⤙⤚❲❳-cong refl refl (F.●-inner-commuteʳ s r) ⟩
            x ⤙ ◆ ⤚❲ F.● F.⤙ r ⤚ s ❳ ≈⟨ ⤙⤚❲❳-◆ᶠ-pulloutʳ ◆ x F.● s r ⟩
            x ⤙ x ⤙ ◆ ⤚❲ r ❳ ⤚❲ F.● F.⤙ F.◆ ⤚ s ❳ ≈⟨ ⤙⤚❲❳-cong refl refl (F.●-outer-commute s (F.■ F.⤙ F.■ ⤚ F.■)) ⟨
            x ⤙ x ⤙ ◆ ⤚❲ r ❳ ⤚❲ s F.⤙ F.◆ ⤚ F.● ❳ ≈⟨ ⤙⤚❲❳-◆ᶠ-◆-outer-associate x s F.● (x ⤙ ◆ ⤚❲ r ❳) ⟨
            x ⤙ ◆ ⤚❲ s ❳ ⤙ x ⤙ ◆ ⤚❲ r ❳ ⤚❲ F.● ❳ ∎
          ; *ᵣ-identityʳ = ⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ
          ; *ᵣ-assoc = λ x s r → ⤙⤚❲❳-◆ᶠ-◆-outer-associate x s r ◆
          ; *ᵣ-zeroˡ = λ x → ⤙⤚❲❳-◆-collapse-middleˡ x ◆
          ; *ᵣ-distribʳ = λ s x y → begin
            x ⤙ y ⤚❲ F.● ❳ ⤙ ◆ ⤚❲ s ❳ ≈⟨ ⤙⤚❲❳-◆-pulloutˡ y x F.● s ◆ ⟩
            x ⤙ ◆ ⤚❲ F.● ❳ ⤙ y ⤙ ◆ ⤚❲ s ❳ ⤚❲ s ❳ ≈⟨ ⤙⤚❲❳-cong (⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ x) (sym (⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ (y ⤙ ◆ ⤚❲ s ❳))) F.refl ⟩
            x ⤙ y ⤙ ◆ ⤚❲ s ❳ ⤙ ◆ ⤚❲ F.● ❳ ⤚❲ s ❳ ≈⟨ ⤙⤚❲❳-double-exchange x s (y ⤙ ◆ ⤚❲ s ❳) F.● ◆ ⟩
            ((y ⤙ ◆ ⤚❲ s ❳) ⤙ x ⤙ ◆ ⤚❲ s ❳ ⤚❲ F.● ❳) ≈⟨ ⤙⤚❲❳-●ᶠ-inner-commuteˡ (y ⤙ ◆ ⤚❲ s ❳) (x ⤙ ◆ ⤚❲ s ❳) ⟩
            x ⤙ ◆ ⤚❲ s ❳ ⤙ y ⤙ ◆ ⤚❲ s ❳ ⤚❲ F.● ❳ ∎
          }
        }
      ; -ᴹ‿cong = λ x≈ → ⤙⤚❲❳-cong x≈ refl F.refl
      ; -ᴹ‿inverse =
        (λ x → begin
          x ⤙ ◆ ⤚❲ F.■ ❳ ⤙ x ⤚❲ F.● ❳ ≈⟨ ⤙⤚❲❳-●ᶠ-inner-commuteˡ (x ⤙ ◆ ⤚❲ F.■ ❳) x ⟩
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

  module _ {f x fℓ xℓ} (F : Fumula f fℓ) where
    private
      R : Ring f fℓ
      R = FromFumula.ring F

    rightModule : RightFumulaExtrusion F x xℓ → RightModule R x xℓ
    rightModule X = record { isRightModule = isRightModule F _≈_ _⤙_⤚❲_❳ ◆ isRightFumulaExtrusion }
      where open RightFumulaExtrusion X

  module _ {fₗ fᵣ x fℓₗ fℓᵣ xℓ} (Fₗ : Fumula fₗ fℓₗ) (Fᵣ : Fumula fᵣ fℓᵣ) {Carrier : Set x} (_≈_ : Rel Carrier xℓ)
           (❲_❳⤙_⤚_ : Op₃ₗ (Fumula.Carrier Fₗ) Carrier) (_⤙_⤚❲_❳ : Op₃ᵣ (Fumula.Carrier Fᵣ) Carrier) (◆ : Carrier) where
    private
      Rₗ : Ring fₗ fℓₗ
      Rₗ = FromFumula.ring Fₗ
      module Fₗ where
        open Fumula Fₗ public
        open FumulaProperties Fₗ public
      module Rₗ where
        open Ring Rₗ public
        open RingProperties Rₗ public
        open RingHelpers Rₗ public
      Rᵣ : Ring fᵣ fℓᵣ
      Rᵣ = FromFumula.ring Fᵣ
      module Fᵣ where
        open Fumula Fᵣ public
        open FumulaProperties Fᵣ public
      module Rᵣ where
        open Ring Rᵣ public
        open RingProperties Rᵣ public
        open RingHelpers Rᵣ public

      _+_ : Op₂ Carrier
      x + y = ❲ Fₗ.● ❳⤙ x ⤚ y

      _+′_ : Op₂ Carrier
      x +′ y = x ⤙ y ⤚❲ Fᵣ.● ❳

      0# : Carrier
      0# = ◆

      -_ : Op₁ Carrier
      - x = ❲ Fₗ.■ ❳⤙ ◆ ⤚ x

      _*ₗ_ : Opₗ Rₗ.Carrier Carrier
      s *ₗ x = ❲ s ❳⤙ ◆ ⤚ x

      _*ᵣ_ : Opᵣ Rᵣ.Carrier Carrier
      x *ᵣ s = x ⤙ ◆ ⤚❲ s ❳

    isBimodule : IsDoubleFumulaExtrusion Fₗ Fᵣ _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆ → IsBimodule Rₗ Rᵣ _≈_ _+_ 0# -_ _*ₗ_ _*ᵣ_
    isBimodule X = record
      { isBisemimodule = record
        { +ᴹ-isCommutativeMonoid = L.+ᴹ-isCommutativeMonoid
        ; isPreleftSemimodule = L.isPreleftSemimodule
        ; isPrerightSemimodule = record
          { *ᵣ-cong = R.*ᵣ-cong
          ; *ᵣ-zeroʳ = R.*ᵣ-zeroʳ
          ; *ᵣ-distribˡ = λ x s r → begin
            x *ᵣ (s Rᵣ.+ r) ≈⟨ R.*ᵣ-distribˡ x s r ⟩
            (x *ᵣ s) +′ (x *ᵣ r) ≈⟨ +≈+′ (x *ᵣ s) (x *ᵣ r) ⟨
            (x *ᵣ s) + (x *ᵣ r) ∎
          ; *ᵣ-identityʳ = R.*ᵣ-identityʳ
          ; *ᵣ-assoc = R.*ᵣ-assoc
          ; *ᵣ-zeroˡ = R.*ᵣ-zeroˡ
          ; *ᵣ-distribʳ = λ x s r → begin
            (s + r) *ᵣ x ≈⟨ R.*ᵣ-congʳ (+≈+′ s r) ⟩
            (s +′ r) *ᵣ x ≈⟨ R.*ᵣ-distribʳ x s r ⟩
            (s *ᵣ x) +′ (r *ᵣ x) ≈⟨ +≈+′ (s *ᵣ x) (r *ᵣ x) ⟨
            (s *ᵣ x) + (r *ᵣ x) ∎
          }
        ; *ₗ-*ᵣ-assoc = λ s x r → ◆-outer-associate s x r ◆
        }
      ; -ᴹ‿cong = L.-ᴹ‿cong
      ; -ᴹ‿inverse = L.-ᴹ‿inverse
      }
      where
        open IsDoubleFumulaExtrusion X
        L = isLeftModule Fₗ _≈_ ❲_❳⤙_⤚_ ◆ ❲❳⤙⤚-isLeftFumulaExtrusion
        R = isRightModule Fᵣ _≈_ _⤙_⤚❲_❳ ◆ ⤙⤚❲❳-isRightFumulaExtrusion
        module L where
          open IsLeftModule L public
          open LeftProperties Fₗ record { isLeftFumulaExtrusion = ❲❳⤙⤚-isLeftFumulaExtrusion } public
        module R where
          open IsRightModule R public
          open RightProperties Fᵣ record { isRightFumulaExtrusion = ⤙⤚❲❳-isRightFumulaExtrusion } public
        open IsEquivalence isEquivalence using (refl)
        open SetoidReasoning record { isEquivalence = isEquivalence }

        +≈+′ : ∀ x y → (x + y) ≈ (x +′ y)
        +≈+′ x y = begin
          ❲ Fₗ.● ❳⤙ x ⤚ y ≈⟨ ❲❳⤙⤚-●ᶠ-inner-commuteʳ x y ⟩
          ❲ Fₗ.● ❳⤙ y ⤚ x ≈⟨ ❲❳⤙⤚-cong Fₗ.refl refl (R.⤙⤚❲❳-●ᶠ-◆-collapse-sideʳ x) ⟨
          ❲ Fₗ.● ❳⤙ y ⤚ (x ⤙ ◆ ⤚❲ Fᵣ.● ❳) ≈⟨ ◆-outer-associate Fₗ.● x Fᵣ.● y ⟨
          (❲ Fₗ.● ❳⤙ ◆ ⤚ x) ⤙ y ⤚❲ Fᵣ.● ❳ ≈⟨ ⤙⤚❲❳-cong (L.❲❳⤙⤚-●ᶠ-◆-collapse-sideˡ x) refl Fᵣ.refl ⟩
          x ⤙ y ⤚❲ Fᵣ.● ❳ ∎

  module _ {fₗ fᵣ x fℓₗ fℓᵣ xℓ} (Fₗ : Fumula fₗ fℓₗ) (Fᵣ : Fumula fᵣ fℓᵣ) where
    private
      Rₗ : Ring fₗ fℓₗ
      Rₗ = FromFumula.ring Fₗ
      Rᵣ : Ring fᵣ fℓᵣ
      Rᵣ = FromFumula.ring Fᵣ

    bimodule : DoubleFumulaExtrusion Fₗ Fᵣ x xℓ → Bimodule Rₗ Rᵣ x xℓ
    bimodule X = record { isBimodule = isBimodule Fₗ Fᵣ _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆ isDoubleFumulaExtrusion }
      where open DoubleFumulaExtrusion X

  module _ {f x fℓ xℓ} (F : ReversibleFumula f fℓ) {Carrier : Set x} (_≈_ : Rel Carrier xℓ)
           (❲_❳⤙_⤚_ : Op₃ₗ (ReversibleFumula.Carrier F) Carrier) (_⤙_⤚❲_❳ : Op₃ᵣ (ReversibleFumula.Carrier F) Carrier) (◆ : Carrier) where
    private
      R : CommutativeRing f fℓ
      R = FromFumula.commutativeRing F
      module F where
        open ReversibleFumula F public
        open FumulaProperties fumula public
      module R where
        open CommutativeRing R public
        open RingProperties ring public
        open RingHelpers ring public

      _+_ : Op₂ Carrier
      x + y = ❲ F.● ❳⤙ x ⤚ y

      0# : Carrier
      0# = ◆

      -_ : Op₁ Carrier
      - x = ❲ F.■ ❳⤙ ◆ ⤚ x

      _*ₗ_ : Opₗ R.Carrier Carrier
      s *ₗ x = ❲ s ❳⤙ ◆ ⤚ x

      _*ᵣ_ : Opᵣ R.Carrier Carrier
      x *ᵣ s = x ⤙ ◆ ⤚❲ s ❳

    isModule : IsFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆ → IsModule R _≈_ _+_ 0# -_ _*ₗ_ _*ᵣ_
    isModule X = record
      { isBimodule = iB
      ; *ₗ-*ᵣ-coincident = λ x s → outer-commute s x ◆
      }
      where
        open IsFumulaExtrusion X
        iB : IsBimodule R.ring R.ring _≈_ _+_ 0# -_ _*ₗ_ _*ᵣ_
        iB = isBimodule F.fumula F.fumula _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆ isDoubleFumulaExtrusion
        open IsBimodule iB

  module _ {f x fℓ xℓ} (F : ReversibleFumula f fℓ) where
    private
      R : CommutativeRing f fℓ
      R = FromFumula.commutativeRing F

    ‵module : FumulaExtrusion F x xℓ → Module R x xℓ
    ‵module X = record { isModule = isModule F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆ isFumulaExtrusion }
      where open FumulaExtrusion X
