------------------------------------------------------------------------
-- Conversion of fumulas to and from rings.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.

module Algebra.Fumula.Convert where

open import Function using (id)
open import Data.Product using (_,_)
open import Relation.Binary.Structures using (IsEquivalence)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Algebra
open import Algebra.Morphism
import Algebra.Properties.Ring as RingProperties
import Algebra.Fumula.Properties as FumulaProperties
open import Algebra.Fumula.Structures
open import Algebra.Fumula.Bundles.Raw
open import Algebra.Fumula.Bundles
open import Algebra.Fumula.Morphism

module RingHelpers {c ℓ} (R : Ring c ℓ) where
  private
    module R where
      open Ring R public
      open RingProperties R public
    open SetoidReasoning R.setoid

  x*-1≈-x : ∀ x → x R.* R.- R.1# R.≈ R.- x
  x*-1≈-x x = begin
    x R.* R.- R.1# ≈⟨ R.sym (R.-‿distribʳ-* x R.1#) ⟩
    R.- (x R.* R.1#) ≈⟨ R.-‿cong (R.*-identityʳ x) ⟩
    R.- x ∎

  -1*-1≈1 : R.- R.1# R.* R.- R.1# R.≈ R.1#
  -1*-1≈1 = begin
    R.- R.1# R.* R.- R.1# ≈⟨ R.sym (R.-‿distribˡ-* R.1# (R.- R.1#)) ⟩
    R.- (R.1# R.* R.- R.1#) ≈⟨ R.-‿cong (R.sym (R.-‿distribʳ-* R.1# R.1#)) ⟩
    R.- R.- (R.1# R.* R.1#) ≈⟨ R.-‿involutive (R.1# R.* R.1#) ⟩
    R.1# R.* R.1# ≈⟨ R.*-identityˡ R.1# ⟩
    R.1# ∎

  0≈-1*-1+-1 : R.0# R.≈ R.- R.1# R.* R.- R.1# R.+ R.- R.1#
  0≈-1*-1+-1 = begin
    R.0# ≈⟨ R.sym (R.-‿inverseʳ R.1#) ⟩
    R.1# R.+ R.- R.1# ≈⟨ R.+-congʳ (R.sym -1*-1≈1) ⟩
    R.- R.1# R.* R.- R.1# R.+ R.- R.1# ∎

  1≈-1*-1+[-1*-1+-1] : R.1# R.≈ R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)
  1≈-1*-1+[-1*-1+-1] = begin
    R.1# ≈⟨ R.sym (R.+-identityʳ R.1#) ⟩
    R.1# R.+ R.0# ≈⟨ R.+-congʳ (R.sym -1*-1≈1) ⟩
    R.- R.1# R.* R.- R.1# R.+ R.0# ≈⟨ R.+-congˡ 0≈-1*-1+-1 ⟩
    R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#) ∎

module FromRing where

  rawFumula : ∀{c ℓ} → RawRing c ℓ → RawFumula c ℓ
  rawFumula rawRing = record
    { _≈_ = _≈_
    ; _⤙_⤚_ = λ x z y → x * y + z
    ; ■ = - 1#
    }
    where open RawRing rawRing

  isFumula : ∀{c ℓ} → (R : RawRing c ℓ) → IsRing (RawRing._≈_ R) (RawRing._+_ R) (RawRing._*_ R) (RawRing.-_ R) (RawRing.0# R) (RawRing.1# R)
           → (let F = rawFumula R) → IsFumula (RawFumula._≈_ F) (RawFumula._⤙_⤚_ F) (RawFumula.■ F)
  isFumula R isRing = record
    { isAlmostFumula = record
      { isEquivalence = isEquivalence
      ; ⤙⤚-cong = λ x≈y u≈v n≈m → +-cong (*-cong x≈y n≈m) u≈v
      ; double-exchange = λ v w x y z → begin
        v * w + (x * y + z) ≈⟨ sym (+-assoc (v * w) (x * y) z) ⟩
        (v * w + x * y) + z ≈⟨ +-congʳ (+-comm (v * w) (x * y)) ⟩
        (x * y + v * w) + z ≈⟨ +-assoc (x * y) (v * w) z ⟩
        x * y + (v * w + z) ∎
      }
    ; ■-outer-commute = λ x z → +-congʳ (begin
      x * - 1# ≈⟨ sym (-‿distribʳ-* x 1#) ⟩
      - (x * 1#) ≈⟨ -‿cong (*-identityʳ x) ⟩
      - x ≈⟨ -‿cong (sym (*-identityˡ x)) ⟩
      - (1# * x) ≈⟨ -‿distribˡ-* 1# x ⟩
      - 1# * x ∎)
    ; ■-collapse-dup =
      (λ x → begin
        - 1# * x + x ≈⟨ +-congʳ (-1*x≈-x x) ⟩
        - x + x ≈⟨ -‿inverseˡ x ⟩
        0# ≈⟨ sym (-‿inverseʳ 1#) ⟩
        1# + - 1# ≈⟨ +-congʳ (sym -1*-1≈1) ⟩
        - 1# * - 1# + - 1# ∎) ,
      (λ x → begin
        x * - 1# + x ≈⟨ +-congʳ (x*-1≈-x x) ⟩
        - x + x ≈⟨ -‿inverseˡ x ⟩
        0# ≈⟨ sym (-‿inverseʳ 1#) ⟩
        1# + - 1# ≈⟨ +-congʳ (sym -1*-1≈1) ⟩
        - 1# * - 1# + - 1# ∎)
    ; ◆-outer-commute = λ x z → +-congʳ (begin
      x * (- 1# * - 1# + - 1#) ≈⟨ *-congˡ (sym 0≈-1*-1+-1) ⟩
      x * 0# ≈⟨ zeroʳ x ⟩
      0# ≈⟨ sym (zeroˡ x) ⟩
      0# * x ≈⟨ *-congʳ 0≈-1*-1+-1 ⟩
      (- 1# * - 1# + - 1#) * x ∎)
    ; ◆-collapse-middle =
      (λ x z → begin
        (- 1# * - 1# + - 1#) * x + z ≈⟨ +-congʳ (*-congʳ (sym 0≈-1*-1+-1)) ⟩
        0# * x + z ≈⟨ +-congʳ (zeroˡ x) ⟩
        0# + z ≈⟨ +-identityˡ z ⟩
        z ∎) ,
      (λ x z → begin
        x * (- 1# * - 1# + - 1#) + z ≈⟨ +-congʳ (*-congˡ (sym 0≈-1*-1+-1)) ⟩
        x * 0# + z ≈⟨ +-congʳ (zeroʳ x) ⟩
        0# + z ≈⟨ +-identityˡ z ⟩
        z ∎)
    ; ●-outer-commute = λ x z → +-congʳ (begin
      x * (- 1# * - 1# + (- 1# * - 1# + - 1#)) ≈⟨ *-congˡ (sym 1≈-1*-1+[-1*-1+-1]) ⟩
      x * 1# ≈⟨ *-identityʳ x ⟩
      x ≈⟨ sym (*-identityˡ x) ⟩
      1# * x ≈⟨ *-congʳ 1≈-1*-1+[-1*-1+-1] ⟩
      (- 1# * - 1# + (- 1# * - 1# + - 1#)) * x ∎)
    ; ●-inner-commute =
      (λ x y → begin
        x * (- 1# * - 1# + (- 1# * - 1# + - 1#)) + y ≈⟨ +-congʳ (*-congˡ (sym 1≈-1*-1+[-1*-1+-1])) ⟩
        x * 1# + y ≈⟨ +-congʳ (*-identityʳ x) ⟩
        x + y ≈⟨ +-comm x y ⟩
        y + x ≈⟨ +-congʳ (sym (*-identityʳ y)) ⟩
        y * 1# + x ≈⟨ +-congʳ (*-congˡ 1≈-1*-1+[-1*-1+-1]) ⟩
        y * (- 1# * - 1# + (- 1# * - 1# + - 1#)) + x ∎) ,
      (λ x y → begin
        (- 1# * - 1# + (- 1# * - 1# + - 1#)) * y + x ≈⟨ +-congʳ (*-congʳ (sym 1≈-1*-1+[-1*-1+-1])) ⟩
        1# * y + x ≈⟨ +-congʳ (*-identityˡ y) ⟩
        y + x ≈⟨ +-comm y x ⟩
        x + y ≈⟨ +-congʳ (sym (*-identityˡ x)) ⟩
        1# * x + y ≈⟨ +-congʳ (*-congʳ 1≈-1*-1+[-1*-1+-1]) ⟩
        (- 1# * - 1# + (- 1# * - 1# + - 1#)) * x + y ∎)
    ; ●-◆-collapse-side =
      (λ x →  begin
      (- 1# * - 1# + (- 1# * - 1# + - 1#)) * x + (- 1# * - 1# + - 1#) ≈⟨ +-cong (*-congʳ (sym 1≈-1*-1+[-1*-1+-1])) (sym 0≈-1*-1+-1) ⟩
      1# * x + 0# ≈⟨ +-identityʳ (1# * x) ⟩
      1# * x ≈⟨ *-identityˡ x ⟩
      x ∎) ,
      (λ x → begin
      x * (- 1# * - 1# + (- 1# * - 1# + - 1#)) + (- 1# * - 1# + - 1#) ≈⟨ +-cong (*-congˡ (sym 1≈-1*-1+[-1*-1+-1])) (sym 0≈-1*-1+-1) ⟩
      x * 1# + 0# ≈⟨ +-identityʳ (x * 1#) ⟩
      x * 1# ≈⟨ *-identityʳ x ⟩
      x ∎)
    ; ◆-outer-associate = λ w x y z → +-congʳ (begin
      (w * x + (- 1# * - 1# + - 1#)) * y ≈⟨ *-congʳ (+-congˡ (sym 0≈-1*-1+-1)) ⟩
      (w * x + 0#) * y ≈⟨ *-congʳ (+-identityʳ (w * x)) ⟩
      (w * x) * y ≈⟨ *-assoc w x y ⟩
      w * (x * y) ≈⟨ *-congˡ (sym (+-identityʳ (x * y))) ⟩
      w * (x * y + 0#) ≈⟨ *-congˡ (+-congˡ 0≈-1*-1+-1) ⟩
      w * (x * y + (- 1# * - 1# + - 1#)) ∎)
    ; ◆-pullout =
      (λ v w x y z → begin
        (w * x + v) * y + z ≈⟨ +-congʳ (distribʳ y (w * x) v) ⟩
        ((w * x) * y + v * y) + z ≈⟨ +-assoc ((w * x) * y) (v * y) z ⟩
        (w * x) * y + (v * y + z) ≈⟨ +-congʳ (*-congʳ (sym (+-identityʳ (w * x)))) ⟩
        (w * x + 0#) * y + (v * y + z) ≈⟨ +-congʳ (*-congʳ (+-congˡ 0≈-1*-1+-1)) ⟩
        (w * x + (- 1# * - 1# + - 1#)) * y + (v * y + z) ∎) ,
      (λ v w x y z → begin
        w * (x * y + z) + v ≈⟨ +-congʳ (distribˡ w (x * y) z) ⟩
        (w * (x * y) + w * z) + v ≈⟨ +-assoc (w * (x * y)) (w * z) v ⟩
        w * (x * y) + (w * z + v) ≈⟨ +-congʳ (*-congˡ (sym (+-identityʳ (x * y)))) ⟩
        w * (x * y + 0#) + (w * z + v) ≈⟨ +-congʳ (*-congˡ (+-congˡ 0≈-1*-1+-1)) ⟩
        w * (x * y + (- 1# * - 1# + - 1#)) + (w * z + v) ∎)
    }
    where
      open RawRing R
      open IsRing isRing
      open RingProperties record { isRing = isRing }
      open RingHelpers record { isRing = isRing }
      open SetoidReasoning setoid

  fumula : ∀{c ℓ} → Ring c ℓ → Fumula c ℓ
  fumula R = record { isFumula = isFumula rawRing isRing }
    where open Ring R

  isReversibleFumula : ∀{c ℓ} → (R : RawRing c ℓ) → IsCommutativeRing (RawRing._≈_ R) (RawRing._+_ R) (RawRing._*_ R) (RawRing.-_ R) (RawRing.0# R) (RawRing.1# R)
                     → (let F = rawFumula R) → IsReversibleFumula (RawFumula._≈_ F) (RawFumula._⤙_⤚_ F) (RawFumula.■ F)
  isReversibleFumula R isCommutativeRing = record
    { isFumula = isFumula R isRing
    ; outer-commute = λ y x _ → +-congʳ (*-comm x y)
    }
    where open IsCommutativeRing isCommutativeRing

  reversibleFumula : ∀{c ℓ} → CommutativeRing c ℓ → ReversibleFumula c ℓ
  reversibleFumula R = record { isReversibleFumula = isReversibleFumula rawRing isCommutativeRing }
    where open CommutativeRing R

  isFumulaHomomorphism : ∀{c₁ ℓ₁ c₂ ℓ₂} {R₁ : RawRing c₁ ℓ₁} (R₂ : Ring c₂ ℓ₂) {morph : RawRing.Carrier R₁ → Ring.Carrier R₂} → IsRingHomomorphism R₁ (Ring.rawRing R₂) morph
                       → (let F₁ = rawFumula R₁) → (let F₂ = rawFumula (Ring.rawRing R₂)) → IsFumulaHomomorphism F₁ F₂ morph
  isFumulaHomomorphism {R₁ = R₁} R₂ {morph = morph} isRingHomomorphism = record
    { isAlmostFumulaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; homo = λ x y z → begin
        morph (x F₁.⤙ y ⤚ z) ≡⟨⟩
        morph ((x R₁.* z) R₁.+ y) ≈⟨ +-homo (x R₁.* z) y ⟩
        morph (x R₁.* z) R₂.+ morph y ≈⟨ R₂.+-congʳ (*-homo x z) ⟩
        (morph x R₂.* morph z) R₂.+ morph y ≡⟨⟩
        morph x F₂.⤙ morph y ⤚ morph z ∎
      }
    ; ■-homo = begin
        morph F₁.■ ≡⟨⟩
        morph (R₁.- R₁.1#) ≈⟨ -‿homo R₁.1# ⟩
        R₂.- (morph R₁.1#) ≈⟨ R₂.-‿cong 1#-homo ⟩
        R₂.- R₂.1# ≡⟨⟩
        F₂.■ ∎
    }
    where
      module R₁ = RawRing R₁
      module R₂ = Ring R₂
      module F₁ = RawFumula (rawFumula R₁)
      module F₂ = RawFumula (rawFumula (Ring.rawRing R₂))
      open IsRingHomomorphism isRingHomomorphism
      open SetoidReasoning R₂.setoid

  isFumulaMonomorphism : ∀{c₁ ℓ₁ c₂ ℓ₂} {R₁ : RawRing c₁ ℓ₁} (R₂ : Ring c₂ ℓ₂) {morph : RawRing.Carrier R₁ → Ring.Carrier R₂} → IsRingMonomorphism R₁ (Ring.rawRing R₂) morph
                       → (let F₁ = rawFumula R₁) → (let F₂ = rawFumula (Ring.rawRing R₂)) → IsFumulaMonomorphism F₁ F₂ morph
  isFumulaMonomorphism R₂ isRingMono = record
    { isFumulaHomomorphism = isFumulaHomomorphism R₂ isRingHomomorphism
    ; injective = injective
    }
    where open IsRingMonomorphism isRingMono

  isFumulaIsomorphism : ∀{c₁ ℓ₁ c₂ ℓ₂} {R₁ : RawRing c₁ ℓ₁} (R₂ : Ring c₂ ℓ₂) {morph : RawRing.Carrier R₁ → Ring.Carrier R₂} → IsRingIsomorphism R₁ (Ring.rawRing R₂) morph
                       → (let F₁ = rawFumula R₁) → (let F₂ = rawFumula (Ring.rawRing R₂)) → IsFumulaIsomorphism F₁ F₂ morph
  isFumulaIsomorphism R₂ isRingIso = record
    { isFumulaMonomorphism = isFumulaMonomorphism R₂ isRingMonomorphism
    ; surjective = surjective
    }
    where open IsRingIsomorphism isRingIso

module FromFumula where

  rawRing : ∀{c ℓ} → RawFumula c ℓ → RawRing c ℓ
  rawRing rawFumula = record
    { _≈_ = _≈_
    ; _+_ = λ x y → ● ⤙ x ⤚ y
    ; _*_ = λ x y → x ⤙ ◆ ⤚ y
    ; -_ = invert
    ; 0# = ◆
    ; 1# = ●
    }
    where open RawFumula rawFumula

  isRing : ∀{c ℓ} → (F : RawFumula c ℓ) → IsFumula (RawFumula._≈_ F) (RawFumula._⤙_⤚_ F) (RawFumula.■ F)
         → (let R = rawRing F) → IsRing (RawRing._≈_ R) (RawRing._+_ R) (RawRing._*_ R) (RawRing.-_ R) (RawRing.0# R) (RawRing.1# R)
  isRing F isFumula = record
    { +-isAbelianGroup = record
      { isGroup = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence
              ; ∙-cong = λ x≈y u≈v → ⤙⤚-cong refl x≈y u≈v
              }
            ; assoc = λ x y z → begin
              ● ⤙ ● ⤙ x ⤚ y ⤚ z ≈⟨ ⤙⤚-cong refl (●-inner-commuteʳ x y) refl ⟩
              ● ⤙ ● ⤙ y ⤚ x ⤚ z ≈⟨ ⤙⤚-cong refl (sym (●-outer-commute x y)) refl ⟩
              ● ⤙ x ⤙ y ⤚ ● ⤚ z ≈⟨ double-exchange ● z x ● y ⟩
              x ⤙ ● ⤙ y ⤚ z ⤚ ● ≈⟨ ●-inner-commuteˡ x (● ⤙ y ⤚ z) ⟩
              (● ⤙ y ⤚ z) ⤙ x ⤚ ● ≈⟨ ●-outer-commute (● ⤙ y ⤚ z) x ⟩
              ● ⤙ x ⤚ (● ⤙ y ⤚ z) ∎
            }
          ; identity = ●-◆-collapse-sideˡ , λ x → begin
            ● ⤙ x ⤚ ◆ ≈⟨ ●-inner-commuteʳ x ◆ ⟩
            ● ⤙ ◆ ⤚ x ≈⟨ ●-◆-collapse-sideˡ x ⟩
            x ∎
          }
        ; inverse =
          (λ x → begin
            ● ⤙ ■ ⤙ ◆ ⤚ x ⤚ x ≈⟨ double-exchange ● x ■ x ◆ ⟩
            ■ ⤙ ● ⤙ ◆ ⤚ x ⤚ x ≈⟨ ⤙⤚-cong refl (●-◆-collapse-sideˡ x) refl ⟩
            ■ ⤙ x ⤚ x ≈⟨ ■-collapse-dupˡ x ⟩
            ◆ ∎) ,
          (λ x → begin
            ● ⤙ x ⤚ (■ ⤙ ◆ ⤚ x) ≈⟨ ●-inner-commuteʳ x (■ ⤙ ◆ ⤚ x) ⟩
            ● ⤙ ■ ⤙ ◆ ⤚ x ⤚ x ≈⟨ double-exchange ● x ■ x ◆ ⟩
            ■ ⤙ ● ⤙ ◆ ⤚ x ⤚ x ≈⟨ ⤙⤚-cong refl (●-◆-collapse-sideˡ x) refl ⟩
            ■ ⤙ x ⤚ x ≈⟨ ■-collapse-dupˡ x ⟩
            ◆ ∎)
        ; ⁻¹-cong = invert-cong
        }
      ; comm = ●-inner-commuteʳ
      }
    ; *-cong = λ x≈y u≈v → ⤙⤚-cong x≈y refl u≈v
    ; *-assoc = λ x y z → ◆-outer-associate x y z ◆
    ; *-identity = ●-◆-collapse-sideˡ , ●-◆-collapse-sideʳ
    ; distrib =
      (λ x y z → begin
        x ⤙ ◆ ⤚ (● ⤙ y ⤚ z) ≈⟨ ◆-pulloutʳ ◆ x ● z y ⟩
        x ⤙ x ⤙ ◆ ⤚ y ⤚ (● ⤙ ◆ ⤚ z) ≈⟨ ⤙⤚-cong refl refl (●-◆-collapse-sideˡ z) ⟩
        (x ⤙ x ⤙ ◆ ⤚ y ⤚ z) ≈⟨ sym (●-◆-pull-apartʳ x z (x ⤙ ◆ ⤚ y)) ⟩
        ● ⤙ x ⤙ ◆ ⤚ y ⤚ (x ⤙ ◆ ⤚ z) ∎) ,
      (λ x y z → begin
        (● ⤙ y ⤚ z) ⤙ ◆ ⤚ x ≈⟨ ◆-pulloutˡ y ● z x ◆ ⟩
        (● ⤙ ◆ ⤚ z) ⤙ y ⤙ ◆ ⤚ x ⤚ x ≈⟨ ⤙⤚-cong (●-◆-collapse-sideˡ z) refl refl ⟩
        (z ⤙ y ⤙ ◆ ⤚ x ⤚ x) ≈⟨ sym (●-◆-pull-apartʳ z x (y ⤙ ◆ ⤚ x)) ⟩
        ● ⤙ y ⤙ ◆ ⤚ x ⤚ (z ⤙ ◆ ⤚ x) ∎)
    }
    where
      open RawFumula F
      open IsFumula isFumula
      open FumulaProperties record { isFumula = isFumula }
      open SetoidReasoning setoid

  ring : ∀{c ℓ} → Fumula c ℓ → Ring c ℓ
  ring F = record { isRing = isRing rawFumula isFumula }
    where open Fumula F

  isCommutativeRing : ∀{c ℓ} → (F : RawFumula c ℓ) → IsReversibleFumula (RawFumula._≈_ F) (RawFumula._⤙_⤚_ F) (RawFumula.■ F)
                    → (let R = rawRing F) → IsCommutativeRing (RawRing._≈_ R) (RawRing._+_ R) (RawRing._*_ R) (RawRing.-_ R) (RawRing.0# R) (RawRing.1# R)
  isCommutativeRing F isReversibleFumula = record
    { isRing = isRing F isFumula
    ; *-comm = λ x y → outer-commute y x (RawFumula.◆ F)
    }
    where open IsReversibleFumula isReversibleFumula

  commutativeRing : ∀{c ℓ} → ReversibleFumula c ℓ → CommutativeRing c ℓ
  commutativeRing F = record { isCommutativeRing = isCommutativeRing rawFumula isReversibleFumula }
    where open ReversibleFumula F

  isRingHomomorphism : ∀{c₁ ℓ₁ c₂ ℓ₂} {F₁ : RawFumula c₁ ℓ₁} (F₂ : Fumula c₂ ℓ₂) {morph : RawFumula.Carrier F₁ → Fumula.Carrier F₂} → IsFumulaHomomorphism F₁ (Fumula.rawFumula F₂) morph
                       → (let R₁ = rawRing F₁) → (let R₂ = rawRing (Fumula.rawFumula F₂)) → IsRingHomomorphism R₁ R₂ morph
  isRingHomomorphism {F₁ = F₁} F₂ {morph = morph} isFumulaHomomorphism = record
    { isSemiringHomomorphism = record
      { isNearSemiringHomomorphism = record
        { +-isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = isRelHomomorphism
            ; homo = λ x y → begin
              morph (x R₁.+ y) ≡⟨⟩
              morph (F₁.● F₁.⤙ x ⤚ y) ≈⟨ ⤙⤚-homo F₁.● x y ⟩
              morph F₁.● F₂.⤙ morph x ⤚ morph y ≈⟨ F₂.⤙⤚-cong ●-homo F₂.refl F₂.refl ⟩
              F₂.● F₂.⤙ morph x ⤚ morph y ≡⟨⟩
              morph x R₂.+ morph y ∎
            }
          ; ε-homo = ◆-homo
          }
        ; *-homo = λ x y → begin
          morph (x R₁.* y) ≡⟨⟩
          morph (x F₁.⤙ F₁.◆ ⤚ y) ≈⟨ ⤙⤚-homo x F₁.◆ y ⟩
          morph x F₂.⤙ morph F₁.◆ ⤚ morph y ≈⟨ F₂.⤙⤚-cong F₂.refl ◆-homo F₂.refl ⟩
          morph x F₂.⤙ F₂.◆ ⤚ morph y ≡⟨⟩
          morph x R₂.* morph y ∎
        }
      ; 1#-homo = ●-homo
      }
    ; -‿homo = λ x → begin
      morph (R₁.- x) ≡⟨⟩
      morph (F₁.■ F₁.⤙ F₁.◆ ⤚ x) ≈⟨ ⤙⤚-homo F₁.■ F₁.◆ x ⟩
      morph F₁.■ F₂.⤙ morph F₁.◆ ⤚ morph x ≈⟨ F₂.⤙⤚-cong ■-homo ◆-homo F₂.refl ⟩
      F₂.■ F₂.⤙ F₂.◆ ⤚ morph x ≡⟨⟩
      R₂.- morph x ∎
    }
    where
      module F₁ = RawFumula F₁
      module F₂ = Fumula F₂
      module R₁ = RawRing (rawRing F₁)
      module R₂ = RawRing (rawRing (Fumula.rawFumula F₂))
      open IsFumulaHomomorphism isFumulaHomomorphism
      open SetoidReasoning F₂.setoid

      ◆-homo : morph F₁.◆ F₂.≈ F₂.◆
      ◆-homo = begin
        morph F₁.◆ ≡⟨⟩
        morph (F₁.■ F₁.⤙ F₁.■ ⤚ F₁.■) ≈⟨ ⤙⤚-homo F₁.■ F₁.■ F₁.■ ⟩
        morph F₁.■ F₂.⤙ morph F₁.■ ⤚ morph F₁.■ ≈⟨ F₂.⤙⤚-cong ■-homo ■-homo ■-homo ⟩
        F₂.■ F₂.⤙ F₂.■ ⤚ F₂.■ ≡⟨⟩
        F₂.◆ ∎

      ●-homo : morph F₁.● F₂.≈ F₂.●
      ●-homo = begin
        morph F₁.● ≡⟨⟩
        morph (F₁.■ F₁.⤙ F₁.◆ ⤚ F₁.■) ≈⟨ ⤙⤚-homo F₁.■ F₁.◆ F₁.■ ⟩
        morph F₁.■ F₂.⤙ morph F₁.◆ ⤚ morph F₁.■ ≈⟨ F₂.⤙⤚-cong ■-homo ◆-homo ■-homo ⟩
        F₂.■ F₂.⤙ F₂.◆ ⤚ F₂.■ ≡⟨⟩
        F₂.● ∎

  isRingMonomorphism : ∀{c₁ ℓ₁ c₂ ℓ₂} {F₁ : RawFumula c₁ ℓ₁} (F₂ : Fumula c₂ ℓ₂) {morph : RawFumula.Carrier F₁ → Fumula.Carrier F₂} → IsFumulaMonomorphism F₁ (Fumula.rawFumula F₂) morph
                       → (let R₁ = rawRing F₁) → (let R₂ = rawRing (Fumula.rawFumula F₂)) → IsRingMonomorphism R₁ R₂ morph
  isRingMonomorphism F₂ isFumulaMono = record
    { isRingHomomorphism = isRingHomomorphism F₂ isFumulaHomomorphism
    ; injective = injective
    }
    where open IsFumulaMonomorphism isFumulaMono

  isRingIsomorphism : ∀{c₁ ℓ₁ c₂ ℓ₂} {F₁ : RawFumula c₁ ℓ₁} (F₂ : Fumula c₂ ℓ₂) {morph : RawFumula.Carrier F₁ → Fumula.Carrier F₂} → IsFumulaIsomorphism F₁ (Fumula.rawFumula F₂) morph
                       → (let R₁ = rawRing F₁) → (let R₂ = rawRing (Fumula.rawFumula F₂)) → IsRingIsomorphism R₁ R₂ morph
  isRingIsomorphism F₂ isFumulaIso = record
    { isRingMonomorphism = isRingMonomorphism F₂ isFumulaMonomorphism
    ; surjective = surjective
    }
    where open IsFumulaIsomorphism isFumulaIso

module _ {c ℓ} (R : Ring c ℓ) where
  private
    F = FromRing.fumula R
    R̂ = FromFumula.ring F
    module R where
      open Ring R public
      open RingProperties R public
      open RingHelpers R public
    module F = Fumula F
    module R̂ = Ring R̂
    open SetoidReasoning R.setoid

  ring↔fumula : IsRingIsomorphism R.rawRing R̂.rawRing id
  ring↔fumula = record
    { isRingMonomorphism = record
      { isRingHomomorphism = record
        { isSemiringHomomorphism = record
          { isNearSemiringHomomorphism = record
            { +-isMonoidHomomorphism = record
              { isMagmaHomomorphism = record
                { isRelHomomorphism = record
                  { cong = id
                  }
                ; homo = λ x y → begin
                  x R.+ y ≈⟨ R.+-comm x y ⟩
                  y R.+ x ≈⟨ R.+-congʳ (R.sym (R.*-identityˡ y)) ⟩
                  R.1# R.* y R.+ x ≈⟨ R.+-congʳ (R.*-congʳ R.1≈-1*-1+[-1*-1+-1]) ⟩
                  ((R.- R.1# R.* R.- R.1# R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#)) R.* y R.+ x) ∎
                }
              ; ε-homo = R.0≈-1*-1+-1
              }
            ; *-homo = λ x y → begin
                x R.* y ≈⟨ R.sym (R.+-identityʳ (x R.* y)) ⟩
                (x R.* y R.+ R.0#) ≈⟨ R.+-congˡ R.0≈-1*-1+-1 ⟩
                x R.* y R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#) ∎
            }
          ; 1#-homo = R.1≈-1*-1+[-1*-1+-1]
          }
        ; -‿homo = λ x → begin
            R.- x ≈⟨ R.sym (R.-1*x≈-x x) ⟩
            (R.- R.1# R.* x) ≈⟨ R.sym (R.+-identityʳ (R.- R.1# R.* x)) ⟩
            (R.- R.1# R.* x R.+ R.0#) ≈⟨ R.+-congˡ R.0≈-1*-1+-1 ⟩
            R.- R.1# R.* x R.+ (R.- R.1# R.* R.- R.1# R.+ R.- R.1#) ∎
        }
      ; injective = id
      }
    ; surjective = λ y → y , id
    }

module _ {c ℓ} (F : Fumula c ℓ) where
  private
    R = FromFumula.ring F
    F̂ = FromRing.fumula R
    module F where
      open Fumula F public
      open FumulaProperties F public
    module R = Ring R
    module F̂ = Fumula F̂
    open SetoidReasoning F.setoid

  fumula↔ring : IsFumulaIsomorphism F.rawFumula F̂.rawFumula id
  fumula↔ring = record
    { isFumulaMonomorphism = record
      { isFumulaHomomorphism = record
        { isAlmostFumulaHomomorphism = record
          { isRelHomomorphism = record
            { cong = id
            }
          ; homo = λ x y z → begin
            x F.⤙ y ⤚ z ≈⟨ F.sym (F.●-◆-pull-apartʳ x z y) ⟩
            F.● F.⤙ y ⤚ (x F.⤙ F.◆ ⤚ z) ≈⟨ F.●-inner-commuteʳ y (x F.⤙ F.◆ ⤚ z) ⟩
            F.● F.⤙ x F.⤙ F.◆ ⤚ z ⤚ y ∎
          }
        ; ■-homo = F.sym (F.●-◆-collapse-sideʳ F.■)
        }
      ; injective = id
      }
    ; surjective = λ y → y , id
    }
