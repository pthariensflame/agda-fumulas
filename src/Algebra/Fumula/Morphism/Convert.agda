------------------------------------------------------------------------
-- Conversions between fumula and ring morphisms.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.
module Algebra.Fumula.Morphism.Convert where
open import Algebra.Bundles using (RawRing; Ring)
open import Algebra.Morphism using (IsRingHomomorphism; IsRingMonomorphism; IsRingIsomorphism)
open import Algebra.Fumula.Bundles using (RawFumula; Fumula)
open import Algebra.Fumula.Morphism using (IsFumulaHomomorphism; IsFumulaMonomorphism; IsFumulaIsomorphism)
open import Algebra.Fumula.Convert using (module FromRing; module FromFumula)

module FromRingMorphism {ac bc ae be} {Rᵃ : RawRing ac ae} (Rᵇ : Ring bc be)
                        {⟦_⟧ : RawRing.Carrier Rᵃ → Ring.Carrier Rᵇ} where

  isFumulaHomomorphism : IsRingHomomorphism Rᵃ (Ring.rawRing Rᵇ) ⟦_⟧ →
    IsFumulaHomomorphism (FromRing.rawFumula Rᵃ) (FromRing.rawFumula (Ring.rawRing Rᵇ)) ⟦_⟧
  isFumulaHomomorphism ⟦⟧-isRingHomo = record
    { isAlmostFumulaHomomorphism = record
      { isRelHomomorphism = isRelHomomorphism
      ; homo = λ x y z → trans (+-homo (x * z) y) (+-congʳ (*-homo x z))
      }
    ; ■-homo = trans (-‿homo 1#) (-‿cong 1#-homo)
    }
    where
      open IsRingHomomorphism ⟦⟧-isRingHomo
      open RawRing Rᵃ using (1#; _*_)
      open Ring Rᵇ using (trans; -‿cong; +-congʳ; *-cong)

  isFumulaMonomorphism : IsRingMonomorphism Rᵃ (Ring.rawRing Rᵇ) ⟦_⟧ →
    IsFumulaMonomorphism (FromRing.rawFumula Rᵃ) (FromRing.rawFumula (Ring.rawRing Rᵇ)) ⟦_⟧
  isFumulaMonomorphism ⟦⟧-isRingMono = record
    { isFumulaHomomorphism = isFumulaHomomorphism isRingHomomorphism
    ; injective = injective
    }
    where
      open IsRingMonomorphism ⟦⟧-isRingMono

  isFumulaIsomorphism : IsRingIsomorphism Rᵃ (Ring.rawRing Rᵇ) ⟦_⟧ →
    IsFumulaIsomorphism (FromRing.rawFumula Rᵃ) (FromRing.rawFumula (Ring.rawRing Rᵇ)) ⟦_⟧
  isFumulaIsomorphism ⟦⟧-isRingIso = record
    { isFumulaMonomorphism = isFumulaMonomorphism isRingMonomorphism
    ; surjective = surjective
    }
    where
      open IsRingIsomorphism ⟦⟧-isRingIso

module FromFumulaMorphism {ac bc ae be} {Fᵃ : RawFumula ac ae} (Fᵇ : Fumula bc be)
                          {⟦_⟧ : RawFumula.Carrier Fᵃ → Fumula.Carrier Fᵇ} where

  isRingHomomorphism : IsFumulaHomomorphism Fᵃ (Fumula.rawFumula Fᵇ) ⟦_⟧ →
    IsRingHomomorphism (FromFumula.rawRing Fᵃ) (FromFumula.rawRing (Fumula.rawFumula Fᵇ)) ⟦_⟧
  isRingHomomorphism ⟦⟧-isFumulaHomo = record
    { isSemiringHomomorphism = record
      { isNearSemiringHomomorphism = record
        { +-isMonoidHomomorphism = record
          { isMagmaHomomorphism = record
            { isRelHomomorphism = isRelHomomorphism
            ; homo = λ x y → trans (⤙⤚-homo Fᵃ.● x y) (⤙⤚-cong ●-homo refl refl)
            }
          ; ε-homo = ◆-homo
          }
        ; *-homo = λ x y → trans (⤙⤚-homo x Fᵃ.◆ y) (⤙⤚-cong refl ◆-homo refl)
        }
      ; 1#-homo = ●-homo
      }
    ; -‿homo = λ x → trans (⤙⤚-homo ■ Fᵃ.◆ x) (⤙⤚-cong ■-homo ◆-homo refl)
    }
    where
      open IsFumulaHomomorphism ⟦⟧-isFumulaHomo
      open module Fᵃ = RawFumula Fᵃ using (■)
      open module Fᵇ = Fumula Fᵇ using (_≈_; trans; refl; ⤙⤚-cong)
      open HeartlineHomo Fᵇ.isFumula
 
  isRingMonomorphism : IsFumulaMonomorphism Fᵃ (Fumula.rawFumula Fᵇ) ⟦_⟧ →
    IsRingMonomorphism (FromFumula.rawRing Fᵃ) (FromFumula.rawRing (Fumula.rawFumula Fᵇ)) ⟦_⟧
  isRingMonomorphism ⟦⟧-isFumulaMono = record
    { isRingHomomorphism = isRingHomomorphism isFumulaHomomorphism
    ; injective = injective
    }
    where
      open IsFumulaMonomorphism ⟦⟧-isFumulaMono
 
  isRingIsomorphism : IsFumulaIsomorphism Fᵃ (Fumula.rawFumula Fᵇ) ⟦_⟧ →
    IsRingIsomorphism (FromFumula.rawRing Fᵃ) (FromFumula.rawRing (Fumula.rawFumula Fᵇ)) ⟦_⟧
  isRingIsomorphism ⟦⟧-isFumulaIso = record
    { isRingMonomorphism = isRingMonomorphism isFumulaMonomorphism
    ; surjective = surjective
    }
    where
      open IsFumulaIsomorphism ⟦⟧-isFumulaIso
