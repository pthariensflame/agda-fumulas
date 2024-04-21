{-# OPTIONS --safe --cubical-compatible #-}
module Examples where
open import Function using (_∘_)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (if_then_else_; true; false)
open import Data.Nat as ℕ using (ℕ)
open import Data.Fin as Fin using (Fin)
open import Relation.Nullary using (contradiction)
open import Relation.Nullary.Decidable using (does; yes; no)
open import Relation.Binary using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Algebra.Fumula

module Matrices {c ℓ} (ScalarFumula : Fumula c ℓ) where
  open Fumula ScalarFumula renaming (Carrier to Scalar)

  Vector : ℕ → Set c
  Vector n = Fin n → Scalar

  infix 4 _≈ⱽ_
  _≈ⱽ_ : ∀{n} → Vector n → Vector n → Set ℓ
  v ≈ⱽ w = ∀ i → v i ≈ w i

  Matrix : ℕ → Set c
  Matrix n = Fin n × Fin n → Scalar

  infix 4 _≈ᴹ_
  _≈ᴹ_ : ∀{n} → Matrix n → Matrix n → Set ℓ
  A ≈ᴹ B = ∀ r,c → A r,c ≈ B r,c

  row : ∀{n} → Fin n → Matrix n → Vector n
  row r A c = A (r , c)

  column : ∀{n} → Fin n → Matrix n → Vector n
  column c A r = A (r , c)

  infixl 7 _∙⤙_⤚∙_
  _∙⤙_⤚∙_ : ∀{n} → Vector n → Scalar → Vector n → Scalar
  _∙⤙_⤚∙_ {ℕ.zero} _ x _ = x
  _∙⤙_⤚∙_ {ℕ.suc _} v x w = v Fin.zero ⤙ (v ∘ Fin.suc) ∙⤙ x ⤚∙ (w ∘ Fin.suc) ⤚ w Fin.zero

  ∙⤙⤚∙-cong : ∀{n} {v₁ v₂ : Vector n} {x₁ x₂ : Scalar} {w₁ w₂ : Vector n}
            → (∀ i → v₁ i ≈ v₂ i) → x₁ ≈ x₂ → (∀ i → w₁ i ≈ w₂ i) → v₁ ∙⤙ x₁ ⤚∙ w₁ ≈ v₂ ∙⤙ x₂ ⤚∙ w₂
  ∙⤙⤚∙-cong {ℕ.zero} _ x≈ _ = x≈
  ∙⤙⤚∙-cong {ℕ.suc _} v≈ x≈ w≈ = ⤙⤚-cong (v≈ Fin.zero) (∙⤙⤚∙-cong (v≈ ∘ Fin.suc) x≈ (w≈ ∘ Fin.suc)) (w≈ Fin.zero)

  ∙⤙⤚∙-⤙⤚-double-exchange : ∀{nₒ} (vₒ : Vector nₒ) (x z y : Scalar) (wₒ : Vector nₒ)
                          → (vₒ ∙⤙ x ⤙ z ⤚ y ⤚∙ wₒ) ≈ (x ⤙ vₒ ∙⤙ z ⤚∙ wₒ ⤚ y)
  ∙⤙⤚∙-⤙⤚-double-exchange {ℕ.zero} vₒ x z y wₒ = refl
  ∙⤙⤚∙-⤙⤚-double-exchange {ℕ.suc nₒ} vₒ x z y wₒ = begin
    (vₒ Fin.zero ⤙ (vₒ ∘ Fin.suc) ∙⤙ x ⤙ z ⤚ y ⤚∙ (wₒ ∘ Fin.suc) ⤚ wₒ Fin.zero) ≈⟨ sym (∙⤙⤚∙-⤙⤚-double-exchange (vₒ ∘ Fin.suc) (vₒ Fin.zero) (x ⤙ z ⤚ y) (wₒ Fin.zero) (wₒ ∘ Fin.suc)) ⟩
    (vₒ ∘ Fin.suc) ∙⤙ vₒ Fin.zero ⤙ x ⤙ z ⤚ y ⤚ wₒ Fin.zero ⤚∙ (wₒ ∘ Fin.suc) ≈⟨ ∙⤙⤚∙-cong {nₒ} (λ _ → refl) (double-exchange (vₒ Fin.zero) (wₒ Fin.zero) x y z) (λ _ → refl) ⟩
    (vₒ ∘ Fin.suc) ∙⤙ x ⤙ vₒ Fin.zero ⤙ z ⤚ wₒ Fin.zero ⤚ y ⤚∙ (wₒ ∘ Fin.suc) ≈⟨ ∙⤙⤚∙-⤙⤚-double-exchange (vₒ ∘ Fin.suc) x (vₒ Fin.zero ⤙ z ⤚ wₒ Fin.zero) y (wₒ ∘ Fin.suc) ⟩
    (x ⤙ (vₒ ∘ Fin.suc) ∙⤙ vₒ Fin.zero ⤙ z ⤚ wₒ Fin.zero ⤚∙ (wₒ ∘ Fin.suc) ⤚ y) ≈⟨ ⤙⤚-cong refl (∙⤙⤚∙-⤙⤚-double-exchange (vₒ ∘ Fin.suc) (vₒ Fin.zero) z (wₒ Fin.zero) (wₒ ∘ Fin.suc)) refl ⟩
    (x ⤙ vₒ Fin.zero ⤙ (vₒ ∘ Fin.suc) ∙⤙ z ⤚∙ (wₒ ∘ Fin.suc) ⤚ wₒ Fin.zero ⤚ y) ∎
    where open SetoidReasoning setoid

  ∙⤙⤚∙-double-exchange : ∀{nₒ nᵢ} (vₒ : Fin nₒ → Scalar) (vᵢ : Fin nᵢ → Scalar) (x : Scalar) (wᵢ : Fin nᵢ → Scalar) (wₒ : Fin nₒ → Scalar)
                       → (vₒ ∙⤙ vᵢ ∙⤙ x ⤚∙ wᵢ ⤚∙ wₒ) ≈ (vᵢ ∙⤙ vₒ ∙⤙ x ⤚∙ wₒ ⤚∙ wᵢ)
  ∙⤙⤚∙-double-exchange {nᵢ = ℕ.zero} _ _ _ _ _ = refl
  ∙⤙⤚∙-double-exchange {nᵢ = ℕ.suc _} vₒ vᵢ x wᵢ wₒ = begin
    vₒ ∙⤙ vᵢ Fin.zero ⤙ (vᵢ ∘ Fin.suc) ∙⤙ x ⤚∙ (wᵢ ∘ Fin.suc) ⤚ wᵢ Fin.zero ⤚∙ wₒ ≈⟨ ∙⤙⤚∙-⤙⤚-double-exchange vₒ (vᵢ Fin.zero) ((vᵢ ∘ Fin.suc) ∙⤙ x ⤚∙ (wᵢ ∘ Fin.suc)) (wᵢ Fin.zero) wₒ ⟩
    vᵢ Fin.zero ⤙ vₒ ∙⤙ (vᵢ ∘ Fin.suc) ∙⤙ x ⤚∙ (wᵢ ∘ Fin.suc) ⤚∙ wₒ ⤚ wᵢ Fin.zero ≈⟨ ⤙⤚-cong refl (∙⤙⤚∙-double-exchange vₒ (vᵢ ∘ Fin.suc) x (wᵢ ∘ Fin.suc) wₒ) refl ⟩
    (vᵢ Fin.zero ⤙ (vᵢ ∘ Fin.suc) ∙⤙ vₒ ∙⤙ x ⤚∙ wₒ ⤚∙ (wᵢ ∘ Fin.suc) ⤚ wᵢ Fin.zero) ∎
    where open SetoidReasoning setoid

  diagonal : ∀{n} → Scalar → Matrix n
  diagonal x (r , c) with r Fin.≟ c
  ... | yes _ = x
  ... | no _ = ◆

  diagonal-column≈row : ∀{n} x i (let A = diagonal {n} x) → column i A ≈ⱽ row i A
  diagonal-column≈row x i j with i Fin.≟ j
  ... | yes i=j = {!!}
  ... | no i≠j = {!!}

  _↑ᴹ : ∀{n} → Matrix n → Matrix n
  (A ↑ᴹ) (r , c) = if does (r Fin.≟ c) then A (r , c) ↑ else A (r , c)

  _↓ᴹ : ∀{n} → Matrix n → Matrix n
  (A ↓ᴹ) (r , c) = if does (r Fin.≟ c) then A (r , c) ↓ else A (r , c)

  diagonal-↑-commute : ∀ {n} x r,c → diagonal {n} (x ↑) r,c ≈ (diagonal x ↑ᴹ) r,c
  diagonal-↑-commute x (r , c) with r Fin.≟ c
  ... | yes _ = refl
  ... | no _ = refl

  _⤙ᴹ_ᴹ⤚_ : ∀{n} → Op₃ (Matrix n)
  (A ⤙ᴹ C ᴹ⤚ B) (r , c) = row r A ∙⤙ C (r , c) ⤚∙ column c B

  diagonal-outer-commute : ∀{n} e → _OuterCommutativeWith_ _≈_ _⤙_⤚_ e → _OuterCommutativeWith_ (_≈ᴹ_ {n}) _⤙ᴹ_ᴹ⤚_ (diagonal e)
  diagonal-outer-commute e e-outer-commute A B (r , c) with does (r Fin.≟ c)
  ... | true = {!!}
  ... | false = {!!}

  matrixSetoid : ℕ → Setoid c ℓ
  matrixSetoid n = record
    { Carrier = Matrix n
    ; _≈_ = _≈ᴹ_
    ; isEquivalence = record
      { refl = λ _ → refl
      ; sym = λ A≈B r,c → sym (A≈B r,c)
      ; trans = λ A≈B B≈C r,c → trans (A≈B r,c) (B≈C r,c)
      }
    }

  matrixFumula : ℕ → Fumula c ℓ
  matrixFumula n = record
    { Carrier = Matrix n
    ; _≈_ = _≈ᴹ_
    ; _⤙_⤚_ = _⤙ᴹ_ᴹ⤚_
    ; ■ = diagonal ■
    ; isFumula = record
      { isAlmostFumula = record
        { isEquivalence = Matrix.isEquivalence
        ; ⤙⤚-cong = λ {x = A₁} {y = A₂} {u = C₁} {v = C₂} {n = B₁} {m = B₂} A≈ C≈ B≈ (r , c) →
          ∙⤙⤚∙-cong (λ c′ → A≈ (r , c′)) (C≈ (r , c)) (λ r′ → B≈ (r′ , c))
        ; double-exchange = λ A B C D E (r , c) →
          ∙⤙⤚∙-double-exchange (row r A) (row r C) (E (r , c)) (column c D) (column c B)
        }
      ; ■-outer-commute = diagonal-outer-commute ■ ■-outer-commute
      ; ■-collapse-dup = (λ x r,c → {!!}) , (λ x r,c → {!!})
      ; ◆-outer-commute = λ A B → {!!}
      ; ◆-collapse-middle = (λ x z r,c → {!!}) , (λ x z r,c → {!!})
      ; ●-outer-commute = λ A B → {!!}
      ; ●-inner-commute = (λ x y r,c → {!!}) , (λ x y r,c → {!!})
      ; ●-◆-collapse-side = (λ x r,c → {!!}) , (λ x r,c → {!!})
      ; ◆-outer-associate = λ w x y z r,c → {!!}
      ; ◆-pullout = (λ v w x y z r,c → {!!}) , (λ v w x y z r,c → {!!})
      }
    }
    where
      module Matrix = Setoid (matrixSetoid n)
      open SetoidReasoning (matrixSetoid n)
