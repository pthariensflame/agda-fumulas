------------------------------------------------------------------------
-- Additional properties of fumulas.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.

open import Algebra.Fumula.Bundles using (Fumula)

module Algebra.Fumula.Properties {c ℓ} (F : Fumula c ℓ) where

open import Function.Definitions using (Inverseˡ; Inverseʳ; Inverseᵇ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Integer.Base using (+_; -[1+_]; -1ℤ; 0ℤ; 1ℤ; _+_; _-_)
open Fumula F
open import Algebra.Definitions _≈_ using (Involutive)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (cong to ≡-cong)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Fumula.Definitions _≈_ _⤙_⤚_ using (OuterCommutativeWith)
open import Algebra.Fumula.Properties.Raw rawFumula public

------------------------------------------------------------------------
-- The "side collapse" property: the "missing" collapse form,
-- derivable from the other axioms.
------------------------------------------------------------------------

●-◆-collapse-sideˡ : ∀ x → (● ⤙ ◆ ⤚ x) ≈ x
●-◆-collapse-sideˡ x = begin
  ● ⤙ ◆ ⤚ x ≈⟨ ●-inner-commuteʳ ◆ x ⟩
  ● ⤙ x ⤚ ◆ ≈⟨ ◆-collapse-middleʳ ● x ⟩
  x ∎

●-◆-collapse-sideʳ : ∀ x → (x ⤙ ◆ ⤚ ●) ≈ x
●-◆-collapse-sideʳ x = begin
  x ⤙ ◆ ⤚ ● ≈⟨ ●-inner-commuteˡ x ◆ ⟩
  ◆ ⤙ x ⤚ ● ≈⟨ ◆-collapse-middleˡ ● x ⟩
  x ∎

●-◆-collapse-side : (∀ x → (● ⤙ ◆ ⤚ x) ≈ x) × (∀ x → (x ⤙ ◆ ⤚ ●) ≈ x)
●-◆-collapse-side = ●-◆-collapse-sideˡ , ●-◆-collapse-sideʳ

------------------------------------------------------------------------
-- The "pull apart" property: a way of separating the two ring
-- operators from within a fumula, or of melding them again.
------------------------------------------------------------------------

●-◆-pull-apartˡ : ∀ x y z → (x ⤙ ◆ ⤚ y) ⤙ z ⤚ ● ≈ x ⤙ z ⤚ y
●-◆-pull-apartˡ x y z = begin
  (x ⤙ ◆ ⤚ y) ⤙ z ⤚ ● ≈⟨ ◆-outer-associate x y ● z ⟩
  x ⤙ z ⤚ (y ⤙ ◆ ⤚ ●) ≈⟨ ⤙⤚-cong refl refl (●-◆-collapse-sideʳ y) ⟩
  x ⤙ z ⤚ y ∎

●-◆-pull-apartʳ : ∀ x y z → ● ⤙ z ⤚ (x ⤙ ◆ ⤚ y) ≈ x ⤙ z ⤚ y
●-◆-pull-apartʳ x y z = begin
  ● ⤙ z ⤚ (x ⤙ ◆ ⤚ y) ≈⟨ sym (◆-outer-associate ● x y z) ⟩
  (● ⤙ ◆ ⤚ x) ⤙ z ⤚ y ≈⟨ ⤙⤚-cong (●-◆-collapse-sideˡ x) refl refl ⟩
  x ⤙ z ⤚ y ∎

●-◆-pull-apart : (∀ x y z → (x ⤙ ◆ ⤚ y) ⤙ z ⤚ ● ≈ x ⤙ z ⤚ y) × (∀ x y z → ● ⤙ z ⤚ (x ⤙ ◆ ⤚ y) ≈ x ⤙ z ⤚ y)
●-◆-pull-apart = ●-◆-pull-apartˡ , ●-◆-pull-apartʳ

------------------------------------------------------------------------
-- Properties of the successor and predecessor operations.
------------------------------------------------------------------------

↓-↑≈↑-↓ : ∀ x → x ↑ ↓ ≈ x ↓ ↑
↓-↑≈↑-↓ x = begin
  x ↑ ↓ ≡⟨⟩
  ■ ⤙ ■ ⤙ x ⤚ ■ ⤚ ● ≈⟨ double-exchange ■ ● ■ ■ x ⟩
  ■ ⤙ ■ ⤙ x ⤚ ● ⤚ ■ ≡⟨⟩
  x ↓ ↑ ∎

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
  x ↑ ↓ ≈⟨ ↓-↑≈↑-↓ x ⟩
  x ↓ ↑ ≈⟨ ↑-↓-inverseˡ refl ⟩
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

↑-⤙⤚-●-dup-nestˡ : ∀ x y z → x ↑ ⤙ z ⤚ y ≈ x ⤙ ● ⤙ z ⤚ y ⤚ y
↑-⤙⤚-●-dup-nestˡ x y z = begin
  x ↑ ⤙ z ⤚ y ≈⟨ ◆-pulloutˡ x ■ ■ y z ⟩
  ● ⤙ x ⤙ z ⤚ y ⤚ y ≈⟨ double-exchange ● y x y z ⟩
  x ⤙ ● ⤙ z ⤚ y ⤚ y ∎

↑-⤙⤚-●-dup-nestʳ : ∀ x y z → x ⤙ z ⤚ y ↑ ≈ x ⤙ x ⤙ z ⤚ ● ⤚ y
↑-⤙⤚-●-dup-nestʳ x y z = begin
  x ⤙ z ⤚ y ↑ ≈⟨ ◆-pulloutʳ z x ■ ■ y ⟩
  x ⤙ x ⤙ z ⤚ y ⤚ ● ≈⟨ double-exchange x ● x y z ⟩
  x ⤙ x ⤙ z ⤚ ● ⤚ y ∎

↑-⤙⤚-●-dup-nest : (∀ x y z → x ↑ ⤙ z ⤚ y ≈ x ⤙ ● ⤙ z ⤚ y ⤚ y) × (∀ x y z → x ⤙ z ⤚ y ↑ ≈ x ⤙ x ⤙ z ⤚ ● ⤚ y)
↑-⤙⤚-●-dup-nest = ↑-⤙⤚-●-dup-nestˡ , ↑-⤙⤚-●-dup-nestʳ

↓-⤙⤚-■-dup-nestˡ : ∀ x y z → x ↓ ⤙ z ⤚ y ≈ x ⤙ ■ ⤙ z ⤚ y ⤚ y
↓-⤙⤚-■-dup-nestˡ x y z = begin
  x ↓ ⤙ z ⤚ y ≈⟨ ◆-pulloutˡ x ■ ● y z ⟩
  (■ ⤙ ◆ ⤚ ●) ⤙ x ⤙ z ⤚ y ⤚ y ≈⟨ ⤙⤚-cong (●-◆-collapse-sideʳ ■) refl refl ⟩
  ■ ⤙ x ⤙ z ⤚ y ⤚ y ≈⟨ double-exchange ■ y x y z ⟩
  x ⤙ ■ ⤙ z ⤚ y ⤚ y ∎

↓-⤙⤚-■-dup-nestʳ : ∀ x y z → x ⤙ z ⤚ y ↓ ≈ x ⤙ x ⤙ z ⤚ ■ ⤚ y
↓-⤙⤚-■-dup-nestʳ x y z = begin
  x ⤙ z ⤚ y ↓ ≈⟨ ◆-pulloutʳ z x ■ ● y ⟩
  x ⤙ x ⤙ z ⤚ y ⤚ (■ ⤙ ◆ ⤚ ●) ≈⟨ ⤙⤚-cong refl refl (●-◆-collapse-sideʳ ■) ⟩
  x ⤙ x ⤙ z ⤚ y ⤚ ■ ≈⟨ double-exchange x ■ x y z ⟩
  x ⤙ x ⤙ z ⤚ ■ ⤚ y ∎

↓-⤙⤚-■-dup-nest : (∀ x y z → x ↓ ⤙ z ⤚ y ≈ x ⤙ ■ ⤙ z ⤚ y ⤚ y) × (∀ x y z → x ⤙ z ⤚ y ↓ ≈ x ⤙ x ⤙ z ⤚ ■ ⤚ y)
↓-⤙⤚-■-dup-nest = ↓-⤙⤚-■-dup-nestˡ , ↓-⤙⤚-■-dup-nestʳ

------------------------------------------------------------------------
-- Properties of the invert operation.
------------------------------------------------------------------------

invert-involutive : Involutive invert
invert-involutive x = begin
  invert (invert x) ≡⟨⟩
  ■ ⤙ ◆ ⤚ (■ ⤙ ◆ ⤚ x) ≈⟨ sym (◆-outer-associate ■ ■ x ◆) ⟩
  ● ⤙ ◆ ⤚ x ≈⟨ ●-◆-collapse-sideˡ x ⟩
  x ∎

invert-↑≈↓-invert : ∀ x → invert (x ↑) ≈ invert x ↓
invert-↑≈↓-invert x = begin
  invert (x ↑) ≡⟨⟩
  ■ ⤙ ◆ ⤚ (■ ⤙ x ⤚ ■) ≈⟨ ◆-pulloutʳ ◆ ■ ■ ■ x ⟩
  ■ ⤙ ■ ⤙ ◆ ⤚ x ⤚ ● ≡⟨⟩
  invert x ↓ ∎

invert-↓≈↑-invert : ∀ x → invert (x ↓) ≈ invert x ↑
invert-↓≈↑-invert x = begin
  invert (x ↓) ≡⟨⟩
  ■ ⤙ ◆ ⤚ (■ ⤙ x ⤚ ●) ≈⟨ ◆-pulloutʳ ◆ ■ ■ ● x ⟩
  ■ ⤙ ■ ⤙ ◆ ⤚ x ⤚ (■ ⤙ ◆ ⤚ ●) ≈⟨ ⤙⤚-cong refl refl (●-◆-collapse-sideʳ ■) ⟩
  ■ ⤙ ■ ⤙ ◆ ⤚ x ⤚ ■ ≡⟨⟩
  invert x ↑ ∎

------------------------------------------------------------------------
-- Properties of a fumula's heartline
------------------------------------------------------------------------

heartline-cong : ∀{i j} → i ≡ j → heartline i ≈ heartline j
heartline-cong i≡j = reflexive (≡-cong heartline i≡j)

heartline‿-1≈■ : heartline -1ℤ ≈ ■
heartline‿-1≈■ = refl

heartline-0≈◆ : heartline 0ℤ ≈ ◆
heartline-0≈◆ = refl

heartline-1≈● : heartline 1ℤ ≈ ●
heartline-1≈● = refl

heartline∘[+1]≈↑∘heartline : ∀ i → heartline (i + 1ℤ) ≈ heartline i ↑
heartline∘[+1]≈↑∘heartline (+ zero) = refl
heartline∘[+1]≈↑∘heartline (+ suc n) = ↑-cong (heartline∘[+1]≈↑∘heartline (+ n))
heartline∘[+1]≈↑∘heartline -[1+ zero ] = refl
heartline∘[+1]≈↑∘heartline -[1+ suc n ] = sym (↑-↓-inverseˡ refl)

heartline∘[-1]≈↓∘heartline : ∀ i → heartline (i - 1ℤ) ≈ heartline i ↓
heartline∘[-1]≈↓∘heartline (+ zero) = sym (↑-↓-inverseʳ refl)
heartline∘[-1]≈↓∘heartline (+ suc n) = sym (↑-↓-inverseʳ refl)
heartline∘[-1]≈↓∘heartline -[1+ zero ] = refl
heartline∘[-1]≈↓∘heartline -[1+ suc n ] = ↓-cong (↓-cong (heartline-cong (≡-cong -[1+_] (+-comm n zero))))

heartline-outer-commute : ∀ i → OuterCommutativeWith (heartline i)
heartline-outer-commute (+ zero) = ◆-outer-commute
heartline-outer-commute (+ suc n) x z = begin
  x ⤙ z ⤚ heartline (+ n) ↑ ≈⟨ ◆-pulloutʳ z x ■ ■ (heartline (+ n)) ⟩
  x ⤙ x ⤙ z ⤚ heartline (+ n) ⤚ ● ≈⟨ ●-outer-commute x (x ⤙ z ⤚ heartline (+ n)) ⟩
  ● ⤙ x ⤙ z ⤚ heartline (+ n) ⤚ x ≈⟨ ⤙⤚-cong refl (heartline-outer-commute (+ n) x z) refl ⟩
  ● ⤙ heartline (+ n) ⤙ z ⤚ x ⤚ x ≈⟨ ◆-pulloutˡ (heartline (+ n)) ■ ■ x z ⟨
  heartline (+ n) ↑ ⤙ z ⤚ x ∎
heartline-outer-commute -[1+ zero ] = ■-outer-commute
heartline-outer-commute -[1+ suc n ] x z = begin
  x ⤙ z ⤚ heartline -[1+ n ] ↓ ≈⟨ ◆-pulloutʳ z x ■ ● (heartline -[1+ n ]) ⟩
  x ⤙ x ⤙ z ⤚ heartline -[1+ n ] ⤚ (■ ⤙ ◆ ⤚ ●) ≈⟨ ⤙⤚-cong refl refl (↑-↓-inverseʳ refl) ⟩
  x ⤙ x ⤙ z ⤚ heartline -[1+ n ] ⤚ ■ ≈⟨ ■-outer-commute x (x ⤙ z ⤚ heartline -[1+ n ]) ⟩
  ■ ⤙ x ⤙ z ⤚ heartline -[1+ n ] ⤚ x ≈⟨ ⤙⤚-cong (↑-↓-inverseʳ refl) refl refl ⟨
  (■ ⤙ ◆ ⤚ ●) ⤙ x ⤙ z ⤚ heartline -[1+ n ] ⤚ x ≈⟨ ⤙⤚-cong refl (heartline-outer-commute -[1+ n ] x z) refl ⟩
  (■ ⤙ ◆ ⤚ ●) ⤙ heartline -[1+ n ] ⤙ z ⤚ x ⤚ x ≈⟨ ◆-pulloutˡ (heartline -[1+ n ]) ■ (■ ⤙ ■ ⤙ ■ ⤚ ■ ⤚ ■) x z ⟨
  heartline -[1+ n ] ↓ ⤙ z ⤚ x ∎
