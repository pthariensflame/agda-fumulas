------------------------------------------------------------------------
-- Additional properties of fumulas.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula`.

open import Algebra.Fumula.Bundles using (Fumula)

module Algebra.Fumula.Properties {c ℓ} (F : Fumula c ℓ) where

open import Function.Definitions using (Inverseˡ; Inverseʳ; Inverseᵇ)
open import Data.Product.Base using (_,_)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Nat.Properties using (+-comm)
open import Data.Integer.Base using (ℤ; +_; -[1+_]; -1ℤ; 0ℤ; 1ℤ; _+_; _-_)
open Fumula F
open import Algebra.Definitions _≈_ using (Involutive)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (cong to ≡-cong)
open import Relation.Binary.Reasoning.Setoid setoid
open import Algebra.Fumula.Definitions _≈_ _⤙_⤚_ using (OuterCommutativeWith)

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

------------------------------------------------------------------------
-- Properties of the invert operation.
------------------------------------------------------------------------

invert-involutive : Involutive invert
invert-involutive x = begin
  invert (invert x) ≡⟨⟩
  ■ ⤙ ◆ ⤚ (■ ⤙ ◆ ⤚ x) ≈⟨ sym (◆-outer-associate ■ ■ x ◆) ⟩
  ● ⤙ ◆ ⤚ x ≈⟨ ●-◆-collapse-sideˡ x ⟩
  x ∎

------------------------------------------------------------------------
-- The heartline of a fumula: the shadow of the integers
------------------------------------------------------------------------

heartline : ℤ → Carrier
heartline (+ zero) = ◆ -- ≈ ■ ↑
heartline (+ suc n) = heartline (+ n) ↑
heartline -[1+ zero ] = ■
heartline -[1+ suc n ] = heartline -[1+ n ] ↓

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
  x ⤙ z ⤚ heartline (+ n) ↑ ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  heartline (+ n) ↑ ⤙ z ⤚ x ∎
heartline-outer-commute -[1+ zero ] = ■-outer-commute
heartline-outer-commute -[1+ suc n ] x z = begin
  x ⤙ z ⤚ heartline -[1+ n ] ↓ ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  {!!} ≈⟨ {!!} ⟩
  heartline -[1+ n ] ↓ ⤙ z ⤚ x ∎
