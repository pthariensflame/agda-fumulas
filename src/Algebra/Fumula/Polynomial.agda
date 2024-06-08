{-# OPTIONS -WnoUnsupportedIndexedMatch #-} -- for trans
module Algebra.Fumula.Polynomial {c ℓ} where
open import Level using (_⊔_)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.Core using (Rel; _Preserves_⟶_; _Preserves₂_⟶_⟶_)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Reasoning.MultiSetoid
open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Congruent₂)
open import Algebra.Fumula.Core
open import Algebra.Fumula.Definitions
open import Algebra.Fumula.Bundles
import Algebra.Fumula.Properties as FumulaProperties
open import Algebra.Fumula.Morphism

module RawPolynomial (F : RawFumula c ℓ) where
  private
    module F = RawFumula F

  infix 7 var⤙_⤚_
  data Polynomial : Set c where
    var⤙_⤚_ : (x : F.Carrier) (f : Polynomial) → Polynomial
    const : (x : F.Carrier) → Polynomial

  ■ : Polynomial
  ■ = const F.■

  ◆ : Polynomial
  ◆ = const F.◆

  ● : Polynomial
  ● = const F.●

  var : Polynomial
  var = var⤙ F.◆ ⤚ ●

  infix 4 _≈_
  data _≈_ : Rel Polynomial (c ⊔ ℓ) where
    ≈var⤙_⤚_ : {x₁ x₂ : F.Carrier} {f₁ f₂ : Polynomial} (x≈ : x₁ F.≈ x₂) (f≈ : f₁ ≈ f₂) → var⤙ x₁ ⤚ f₁ ≈ var⤙ x₂ ⤚ f₂
    ≈var⤙_⤚◆ˡ≈_ : {x₁ x₂ : F.Carrier} {◆̂ : Polynomial} (x≈ : x₁ F.≈ x₂) (◆≈ : ◆̂ ≈ ◆) → var⤙ x₁ ⤚ ◆̂ ≈ const x₂
    ≈var⤙_⤚◆ʳ≈_ : {x₁ x₂ : F.Carrier} {◆̂ : Polynomial} (x≈ : x₁ F.≈ x₂) (◆≈ : ◆̂ ≈ ◆) → const x₁ ≈ var⤙ x₂ ⤚ ◆̂
    ≈const : {x₁ x₂ : F.Carrier} (x≈ : x₁ F.≈ x₂) → const x₁ ≈ const x₂

  var⤙⤚-cong : var⤙_⤚_ Preserves₂ F._≈_ ⟶ _≈_ ⟶ _≈_
  var⤙⤚-cong x≈y f≈g = ≈var⤙ x≈y ⤚ f≈g

  const-cong : const Preserves F._≈_ ⟶ _≈_
  const-cong x≈y = ≈const x≈y

  infix 7 ●⤙_⤚_
  ●⤙_⤚_ : F.Carrier → Polynomial → Polynomial
  ●⤙ x ⤚ var⤙ y ⤚ f = var⤙ F.● F.⤙ x ⤚ y ⤚ f
  ●⤙ x ⤚ const y = const (F.● F.⤙ x ⤚ y)

  infix 7 var⤙′_⤚_
  var⤙′_⤚_ : Op₂ Polynomial
  var⤙′ var⤙ x ⤚ h ⤚ var⤙ y ⤚ f = var⤙ x ⤚ var⤙′ ●⤙ y ⤚ h ⤚ f
  var⤙′ var⤙ x ⤚ h ⤚ const y = var⤙ x ⤚ ●⤙ y ⤚ h
  var⤙′ const x ⤚ f = var⤙ x ⤚ f

  infix 7 _⤙_⤚_
  _⤙_⤚_ : Op₃ Polynomial
  (var⤙ x ⤚ f) ⤙ var⤙ z ⤚ h ⤚ (var⤙ y ⤚ g) =
    var⤙ x F.⤙ z ⤚ y ⤚ var⤙′ f ⤙ const x ⤙ h ⤚ g ⤚ const y ⤚ (f ⤙ ◆ ⤚ g)
  (var⤙ x ⤚ f) ⤙ var⤙ z ⤚ h ⤚ const y = var⤙ x F.⤙ z ⤚ y ⤚ (f ⤙ h ⤚ const y)
  (var⤙ x ⤚ f) ⤙ const z ⤚ (var⤙ y ⤚ g) =
    var⤙ x F.⤙ z ⤚ y ⤚ var⤙′ f ⤙ const x ⤙ ◆ ⤚ g ⤚ const y ⤚ (f ⤙ ◆ ⤚ g)
  (var⤙ x ⤚ f) ⤙ const z ⤚ const y = var⤙ x F.⤙ z ⤚ y ⤚ (f ⤙ ◆ ⤚ const y)
  const x ⤙ var⤙ z ⤚ h ⤚ (var⤙ y ⤚ g) = var⤙ x F.⤙ z ⤚ y ⤚ (const x ⤙ h ⤚ g)
  const x ⤙ var⤙ z ⤚ h ⤚ const y = var⤙ x F.⤙ z ⤚ y ⤚ h
  const x ⤙ const z ⤚ (var⤙ y ⤚ g) = var⤙ x F.⤙ z ⤚ y ⤚ (const x ⤙ ◆ ⤚ g)
  const x ⤙ const z ⤚ const y = const (x F.⤙ z ⤚ y)

  eval : Polynomial → F.Carrier → F.Carrier
  eval (var⤙ x ⤚ f) v = v F.⤙ x ⤚ eval f v
  eval (const x) _ = x

  rawFumula : RawFumula c (c ⊔ ℓ)
  rawFumula = record
    { Carrier = Polynomial
    ; _≈_ = _≈_
    ; _⤙_⤚_ = _⤙_⤚_
    ; ■ = ■
    }
  open RawFumula rawFumula public
    hiding (Carrier; _≈_; _⤙_⤚_; ■; ◆; ●)

module FullPolynomial (F : ReversibleFumula c ℓ) where
  private
    module F where
      open ReversibleFumula F public
      open FumulaProperties fumula public

      double-double-exchange : ∀ v v′ w w′ x x′ y y′ z′ →
        v′ ⤙ v ⤙ x′ ⤙ x ⤙ z′ ⤚ y′ ⤚ y ⤚ w′ ⤚ w ≈
        x′ ⤙ x ⤙ v′ ⤙ v ⤙ z′ ⤚ w′ ⤚ w ⤚ y′ ⤚ y
      double-double-exchange v v′ w w′ x x′ y y′ z′ = begin⟨ setoid ⟩
        v′ ⤙ v ⤙ x′ ⤙ x ⤙ z′ ⤚ y′ ⤚ y ⤚ w′ ⤚ w ≈⟨ double-exchange v′ w v w′ (x′ ⤙ x ⤙ z′ ⤚ y′ ⤚ y) ⟩
        v ⤙ v′ ⤙ x′ ⤙ x ⤙ z′ ⤚ y′ ⤚ y ⤚ w ⤚ w′ ≈⟨ ⤙⤚-cong refl (double-exchange v′ w x′ y (x ⤙ z′ ⤚ y′)) refl ⟩
        v ⤙ x′ ⤙ v′ ⤙ x ⤙ z′ ⤚ y′ ⤚ w ⤚ y ⤚ w′ ≈⟨ ⤙⤚-cong refl (⤙⤚-cong refl (double-exchange v′ w x y′ z′) refl) refl ⟩
        v ⤙ x′ ⤙ x ⤙ v′ ⤙ z′ ⤚ w ⤚ y′ ⤚ y ⤚ w′ ≈⟨ ⤙⤚-cong refl (double-exchange x′ y x y′ (v′ ⤙ z′ ⤚ w)) refl ⟩
        v ⤙ x ⤙ x′ ⤙ v′ ⤙ z′ ⤚ w ⤚ y ⤚ y′ ⤚ w′ ≈⟨ double-exchange v w′ x y′ (x′ ⤙ v′ ⤙ z′ ⤚ w ⤚ y) ⟩
        x ⤙ v ⤙ x′ ⤙ v′ ⤙ z′ ⤚ w ⤚ y ⤚ w′ ⤚ y′ ≈⟨ ⤙⤚-cong refl (double-exchange v w′ x′ y (v′ ⤙ z′ ⤚ w)) refl ⟩
        x ⤙ x′ ⤙ v ⤙ v′ ⤙ z′ ⤚ w ⤚ w′ ⤚ y ⤚ y′ ≈⟨ ⤙⤚-cong refl (⤙⤚-cong refl (double-exchange v w′ v′ w z′) refl) refl ⟩
        x ⤙ x′ ⤙ v′ ⤙ v ⤙ z′ ⤚ w′ ⤚ w ⤚ y ⤚ y′ ≈⟨ double-exchange x y′ x′ y (v′ ⤙ v ⤙ z′ ⤚ w′ ⤚ w) ⟩
        x′ ⤙ x ⤙ v′ ⤙ v ⤙ z′ ⤚ w′ ⤚ w ⤚ y′ ⤚ y ∎

  open RawPolynomial F.rawFumula public

  eval-cong : eval Preserves₂ _≈_ ⟶ F._≈_ ⟶ F._≈_
  eval-cong (≈var⤙ x≈ ⤚ f≈) v≈ = F.⤙⤚-cong v≈ x≈ (eval-cong f≈ v≈)
  eval-cong (≈var⤙ x≈ ⤚◆ˡ≈ ◆≈) v≈ = F.trans (F.⤙⤚-cong F.refl F.refl eval-◆≈) (F.trans (F.◆-collapse-middleʳ _ _) x≈)
    where eval-◆≈ = eval-cong ◆≈ v≈
  eval-cong (≈var⤙ x≈ ⤚◆ʳ≈ ◆≈) v≈ = F.trans (F.trans x≈ (F.sym (F.◆-collapse-middleʳ _ _))) (F.⤙⤚-cong v≈ F.refl (F.sym eval-◆≈))
    where eval-◆≈ = eval-cong ◆≈ (F.sym v≈)
  eval-cong (≈const x≈) _ = x≈

  refl : Reflexive _≈_
  refl {var⤙ x ⤚ f} = ≈var⤙ F.refl ⤚ refl {x = f}
  refl {const x} = ≈const F.refl

  sym : Symmetric _≈_
  sym (≈var⤙ x≈y ⤚ f≈g) = ≈var⤙ F.sym x≈y ⤚ sym f≈g
  sym (≈var⤙ x≈y ⤚◆ˡ≈ ◆≈) = ≈var⤙ F.sym x≈y ⤚◆ʳ≈ ◆≈
  sym (≈var⤙ x≈y ⤚◆ʳ≈ ◆≈) = ≈var⤙ F.sym x≈y ⤚◆ˡ≈ ◆≈
  sym (≈const x≈y) = ≈const (F.sym x≈y)

  trans : Transitive _≈_
  trans {var⤙ x ⤚ f} {var⤙ z ⤚ h} {var⤙ y ⤚ g} (≈var⤙ x≈z ⤚ f≈h) (≈var⤙ z≈y ⤚ h≈g) = ≈var⤙ F.trans x≈z z≈y ⤚ trans f≈h h≈g
  trans {var⤙ x ⤚ f} {var⤙ z ⤚ h} {const y} (≈var⤙ x≈z ⤚ f≈h) (≈var⤙ z≈y ⤚◆ˡ≈ ◆≈ᵣ) = ≈var⤙ F.trans x≈z z≈y ⤚◆ˡ≈ trans f≈h ◆≈ᵣ
  trans {var⤙ x ⤚ f} {const z} {var⤙ y ⤚ g} (≈var⤙ x≈z ⤚◆ˡ≈ ◆≈ₗ) (≈var⤙ z≈y ⤚◆ʳ≈ ◆≈ᵣ) = ≈var⤙ F.trans x≈z z≈y ⤚ trans-◆-middle f g ◆≈ₗ ◆≈ᵣ
    where 
      trans-◆-middle : ∀ f′ g′ (f′≈◆ : f′ ≈ ◆) (g′≈◆ : g′ ≈ ◆) → f′ ≈ g′
      trans-◆-middle (var⤙ x′ ⤚ f′) (var⤙ y′ ⤚ g′) (≈var⤙ x′≈◆ ⤚◆ˡ≈ f′≈◆) (≈var⤙ y′≈◆ ⤚◆ˡ≈ g′≈◆) = ≈var⤙ F.trans x′≈◆ (F.sym y′≈◆) ⤚ trans-◆-middle f′ g′ f′≈◆ g′≈◆
      trans-◆-middle (var⤙ x′ ⤚ f′) (const y′) (≈var⤙ x′≈◆ ⤚◆ˡ≈ f′≈◆) (≈const y′≈◆) = ≈var⤙ F.trans x′≈◆ (F.sym y′≈◆) ⤚◆ˡ≈ f′≈◆
      trans-◆-middle (const x′) (var⤙ y′ ⤚ g′) (≈const x′≈◆) (≈var⤙ y′≈◆ ⤚◆ˡ≈ g′≈◆) = ≈var⤙ F.trans x′≈◆ (F.sym y′≈◆) ⤚◆ʳ≈ g′≈◆
      trans-◆-middle (const x′) (const y′) (≈const x′≈◆) (≈const y′≈◆) = ≈const (F.trans x′≈◆ (F.sym y′≈◆))
  trans {var⤙ x ⤚ f} {const z} {const y} (≈var⤙ x≈z ⤚◆ˡ≈ ◆≈ₗ) (≈const z≈y) = ≈var⤙ F.trans x≈z z≈y ⤚◆ˡ≈ ◆≈ₗ
  trans {const x} {var⤙ z ⤚ h} {var⤙ y ⤚ g} (≈var⤙ x≈z ⤚◆ʳ≈ ◆≈ₗ) (≈var⤙ z≈y ⤚ h≈g) = ≈var⤙ F.trans x≈z z≈y ⤚◆ʳ≈ trans-◆-side h g ◆≈ₗ h≈g
    where
      trans-◆-side : ∀ h′ g′ (h′≈◆ : h′ ≈ ◆) (h′≈g′ : h′ ≈ g′) → g′ ≈ ◆
      trans-◆-side (var⤙ z′ ⤚ h′) (var⤙ y′ ⤚ g′) (≈var⤙ z′≈◆ ⤚◆ˡ≈ h′≈◆) (≈var⤙ z′≈y′ ⤚ h′≈g′) = ≈var⤙ F.trans (F.sym z′≈y′) z′≈◆ ⤚◆ˡ≈ trans-◆-side h′ g′ h′≈◆ h′≈g′
      trans-◆-side (var⤙ z′ ⤚ h′) (const y′) (≈var⤙ z′≈◆ ⤚◆ˡ≈ _) (≈var⤙ z′≈y′ ⤚◆ˡ≈ h′≈g′) = ≈const (F.trans (F.sym z′≈y′) z′≈◆)
      trans-◆-side (const z′) (var⤙ y′ ⤚ g′) (≈const z′≈◆) (≈var⤙ z′≈y′ ⤚◆ʳ≈ h′≈g′) = ≈var⤙ F.trans (F.sym z′≈y′) z′≈◆ ⤚◆ˡ≈ h′≈g′
      trans-◆-side (const z′) (const y′) (≈const z′≈◆) (≈const z′≈y′) = ≈const (F.trans (F.sym z′≈y′) z′≈◆)
  trans {const x} {var⤙ z ⤚ h} {const y} (≈var⤙ x≈z ⤚◆ʳ≈ _) (≈var⤙ z≈y ⤚◆ˡ≈ _) = ≈const (F.trans x≈z z≈y)
  trans {const x} {const z} {var⤙ y ⤚ g} (≈const x≈z) (≈var⤙ z≈y ⤚◆ʳ≈ ◆≈ᵣ) = ≈var⤙ F.trans x≈z z≈y ⤚◆ʳ≈ ◆≈ᵣ
  trans {const x} {const z} {const y} (≈const x≈z) (≈const z≈y) = ≈const (F.trans x≈z z≈y)

  setoid : Setoid c (c ⊔ ℓ)
  setoid = record
    { Carrier = Polynomial
    ; _≈_ = _≈_
    ; isEquivalence = record
      { refl = refl
      ; sym = sym
      ; trans = trans
      }
    }
  open Setoid setoid public
    hiding (Carrier; _≈_; _≉_; refl; sym; trans)

  ◆≈■↑ : ◆ ≈ ■ ↑
  ◆≈■↑ = refl

  ●≈◆↑ : ● ≈ ◆ ↑
  ●≈◆↑ = refl

  ●≈■↑↑ : ● ≈ ■ ↑ ↑
  ●≈■↑↑ = refl

  ●⤙⤚-cong : ●⤙_⤚_ Preserves₂ F._≈_ ⟶ _≈_ ⟶ _≈_
  ●⤙⤚-cong x≈ (≈var⤙ y≈ ⤚ f≈) = ≈var⤙ F.⤙⤚-cong F.refl x≈ y≈ ⤚ f≈
  ●⤙⤚-cong x≈ (≈var⤙ y≈ ⤚◆ˡ≈ ◆≈) = ≈var⤙ F.⤙⤚-cong F.refl x≈ y≈ ⤚◆ˡ≈ ◆≈
  ●⤙⤚-cong x≈ (≈var⤙ y≈ ⤚◆ʳ≈ ◆≈) = ≈var⤙ F.⤙⤚-cong F.refl x≈ y≈ ⤚◆ʳ≈ ◆≈
  ●⤙⤚-cong x≈ (≈const y≈) = ≈const (F.⤙⤚-cong F.refl x≈ y≈)

  ●⤙⤚-◆-collapse-middleʳ : ∀ x {◆̂} (◆≈ : ◆̂ ≈ ◆) → ●⤙ x ⤚ ◆̂ ≈ const x
  ●⤙⤚-◆-collapse-middleʳ x ◆≈ = trans (●⤙⤚-cong F.refl ◆≈) (≈const (F.◆-collapse-middleʳ F.● x))

  ●⤙⤚-◆-collapse-sideˡ : ∀ f → ●⤙ F.◆ ⤚ f ≈ f
  ●⤙⤚-◆-collapse-sideˡ (var⤙ x ⤚ f) = ≈var⤙ F.●-◆-collapse-sideˡ x ⤚ refl
  ●⤙⤚-◆-collapse-sideˡ (const x) = ≈const (F.●-◆-collapse-sideˡ x)

  var⤙′⤚-◆-collapse-middleʳ : ∀ f {◆̂} (◆≈ : ◆̂ ≈ ◆) → var⤙′ f ⤚ ◆̂ ≈ f
  var⤙′⤚-◆-collapse-middleʳ (var⤙ x ⤚ f) (≈var⤙ x≈ ⤚◆ˡ≈ ◆≈) =
    ≈var⤙ F.refl ⤚ trans (var⤙′⤚-◆-collapse-middleʳ (●⤙ _ ⤚ f) ◆≈) (trans (●⤙⤚-cong x≈ refl) (●⤙⤚-◆-collapse-sideˡ f))
  var⤙′⤚-◆-collapse-middleʳ (var⤙ x ⤚ f) (≈const x≈) =
    ≈var⤙ F.refl ⤚ trans (●⤙⤚-cong x≈ refl) (●⤙⤚-◆-collapse-sideˡ f)
  var⤙′⤚-◆-collapse-middleʳ (const x) ◆≈ = ≈var⤙ F.refl ⤚◆ˡ≈ ◆≈

  var⤙′⤚-cong : Congruent₂ _≈_ var⤙′_⤚_
  var⤙′⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ z≈ ⤚ h≈) (≈var⤙ x≈ ⤚ f≈) =
    ≈var⤙ z≈ ⤚ var⤙′⤚-cong (●⤙⤚-cong x≈ h≈) f≈
  var⤙′⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ z≈ ⤚ h≈) (≈var⤙ x≈ ⤚◆ˡ≈ ◆≈ᵣ) =
    ≈var⤙ z≈ ⤚ trans (var⤙′⤚-◆-collapse-middleʳ (●⤙ _ ⤚ _) ◆≈ᵣ) (●⤙⤚-cong x≈ h≈)
  var⤙′⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ z≈ ⤚ h≈) (≈var⤙ x≈ ⤚◆ʳ≈ ◆≈ᵣ) =
    ≈var⤙ z≈ ⤚ trans  (●⤙⤚-cong x≈ h≈) (sym (var⤙′⤚-◆-collapse-middleʳ (●⤙ _ ⤚ _) ◆≈ᵣ))
  var⤙′⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} (≈var⤙ z≈ ⤚ h≈) (≈const x≈) =
    ≈var⤙ z≈ ⤚ ●⤙⤚-cong x≈ h≈
  var⤙′⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ z≈ ⤚◆ˡ≈ ◆≈ₗ) (≈var⤙ x≈ ⤚ f≈) =
    ≈var⤙ z≈ ⤚ var⤙′⤚-cong (trans (●⤙⤚-◆-collapse-middleʳ _ ◆≈ₗ) (≈const x≈)) f≈
  var⤙′⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ z≈ ⤚◆ˡ≈ ◆≈ₗ) (≈var⤙ x≈ ⤚◆ˡ≈ ◆≈ᵣ) =
    ≈var⤙ z≈ ⤚ trans (var⤙′⤚-◆-collapse-middleʳ _ ◆≈ᵣ) (trans (●⤙⤚-◆-collapse-middleʳ _ ◆≈ₗ) (≈const x≈))
  var⤙′⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ z≈ ⤚◆ˡ≈ ◆≈ₗ) (≈var⤙ x≈ ⤚◆ʳ≈ ◆≈ᵣ) =
    ≈var⤙ z≈ ⤚ trans (●⤙⤚-◆-collapse-middleʳ _ ◆≈ₗ) (≈var⤙ x≈ ⤚◆ʳ≈ ◆≈ᵣ)
  var⤙′⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} (≈var⤙ z≈ ⤚◆ˡ≈ ◆≈ₗ) (≈const x≈) =
    ≈var⤙ z≈ ⤚ trans (●⤙⤚-◆-collapse-middleʳ _ ◆≈ₗ) (≈const x≈)
  var⤙′⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ z≈ ⤚◆ʳ≈ ◆≈ₗ) (≈var⤙ x≈ ⤚ f≈) =
    ≈var⤙ z≈ ⤚ trans (≈var⤙ x≈ ⤚ f≈) (var⤙′⤚-cong (sym (●⤙⤚-◆-collapse-middleʳ _ ◆≈ₗ)) refl)
  var⤙′⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ z≈ ⤚◆ʳ≈ ◆≈ₗ) (≈var⤙ x≈ ⤚◆ˡ≈ ◆≈ᵣ) =
    ≈var⤙ z≈ ⤚ trans (≈var⤙ x≈ ⤚◆ˡ≈ ◆≈ᵣ) (sym (●⤙⤚-◆-collapse-middleʳ _ ◆≈ₗ))
  var⤙′⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ z≈ ⤚◆ʳ≈ ◆≈ₗ) (≈var⤙ x≈ ⤚◆ʳ≈ ◆≈ᵣ) =
    ≈var⤙ z≈ ⤚ trans (≈const x≈) (sym (trans (var⤙′⤚-◆-collapse-middleʳ _ ◆≈ᵣ) (●⤙⤚-◆-collapse-middleʳ _ ◆≈ₗ)))
  var⤙′⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} (≈var⤙ z≈ ⤚◆ʳ≈ ◆≈ₗ) (≈const x≈) =
    ≈var⤙ z≈ ⤚ trans (≈const x≈) (sym (●⤙⤚-◆-collapse-middleʳ _ ◆≈ₗ))
  var⤙′⤚-cong {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈const z≈) (≈var⤙ x≈ ⤚ f≈) =
    ≈var⤙ z≈ ⤚ ≈var⤙ x≈ ⤚ f≈
  var⤙′⤚-cong {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈const z≈) (≈var⤙ x≈ ⤚◆ˡ≈ ◆≈ᵣ) =
    ≈var⤙ z≈ ⤚ ≈var⤙ x≈ ⤚◆ˡ≈ ◆≈ᵣ
  var⤙′⤚-cong {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈const z≈) (≈var⤙ x≈ ⤚◆ʳ≈ ◆≈ᵣ) =
    ≈var⤙ z≈ ⤚ ≈var⤙ x≈ ⤚◆ʳ≈ ◆≈ᵣ
  var⤙′⤚-cong {.(const _)} {.(const _)} {.(const _)} {.(const _)} (≈const z≈) (≈const x≈) =
    ≈var⤙ z≈ ⤚ ≈const x≈

  var⤙′⤚-◆-double-exchange-complex : ∀ v v⋆ w w⋆ x x⋆ y y⋆ z →
    var⤙′ v ⤙ const v⋆ ⤙ var⤙′ x ⤙ const x⋆ ⤙ z ⤚ y ⤚ const y⋆ ⤚ (x ⤙ ◆ ⤚ y) ⤚ w ⤚ const w⋆ ⤚ (v ⤙ ◆ ⤚ w) ≈
    var⤙′ x ⤙ const x⋆ ⤙ var⤙′ v ⤙ const v⋆ ⤙ z ⤚ w ⤚ const w⋆ ⤚ (v ⤙ ◆ ⤚ w) ⤚ y ⤚ const y⋆ ⤚ (x ⤙ ◆ ⤚ y)
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(var⤙ z⋆′ ⤚ z′) =
    RawPolynomial.≈var⤙ F.double-double-exchange v⋆ v⋆′ w⋆ w⋆′ x⋆ x⋆′ y⋆ y⋆′ z⋆′ ⤚ {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(const y⋆′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(const y⋆′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(const x⋆′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(const x⋆′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(const x⋆′) x⋆ y@(const y⋆′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(const x⋆′) x⋆ y@(const y⋆′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(const w⋆′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(const w⋆′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(const w⋆′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(const y⋆′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(const w⋆′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(const y⋆′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(const w⋆′) w⋆ x@(const x⋆′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(const w⋆′) w⋆ x@(const x⋆′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(const w⋆′) w⋆ x@(const x⋆′) x⋆ y@(const y⋆′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(var⤙ v⋆′ ⤚ v′) v⋆ w@(const w⋆′) w⋆ x@(const x⋆′) x⋆ y@(const y⋆′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(const y⋆′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(const y⋆′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(const x⋆′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(const x⋆′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(const x⋆′) x⋆ y@(const y⋆′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(var⤙ w⋆′ ⤚ w′) w⋆ x@(const x⋆′) x⋆ y@(const y⋆′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(const w⋆′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(const w⋆′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(const w⋆′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(const y⋆′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(const w⋆′) w⋆ x@(var⤙ x⋆′ ⤚ x′) x⋆ y@(const y⋆′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(const w⋆′) w⋆ x@(const x⋆′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(const w⋆′) w⋆ x@(const x⋆′) x⋆ y@(var⤙ y⋆′ ⤚ y′) y⋆ z@(const z⋆′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(const w⋆′) w⋆ x@(const x⋆′) x⋆ y@(const y⋆′) y⋆ z@(var⤙ z⋆′ ⤚ z′) = {!!}
  var⤙′⤚-◆-double-exchange-complex v@(const v⋆′) v⋆ w@(const w⋆′) w⋆ x@(const x⋆′) x⋆ y@(const y⋆′) y⋆ z@(const z⋆′) = {!!}

  -- double-exchange : MiddleNestedDoubleExchange _≈_ _⤙_⤚_
  -- double-exchange (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ var⤙′⤚-◆-double-exchange-complex v v⋆ w w⋆ x x⋆ y y⋆ z
  -- double-exchange (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ var⤙′⤚-◆-double-exchange-complex v v⋆ w w⋆ x x⋆ y y⋆ ◆
  -- double-exchange (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (const y⋆) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (const w⋆) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = ≈var⤙ F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆ ⤚ {!!}
  -- double-exchange (const v⋆) (const w⋆) (const x⋆) (const y⋆) (const z⋆) = ≈const (F.double-exchange v⋆ w⋆ x⋆ y⋆ z⋆)

  -- ■-collapse-dupˡ : ∀ x → ■ ⤙ x ⤚ x ≈ ◆
  -- ■-collapse-dupˡ (var⤙ x ⤚ f) = ≈var⤙ F.■-collapse-dupˡ x ⤚◆ˡ≈ ■-collapse-dupˡ f
  -- ■-collapse-dupˡ (const x) = ≈const (F.■-collapse-dupˡ x)

  -- ■-collapse-dupʳ : ∀ x → x ⤙ x ⤚ ■ ≈ ◆
  -- ■-collapse-dupʳ (var⤙ x ⤚ f) = ≈var⤙ F.■-collapse-dupʳ x ⤚◆ˡ≈ ■-collapse-dupʳ f
  -- ■-collapse-dupʳ (const x) = ≈const (F.■-collapse-dupʳ x)

  -- ◆-collapse-middleˡ : ∀ x z → ◆ ⤙ z ⤚ x ≈ z
  -- ◆-collapse-middleˡ (var⤙ y ⤚ g) (var⤙ z ⤚ h) = ≈var⤙ F.◆-collapse-middleˡ y z ⤚ ◆-collapse-middleˡ g h
  -- ◆-collapse-middleˡ (var⤙ y ⤚ g) (const z) = ≈var⤙ F.◆-collapse-middleˡ y z ⤚◆ˡ≈ ◆-collapse-middleˡ g ◆
  -- ◆-collapse-middleˡ (const y) (var⤙ z ⤚ _) = ≈var⤙ F.◆-collapse-middleˡ y z ⤚ refl
  -- ◆-collapse-middleˡ (const y) (const z) = ≈const (F.◆-collapse-middleˡ y z)

  -- ◆-collapse-middleʳ : ∀ x z → x ⤙ z ⤚ ◆ ≈ z
  -- ◆-collapse-middleʳ (var⤙ x ⤚ f) (var⤙ z ⤚ h) = ≈var⤙ F.◆-collapse-middleʳ x z ⤚ ◆-collapse-middleʳ f h
  -- ◆-collapse-middleʳ (var⤙ x ⤚ f) (const z) = ≈var⤙ F.◆-collapse-middleʳ x z ⤚◆ˡ≈ ◆-collapse-middleʳ f ◆
  -- ◆-collapse-middleʳ (const x) (var⤙ z ⤚ _) = ≈var⤙ F.◆-collapse-middleʳ x z ⤚ refl
  -- ◆-collapse-middleʳ (const x) (const z) = ≈const (F.◆-collapse-middleʳ x z)

  -- ●-◆-collapse-sideˡ : ∀ x → (● ⤙ ◆ ⤚ x) ≈ x
  -- ●-◆-collapse-sideˡ (var⤙ x ⤚ f) = ≈var⤙ F.●-◆-collapse-sideˡ x ⤚ ●-◆-collapse-sideˡ f
  -- ●-◆-collapse-sideˡ (const x) = ≈const (F.●-◆-collapse-sideˡ x)

  -- ●-◆-collapse-sideʳ : ∀ x → (x ⤙ ◆ ⤚ ●) ≈ x
  -- ●-◆-collapse-sideʳ (var⤙ x ⤚ f) = ≈var⤙ F.●-◆-collapse-sideʳ x ⤚ ●-◆-collapse-sideʳ f
  -- ●-◆-collapse-sideʳ (const x) = ≈const (F.●-◆-collapse-sideʳ x)

  -- ●-inner-commuteˡ : LeftInnerCommutativeWith _≈_ _⤙_⤚_ ●
  -- ●-inner-commuteˡ (var⤙ x ⤚ f) (var⤙ y ⤚ g) = ≈var⤙ F.●-inner-commuteˡ x y ⤚ ●-inner-commuteˡ f g
  -- ●-inner-commuteˡ (var⤙ x ⤚ f) (const y) = ≈var⤙ F.●-inner-commuteˡ x y ⤚ ●-◆-collapse-sideʳ f
  -- ●-inner-commuteˡ (const x) (var⤙ y ⤚ g) = ≈var⤙ F.●-inner-commuteˡ x y ⤚ sym (●-◆-collapse-sideʳ g)
  -- ●-inner-commuteˡ (const x) (const y) = ≈const (F.●-inner-commuteˡ x y)

  -- ●-inner-commuteʳ : RightInnerCommutativeWith _≈_ _⤙_⤚_ ●
  -- ●-inner-commuteʳ (var⤙ x ⤚ f) (var⤙ y ⤚ g) = ≈var⤙ F.●-inner-commuteʳ x y ⤚ ●-inner-commuteʳ f g
  -- ●-inner-commuteʳ (var⤙ x ⤚ f) (const y) = ≈var⤙ F.●-inner-commuteʳ x y ⤚ sym (●-◆-collapse-sideˡ f)
  -- ●-inner-commuteʳ (const x) (var⤙ y ⤚ g) = ≈var⤙ F.●-inner-commuteʳ x y ⤚ ●-◆-collapse-sideˡ g
  -- ●-inner-commuteʳ (const x) (const y) = ≈const (F.●-inner-commuteʳ x y)

  -- ◆-outer-associate : OuterAssociativeWith _≈_ _⤙_⤚_ ◆
  -- ◆-outer-associate (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = ≈var⤙ {!!} ⤚ {!!}
  -- ◆-outer-associate (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-outer-associate (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-outer-associate (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- ◆-outer-associate (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-outer-associate (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-outer-associate (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-outer-associate (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (const z⋆) = {!!}
  -- ◆-outer-associate (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-outer-associate (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-outer-associate (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-outer-associate (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- ◆-outer-associate (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-outer-associate (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-outer-associate (const w⋆) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-outer-associate (const w⋆) (const x⋆) (const y⋆) (const z⋆) = {!!}

  -- ◆-pulloutˡ : LeftPulloutWith _≈_ _⤙_⤚_ ◆
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutˡ (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutˡ (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutˡ (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutˡ (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutˡ (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutˡ (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutˡ (const v⋆) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (const v⋆) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutˡ (const v⋆) (const w⋆) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutˡ (const v⋆) (const w⋆) (const x⋆) (const y⋆) (const z⋆) = {!!}

  -- ◆-pulloutʳ : RightPulloutWith _≈_ _⤙_⤚_ ◆
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (var⤙ v⋆ ⤚ v) (const w⋆) (const x⋆) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutʳ (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutʳ (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (const v⋆) (var⤙ w⋆ ⤚ w) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutʳ (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutʳ (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (const v⋆) (var⤙ w⋆ ⤚ w) (const x⋆) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutʳ (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutʳ (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (const v⋆) (const w⋆) (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- ◆-pulloutʳ (const v⋆) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (const v⋆) (const w⋆) (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- ◆-pulloutʳ (const v⋆) (const w⋆) (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- ◆-pulloutʳ (const v⋆) (const w⋆) (const x⋆) (const y⋆) (const z⋆) = {!!}

  -- outer-commute : OuterCommutative _≈_ _⤙_⤚_
  -- outer-commute (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- outer-commute (var⤙ x⋆ ⤚ x) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- outer-commute (var⤙ x⋆ ⤚ x) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- outer-commute (var⤙ x⋆ ⤚ x) (const y⋆) (const z⋆) = {!!}
  -- outer-commute (const x⋆) (var⤙ y⋆ ⤚ y) (var⤙ z⋆ ⤚ z) = {!!}
  -- outer-commute (const x⋆) (var⤙ y⋆ ⤚ y) (const z⋆) = {!!}
  -- outer-commute (const x⋆) (const y⋆) (var⤙ z⋆ ⤚ z) = {!!}
  -- outer-commute (const x⋆) (const y⋆) (const z⋆) = {!!}

  -- ⤙⤚-cong : Congruent₃ _≈_ _⤙_⤚_
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚ g≈) =
  --   ≈var⤙ F.⤙⤚-cong x≈ z≈ y≈ ⤚ var⤙′⤚-cong (⤙⤚-cong f≈ (⤙⤚-cong (≈const x≈) h≈ g≈) (≈const y≈)) (⤙⤚-cong f≈ refl g≈)
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   ≈var⤙ F.⤙⤚-cong x≈ z≈ y≈ ⤚ trans
  --     (var⤙′⤚-◆-collapse-middleʳ
  --       (_ ⤙ const _ ⤙ _ ⤚ _ ⤚ const _)
  --       (trans (⤙⤚-cong refl refl g◆≈) (◆-collapse-middleʳ _ ◆)))
  --     (⤙⤚-cong f≈
  --       (trans (trans (⤙⤚-cong refl refl g◆≈) (◆-collapse-middleʳ (const _) _)) h≈)
  --       (≈const y≈))
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   ≈var⤙ F.⤙⤚-cong x≈ z≈ y≈ ⤚ trans
  --     (⤙⤚-cong f≈
  --       (trans (sym (◆-collapse-middleʳ (const _) _)) (⤙⤚-cong (≈const x≈) h≈ (sym g◆≈)))
  --       (≈const y≈))
  --     (sym (var⤙′⤚-◆-collapse-middleʳ
  --       (_ ⤙ const _ ⤙ _ ⤚ _ ⤚ const _)
  --       (trans (⤙⤚-cong refl refl g◆≈) (◆-collapse-middleʳ _ ◆))))
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚ h≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚ f≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚ f≈) (≈const z≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚ f≈) (≈const z≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚ f≈) (≈const z≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚ f≈) (≈const z≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚ h≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈const z≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈const z≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈const z≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚◆ˡ≈ f◆≈) (≈const z≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚ h≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈const z≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈const z≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈const z≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} {.(const _)} (≈var⤙ x≈ ⤚◆ʳ≈ f◆≈) (≈const z≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈const x≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈const x≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈const x≈) (≈var⤙ z≈ ⤚ h≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} (≈const x≈) (≈var⤙ z≈ ⤚ h≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈const x≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈const x≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈const x≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} {.(const _)} (≈const x≈) (≈var⤙ z≈ ⤚◆ˡ≈ h◆≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈const x≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈const x≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈const x≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} {.(const _)} (≈const x≈) (≈var⤙ z≈ ⤚◆ʳ≈ h◆≈) (≈const y≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(var⤙ _ ⤚ _)} (≈const x≈) (≈const z≈) (≈var⤙ y≈ ⤚ g≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} {.(const _)} (≈const x≈) (≈const z≈) (≈var⤙ y≈ ⤚◆ˡ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(const _)} {.(const _)} {.(const _)} {.(var⤙ _ ⤚ _)} (≈const x≈) (≈const z≈) (≈var⤙ y≈ ⤚◆ʳ≈ g◆≈) =
  --   {!!}
  -- ⤙⤚-cong {.(const _)} {.(const _)} {.(const _)} {.(const _)} {.(const _)} {.(const _)} (≈const x≈) (≈const z≈) (≈const y≈) =
  --   {!!}

  -- reversibleFumula : ReversibleFumula c (c ⊔ ℓ)
  -- reversibleFumula = record
  --   { Carrier = Polynomial
  --   ; _≈_ = _≈_
  --   ; _⤙_⤚_ = _⤙_⤚_
  --   ; ■ = ■
  --   ; isReversibleFumula = record
  --     { isFumula = record
  --       { isAlmostFumula = record
  --         { isEquivalence = isEquivalence
  --         ; ⤙⤚-cong = ⤙⤚-cong
  --         ; double-exchange = double-exchange
  --         }
  --       ; ■-outer-commute = outer-commute ■
  --       ; ■-collapse-dup = ■-collapse-dupˡ , ■-collapse-dupʳ
  --       ; ◆-outer-commute = outer-commute ◆
  --       ; ◆-collapse-middle = ◆-collapse-middleˡ , ◆-collapse-middleʳ
  --       ; ●-outer-commute = outer-commute ●
  --       ; ●-inner-commute = ●-inner-commuteˡ , ●-inner-commuteʳ
  --       ; ◆-outer-associate = ◆-outer-associate
  --       ; ◆-pullout = ◆-pulloutˡ , ◆-pulloutʳ
  --       }
  --     ; outer-commute = outer-commute
  --     }
  --   }
  -- open ReversibleFumula reversibleFumula public
  --   hiding (Carrier; _≈_; _≉_; _⤙_⤚_; _↑; _↑′; _↓; _↓′; invert; ■; ◆; ●; ⤙⤚-cong;
  --           refl; sym; trans; reflexive; isPartialEquivalence; isEquivalence; setoid; rawAlmostFumula; rawFumula;
  --           double-exchange; ■-collapse-dupˡ; ■-collapse-dupʳ; ◆-collapse-middleˡ; ◆-collapse-middleʳ;
  --           ◆-outer-associate; ●-inner-commuteˡ; ●-inner-commuteʳ; ◆-pulloutˡ; ◆-pulloutʳ; outer-commute)
  -- open FumulaProperties fumula public
  --   hiding (●-◆-collapse-sideˡ; ●-◆-collapse-sideʳ; ●-◆-collapse-side)

  -- ●-◆-collapse-side : (∀ x → ● ⤙ ◆ ⤚ x ≈ x) × (∀ x → x ⤙ ◆ ⤚ ● ≈ x)
  -- ●-◆-collapse-side = ●-◆-collapse-sideˡ , ●-◆-collapse-sideʳ

  -- eval-homo : ∀ v → IsFumulaHomomorphism rawFumula F.rawFumula (λ x → eval x v)
  -- eval-homo v = record
  --   { isAlmostFumulaHomomorphism = record
  --     { isRelHomomorphism = record
  --       { cong = λ x≈ → eval-cong x≈ F.refl
  --       }
  --     ; homo = homo
  --     }
  --   ; ■-homo = F.refl
  --   }
  --   where
  --     open SetoidReasoning F.setoid

  --     homo : (f h g : Polynomial) → eval (f ⤙ h ⤚ g) v F.≈ eval f v F.⤙ eval h v ⤚ eval g v
  --     homo (var⤙ x ⤚ f) (var⤙ z ⤚ h) (var⤙ y ⤚ g) = begin
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ∎
  --     homo (var⤙ x ⤚ f) (var⤙ z ⤚ h) (const y) = begin
  --       v F.⤙ x F.⤙ z ⤚ y ⤚ eval (f ⤙ h ⤚ const y) v ≈⟨ F.⤙⤚-cong F.refl F.refl (homo f h (const y)) ⟩
  --       v F.⤙ x F.⤙ z ⤚ y ⤚ (eval f v F.⤙ eval h v ⤚ y) ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       (v F.⤙ x ⤚ eval f v) F.⤙ v F.⤙ z ⤚ eval h v ⤚ y ∎
  --     homo (var⤙ x ⤚ f) (const z) (var⤙ y ⤚ g) = begin
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ∎
  --     homo (var⤙ x ⤚ f) (const z) (const y) = begin
  --       v F.⤙ x F.⤙ z ⤚ y ⤚ eval (f ⤙ ◆ ⤚ const y) v ≈⟨ F.⤙⤚-cong F.refl F.refl (homo f ◆ (const y)) ⟩
  --       v F.⤙ x F.⤙ z ⤚ y ⤚ (eval f v F.⤙ F.◆ ⤚ y) ≈⟨ F.◆-outer-associate v (eval f v) y (x F.⤙ z ⤚ y) ⟨
  --       (v F.⤙ F.◆ ⤚ eval f v) F.⤙ x F.⤙ z ⤚ y ⤚ y ≈⟨ F.◆-pulloutˡ x v (eval f v) y z ⟨
  --       (v F.⤙ x ⤚ eval f v) F.⤙ z ⤚ y ∎
  --     homo (const x) (var⤙ z ⤚ h) (var⤙ y ⤚ g) = begin
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ≈⟨ {!!} ⟩
  --       {!!} ∎
  --     homo (const x) (var⤙ z ⤚ h) (const y) = F.double-exchange v (eval h v) x y z
  --     homo (const x) (const z) (var⤙ y ⤚ g) = begin
  --       v F.⤙ x F.⤙ z ⤚ y ⤚ eval (const x ⤙ ◆ ⤚ g) v ≈⟨ F.⤙⤚-cong F.refl F.refl (homo (const x) ◆ g) ⟩
  --       v F.⤙ x F.⤙ z ⤚ y ⤚ (x F.⤙ F.◆ ⤚ eval g v) ≈⟨ F.◆-outer-associate v x (eval g v) (x F.⤙ z ⤚ y) ⟨
  --       (v F.⤙ F.◆ ⤚ x) F.⤙ x F.⤙ z ⤚ y ⤚ eval g v ≈⟨ F.⤙⤚-cong (F.outer-commute v x F.◆) F.refl F.refl ⟨
  --       (x F.⤙ F.◆ ⤚ v) F.⤙ x F.⤙ z ⤚ y ⤚ eval g v ≈⟨ F.◆-outer-associate x v (eval g v) (x F.⤙ z ⤚ y) ⟩
  --       x F.⤙ x F.⤙ z ⤚ y ⤚ (v F.⤙ F.◆ ⤚ eval g v) ≈⟨ F.◆-pulloutʳ z x v (eval g v) y ⟨
  --       x F.⤙ z ⤚ (v F.⤙ y ⤚ eval g v) ∎
  --     homo (const x) (const z) (const y) = F.refl
