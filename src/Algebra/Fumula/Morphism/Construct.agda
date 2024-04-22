module Algebra.Fumula.Morphism.Construct where
open import Data.Product.Base using (_,_)
open import Function.Base using (id; _∘_)
import Function.Construct.Identity as Id
import Function.Construct.Composition as Comp
open import Relation.Binary.Morphism.Construct.Identity using () renaming (isRelHomomorphism to id-isRelHomomorphism)
open import Relation.Binary.Morphism.Construct.Composition using () renaming (isRelHomomorphism to ∘-isRelHomomorphism)
open import Relation.Binary.Definitions using (Reflexive; Transitive)
open import Algebra.Fumula.Bundles
open import Algebra.Fumula.Morphism using (module AlmostFumulaMorphisms; module FumulaMorphisms)

module Identity {c ℓ} where

  module _ (F : RawAlmostFumula c ℓ) (open RawAlmostFumula F) (refl : Reflexive _≈_) where
    open AlmostFumulaMorphisms F F

    isAlmostFumulaHomomorphism : IsAlmostFumulaHomomorphism id
    isAlmostFumulaHomomorphism = record
      { isRelHomomorphism = id-isRelHomomorphism _≈_
      ; homo = λ _ _ _ → refl
      }

    isAlmostFumulaMonomorphism : IsAlmostFumulaMonomorphism id
    isAlmostFumulaMonomorphism = record
      { isAlmostFumulaHomomorphism = isAlmostFumulaHomomorphism
      ; injective = id
      }

    isAlmostFumulaIsomorphism : IsAlmostFumulaIsomorphism id
    isAlmostFumulaIsomorphism = record
      { isAlmostFumulaMonomorphism = isAlmostFumulaMonomorphism
      ; surjective = Id.surjective _≈_
      }

  module _ (F : RawFumula c ℓ) (open RawFumula F) (refl : Reflexive _≈_) where
    open FumulaMorphisms F F

    isFumulaHomomorphism : IsFumulaHomomorphism id
    isFumulaHomomorphism = record
      { isAlmostFumulaHomomorphism = isAlmostFumulaHomomorphism rawAlmostFumula refl
      ; ■-homo = refl
      }

    isFumulaMonomorphism : IsFumulaMonomorphism id
    isFumulaMonomorphism = record
      { isFumulaHomomorphism = isFumulaHomomorphism
      ; injective = id
      }

    isFumulaIsomorphism : IsFumulaIsomorphism id
    isFumulaIsomorphism = record
      { isFumulaMonomorphism = isFumulaMonomorphism
      ; surjective = Id.surjective _≈_
      }

module Composition {a b c ℓ₁ ℓ₂ ℓ₃} where

  module _ {F₁ : RawAlmostFumula a ℓ₁} {F₂ : RawAlmostFumula b ℓ₂} {F₃ : RawAlmostFumula c ℓ₃}
           (let module F₁ = RawAlmostFumula F₁) (let module F₂ = RawAlmostFumula F₂) (let module F₃ = RawAlmostFumula F₃)
           (≈₃-trans : Transitive F₃._≈_) {f : F₁.Carrier → F₂.Carrier} {g : F₂.Carrier → F₃.Carrier}
           where
    open AlmostFumulaMorphisms

    isAlmostFumulaHomomorphism : IsAlmostFumulaHomomorphism F₁ F₂ f → IsAlmostFumulaHomomorphism F₂ F₃ g
                               → IsAlmostFumulaHomomorphism F₁ F₃ (g ∘ f)
    isAlmostFumulaHomomorphism f-homo g-homo = record
      { isRelHomomorphism = ∘-isRelHomomorphism f.isRelHomomorphism g.isRelHomomorphism
      ; homo = λ x y z → ≈₃-trans (g.⟦⟧-cong (f.homo x y z)) (g.homo (f x) (f y) (f z))
      }
      where
        module f = IsAlmostFumulaHomomorphism f-homo
        module g = IsAlmostFumulaHomomorphism g-homo

    isAlmostFumulaMonomorphism : IsAlmostFumulaMonomorphism F₁ F₂ f → IsAlmostFumulaMonomorphism F₂ F₃ g
                               → IsAlmostFumulaMonomorphism F₁ F₃ (g ∘ f)
    isAlmostFumulaMonomorphism f-mono g-mono = record
      { isAlmostFumulaHomomorphism = isAlmostFumulaHomomorphism f.isAlmostFumulaHomomorphism g.isAlmostFumulaHomomorphism
      ; injective = f.injective ∘ g.injective
      }
      where
        module f = IsAlmostFumulaMonomorphism f-mono
        module g = IsAlmostFumulaMonomorphism g-mono

    isAlmostFumulaIsomorphism : IsAlmostFumulaIsomorphism F₁ F₂ f → IsAlmostFumulaIsomorphism F₂ F₃ g
                               → IsAlmostFumulaIsomorphism F₁ F₃ (g ∘ f)
    isAlmostFumulaIsomorphism f-iso g-iso = record
      { isAlmostFumulaMonomorphism = isAlmostFumulaMonomorphism f.isAlmostFumulaMonomorphism g.isAlmostFumulaMonomorphism
      ; surjective = Comp.surjective F₁._≈_ F₂._≈_ F₃._≈_ f.surjective g.surjective
      }
      where
        module f = IsAlmostFumulaIsomorphism f-iso
        module g = IsAlmostFumulaIsomorphism g-iso

  module _ {F₁ : RawFumula a ℓ₁} {F₂ : RawFumula b ℓ₂} {F₃ : RawFumula c ℓ₃}
           (let module F₁ = RawFumula F₁) (let module F₂ = RawFumula F₂) (let module F₃ = RawFumula F₃)
           (≈₃-trans : Transitive F₃._≈_) {f : F₁.Carrier → F₂.Carrier} {g : F₂.Carrier → F₃.Carrier}
           where
    open FumulaMorphisms

    isFumulaHomomorphism : IsFumulaHomomorphism F₁ F₂ f → IsFumulaHomomorphism F₂ F₃ g
                               → IsFumulaHomomorphism F₁ F₃ (g ∘ f)
    isFumulaHomomorphism f-homo g-homo = record
      { isAlmostFumulaHomomorphism = isAlmostFumulaHomomorphism ≈₃-trans f.isAlmostFumulaHomomorphism g.isAlmostFumulaHomomorphism
      ; ■-homo = ≈₃-trans (g.⟦⟧-cong f.■-homo) g.■-homo
      }
      where
        module f = IsFumulaHomomorphism f-homo
        module g = IsFumulaHomomorphism g-homo

    isFumulaMonomorphism : IsFumulaMonomorphism F₁ F₂ f → IsFumulaMonomorphism F₂ F₃ g
                               → IsFumulaMonomorphism F₁ F₃ (g ∘ f)
    isFumulaMonomorphism f-mono g-mono = record
      { isFumulaHomomorphism = isFumulaHomomorphism f.isFumulaHomomorphism g.isFumulaHomomorphism
      ; injective = f.injective ∘ g.injective
      }
      where
        module f = IsFumulaMonomorphism f-mono
        module g = IsFumulaMonomorphism g-mono

    isFumulaIsomorphism : IsFumulaIsomorphism F₁ F₂ f → IsFumulaIsomorphism F₂ F₃ g
                               → IsFumulaIsomorphism F₁ F₃ (g ∘ f)
    isFumulaIsomorphism f-iso g-iso = record
      { isFumulaMonomorphism = isFumulaMonomorphism f.isFumulaMonomorphism g.isFumulaMonomorphism
      ; surjective = Comp.surjective F₁._≈_ F₂._≈_ F₃._≈_ f.surjective g.surjective
      }
      where
        module f = IsFumulaIsomorphism f-iso
        module g = IsFumulaIsomorphism g-iso
