------------------------------------------------------------------------
-- Definitions of fumula extrusions (bundled).
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Bundles where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
open import Algebra.Fumula.Bundles
open import Algebra.Fumula.Extrusion.Core
open import Algebra.Fumula.Extrusion.Definitions
open import Algebra.Fumula.Extrusion.Structures
open import Algebra.Fumula.Extrusion.Bundles.Raw public

private
  variable
    f ℓf fₗ ℓfₗ fᵣ ℓfᵣ : Level

module _ (F : AlmostFumula f ℓf) where
  private
    module F = AlmostFumula F

  record LeftAlmostFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      isLeftAlmostFumulaExtrusion : IsLeftAlmostFumulaExtrusion F _≈_ ❲_❳⤙_⤚_
    open IsLeftAlmostFumulaExtrusion isLeftAlmostFumulaExtrusion public

    setoid : Setoid x ℓx
    setoid = record { isEquivalence = isEquivalence }

  record RightAlmostFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      isRightAlmostFumulaExtrusion : IsRightAlmostFumulaExtrusion F _≈_ _⤙_⤚❲_❳
    open IsRightAlmostFumulaExtrusion isRightAlmostFumulaExtrusion public

    setoid : Setoid x ℓx
    setoid = record { isEquivalence = isEquivalence }

module _ (Fₗ : AlmostFumula fₗ ℓfₗ) (Fᵣ : AlmostFumula fᵣ ℓfᵣ) where
  private
    module Fₗ = AlmostFumula Fₗ
    module Fᵣ = AlmostFumula Fᵣ

  record DoubleAlmostFumulaExtrusion (x ℓx : Level) : Set (fₗ ⊔ fᵣ ⊔ suc x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ Fₗ.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ Fᵣ.Carrier Carrier
      isDoubleAlmostFumulaExtrusion : IsDoubleAlmostFumulaExtrusion Fₗ Fᵣ _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
    open IsDoubleAlmostFumulaExtrusion isDoubleAlmostFumulaExtrusion public

    ❲❳⤙⤚-leftAlmostFumulaExtrusion : LeftAlmostFumulaExtrusion Fₗ x ℓx
    ❲❳⤙⤚-leftAlmostFumulaExtrusion = record { isLeftAlmostFumulaExtrusion = ❲❳⤙⤚-isLeftAlmostFumulaExtrusion }
    open LeftAlmostFumulaExtrusion ❲❳⤙⤚-leftAlmostFumulaExtrusion public
      using (setoid)

    ⤙⤚❲❳-rightAlmostFumulaExtrusion : RightAlmostFumulaExtrusion Fᵣ x ℓx
    ⤙⤚❲❳-rightAlmostFumulaExtrusion = record { isRightAlmostFumulaExtrusion = ⤙⤚❲❳-isRightAlmostFumulaExtrusion }

module _ (F : ReversibleAlmostFumula f ℓf) where
  private
    module F = ReversibleAlmostFumula F

  record AlmostFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      isAlmostFumulaExtrusion : IsAlmostFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
    open IsAlmostFumulaExtrusion isAlmostFumulaExtrusion public

    doubleAlmostFumulaExtrusion : DoubleAlmostFumulaExtrusion F.almostFumula F.almostFumula x ℓx
    doubleAlmostFumulaExtrusion = record { isDoubleAlmostFumulaExtrusion = isDoubleAlmostFumulaExtrusion }
    open DoubleAlmostFumulaExtrusion doubleAlmostFumulaExtrusion public
      using (❲❳⤙⤚-leftAlmostFumulaExtrusion; ⤙⤚❲❳-rightAlmostFumulaExtrusion; setoid)

module _ (F : Fumula f ℓf) where
  private
    module F = Fumula F

  record LeftFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      ◆ : Carrier
      isLeftFumulaExtrusion : IsLeftFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ ◆
    open IsLeftFumulaExtrusion isLeftFumulaExtrusion public

    leftAlmostFumulaExtrusion : LeftAlmostFumulaExtrusion F.almostFumula x ℓx
    leftAlmostFumulaExtrusion = record { isLeftAlmostFumulaExtrusion = isLeftAlmostFumulaExtrusion }
    open LeftAlmostFumulaExtrusion leftAlmostFumulaExtrusion public
      using (setoid)

  record RightFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      ◆ : Carrier
      isRightFumulaExtrusion : IsRightFumulaExtrusion F _≈_ _⤙_⤚❲_❳ ◆
    open IsRightFumulaExtrusion isRightFumulaExtrusion public

    rightAlmostFumulaExtrusion : RightAlmostFumulaExtrusion F.almostFumula x ℓx
    rightAlmostFumulaExtrusion = record { isRightAlmostFumulaExtrusion = isRightAlmostFumulaExtrusion }
    open RightAlmostFumulaExtrusion rightAlmostFumulaExtrusion public
      using (setoid)

module _ (Fₗ : Fumula fₗ ℓfₗ) (Fᵣ : Fumula fᵣ ℓfᵣ) where
  private
    module Fₗ = Fumula Fₗ
    module Fᵣ = Fumula Fᵣ

  record DoubleFumulaExtrusion (x ℓx : Level) : Set (fₗ ⊔ fᵣ ⊔ suc x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ Fₗ.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ Fᵣ.Carrier Carrier
      ◆ : Carrier
      isDoubleFumulaExtrusion : IsDoubleFumulaExtrusion Fₗ Fᵣ _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
    open IsDoubleFumulaExtrusion isDoubleFumulaExtrusion public

    ❲❳⤙⤚-leftFumulaExtrusion : LeftFumulaExtrusion Fₗ x ℓx
    ❲❳⤙⤚-leftFumulaExtrusion = record { isLeftFumulaExtrusion = ❲❳⤙⤚-isLeftFumulaExtrusion }
    open LeftFumulaExtrusion ❲❳⤙⤚-leftFumulaExtrusion public
      using (setoid) renaming (leftAlmostFumulaExtrusion to ❲❳⤙⤚-leftAlmostFumulaExtrusion)

    ⤙⤚❲❳-rightFumulaExtrusion : RightFumulaExtrusion Fᵣ x ℓx
    ⤙⤚❲❳-rightFumulaExtrusion = record { isRightFumulaExtrusion = ⤙⤚❲❳-isRightFumulaExtrusion }
    open RightFumulaExtrusion ⤙⤚❲❳-rightFumulaExtrusion public
      using () renaming (rightAlmostFumulaExtrusion to ⤙⤚❲❳-rightAlmostFumulaExtrusion)

    doubleAlmostFumulaExtrusion : DoubleAlmostFumulaExtrusion Fₗ.almostFumula Fᵣ.almostFumula x ℓx
    doubleAlmostFumulaExtrusion = record { isDoubleAlmostFumulaExtrusion = isDoubleAlmostFumulaExtrusion }

module _ (F : ReversibleFumula f ℓf) where
  private
    module F = ReversibleFumula F

  record FumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      ◆ : Carrier
      isFumulaExtrusion : IsFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
    open IsFumulaExtrusion isFumulaExtrusion public

    doubleFumulaExtrusion : DoubleFumulaExtrusion F.fumula F.fumula x ℓx
    doubleFumulaExtrusion = record { isDoubleFumulaExtrusion = isDoubleFumulaExtrusion }
    open DoubleFumulaExtrusion doubleFumulaExtrusion public
      using (❲❳⤙⤚-leftFumulaExtrusion;
             ⤙⤚❲❳-rightFumulaExtrusion;
             ❲❳⤙⤚-leftAlmostFumulaExtrusion;
             ⤙⤚❲❳-rightAlmostFumulaExtrusion;
             doubleAlmostFumulaExtrusion)

    almostFumulaExtrusion : AlmostFumulaExtrusion F.reversibleAlmostFumula x ℓx
    almostFumulaExtrusion = record { isAlmostFumulaExtrusion = isAlmostFumulaExtrusion }
