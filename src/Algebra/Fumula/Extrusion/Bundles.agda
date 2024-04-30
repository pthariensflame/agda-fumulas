------------------------------------------------------------------------
-- Definitions of fumula extrusions (bundled).
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Bundles where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Algebra.Fumula.Bundles
open import Algebra.Fumula.Extrusion.Core
open import Algebra.Fumula.Extrusion.Definitions
open import Algebra.Fumula.Extrusion.Structures

private
  variable
    f ℓf fₗ ℓfₗ fᵣ ℓfᵣ : Level

module _ (F : AlmostFumula f ℓf) where
  private
    module F = AlmostFumula F

  record LeftAlmostFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      isLeftAlmostFumulaExtrusion : IsLeftAlmostFumulaExtrusion F _≈_ ❲_❳⤙_⤚_
    open IsLeftAlmostFumulaExtrusion isLeftAlmostFumulaExtrusion public

  record RightAlmostFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      isRightAlmostFumulaExtrusion : IsRightAlmostFumulaExtrusion F _≈_ _⤙_⤚❲_❳
    open IsRightAlmostFumulaExtrusion isRightAlmostFumulaExtrusion public

module _ (Fₗ : AlmostFumula fₗ ℓfₗ) (Fᵣ : AlmostFumula fᵣ ℓfᵣ) where
  private
    module Fₗ = AlmostFumula Fₗ
    module Fᵣ = AlmostFumula Fᵣ

  record BiAlmostFumulaExtrusion (x ℓx : Level) : Set (fₗ ⊔ fᵣ ⊔ suc x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ suc ℓx) where
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ Fₗ.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ Fᵣ.Carrier Carrier
      isBiAlmostFumulaExtrusion : IsBiAlmostFumulaExtrusion Fₗ Fᵣ _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
    open IsBiAlmostFumulaExtrusion isBiAlmostFumulaExtrusion public

    ❲❳⤙⤚-leftAlmostFumulaExtrusion : LeftAlmostFumulaExtrusion Fₗ x ℓx
    ❲❳⤙⤚-leftAlmostFumulaExtrusion = record { isLeftAlmostFumulaExtrusion = ❲❳⤙⤚-isLeftAlmostFumulaExtrusion }

    ⤙⤚❲❳-rightAlmostFumulaExtrusion : RightAlmostFumulaExtrusion Fᵣ x ℓx
    ⤙⤚❲❳-rightAlmostFumulaExtrusion = record { isRightAlmostFumulaExtrusion = ⤙⤚❲❳-isRightAlmostFumulaExtrusion }

module _ (F : AlmostFumula f ℓf) where
  private
    module F = AlmostFumula F

  record AlmostFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      isAlmostFumulaExtrusion : IsAlmostFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
    open IsAlmostFumulaExtrusion isAlmostFumulaExtrusion public

    biAlmostFumulaExtrusion : BiAlmostFumulaExtrusion F F x ℓx
    biAlmostFumulaExtrusion = record { isBiAlmostFumulaExtrusion = isBiAlmostFumulaExtrusion }
    open BiAlmostFumulaExtrusion biAlmostFumulaExtrusion public
      using (❲❳⤙⤚-leftAlmostFumulaExtrusion; ⤙⤚❲❳-rightAlmostFumulaExtrusion)

module _ (F : ReversibleAlmostFumula f ℓf) where
  private
    module F = ReversibleAlmostFumula F

  record ReversibleAlmostFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      isReversibleAlmostFumulaExtrusion : IsReversibleAlmostFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳
    open IsReversibleAlmostFumulaExtrusion isReversibleAlmostFumulaExtrusion public

    almostFumulaExtrusion : AlmostFumulaExtrusion F.almostFumula x ℓx
    almostFumulaExtrusion = record { isAlmostFumulaExtrusion = isAlmostFumulaExtrusion }
    open AlmostFumulaExtrusion almostFumulaExtrusion public
      using (❲❳⤙⤚-leftAlmostFumulaExtrusion; ⤙⤚❲❳-rightAlmostFumulaExtrusion;
             biAlmostFumulaExtrusion)

module _ (F : Fumula f ℓf) where
  private
    module F = Fumula F

  record LeftFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      ◆ : Carrier
      isLeftFumulaExtrusion : IsLeftFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ ◆
    open IsLeftFumulaExtrusion isLeftFumulaExtrusion public

    ❲❳⤙⤚-leftAlmostFumulaExtrusion : LeftAlmostFumulaExtrusion F.almostFumula x ℓx
    ❲❳⤙⤚-leftAlmostFumulaExtrusion = record { isLeftAlmostFumulaExtrusion = ❲❳⤙⤚-isLeftAlmostFumulaExtrusion }

  record RightFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      ◆ : Carrier
      isRightFumulaExtrusion : IsRightFumulaExtrusion F _≈_ _⤙_⤚❲_❳ ◆
    open IsRightFumulaExtrusion isRightFumulaExtrusion public

    ⤙⤚❲❳-rightAlmostFumulaExtrusion : RightAlmostFumulaExtrusion F.almostFumula x ℓx
    ⤙⤚❲❳-rightAlmostFumulaExtrusion = record { isRightAlmostFumulaExtrusion = ⤙⤚❲❳-isRightAlmostFumulaExtrusion }

module _ (Fₗ : Fumula fₗ ℓfₗ) (Fᵣ : Fumula fᵣ ℓfᵣ) where
  private
    module Fₗ = Fumula Fₗ
    module Fᵣ = Fumula Fᵣ

  record BiFumulaExtrusion (x ℓx : Level) : Set (fₗ ⊔ fᵣ ⊔ suc x ⊔ ℓfₗ ⊔ ℓfᵣ ⊔ suc ℓx) where
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ Fₗ.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ Fᵣ.Carrier Carrier
      ◆ : Carrier
      isBiFumulaExtrusion : IsBiFumulaExtrusion Fₗ Fᵣ _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
    open IsBiFumulaExtrusion isBiFumulaExtrusion public

    ❲❳⤙⤚-leftFumulaExtrusion : LeftFumulaExtrusion Fₗ x ℓx
    ❲❳⤙⤚-leftFumulaExtrusion = record { isLeftFumulaExtrusion = ❲❳⤙⤚-isLeftFumulaExtrusion }
    open LeftFumulaExtrusion ❲❳⤙⤚-leftFumulaExtrusion public
      using (❲❳⤙⤚-leftAlmostFumulaExtrusion)

    ⤙⤚❲❳-rightFumulaExtrusion : RightFumulaExtrusion Fᵣ x ℓx
    ⤙⤚❲❳-rightFumulaExtrusion = record { isRightFumulaExtrusion = ⤙⤚❲❳-isRightFumulaExtrusion }
    open RightFumulaExtrusion ⤙⤚❲❳-rightFumulaExtrusion public
      using (⤙⤚❲❳-rightAlmostFumulaExtrusion)

    biAlmostFumulaExtrusion : BiAlmostFumulaExtrusion Fₗ.almostFumula Fᵣ.almostFumula x ℓx
    biAlmostFumulaExtrusion = record { isBiAlmostFumulaExtrusion = isBiAlmostFumulaExtrusion }

module _ (F : Fumula f ℓf) where
  private
    module F = Fumula F

  record FumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      ◆ : Carrier
      isFumulaExtrusion : IsFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
    open IsFumulaExtrusion isFumulaExtrusion public

    biFumulaExtrusion : BiFumulaExtrusion F F x ℓx
    biFumulaExtrusion = record { isBiFumulaExtrusion = isBiFumulaExtrusion }
    open BiFumulaExtrusion biFumulaExtrusion public
      using (❲❳⤙⤚-leftFumulaExtrusion; ⤙⤚❲❳-rightFumulaExtrusion;
             ❲❳⤙⤚-leftAlmostFumulaExtrusion; ⤙⤚❲❳-rightAlmostFumulaExtrusion;
             biAlmostFumulaExtrusion)

    almostFumulaExtrusion : AlmostFumulaExtrusion F.almostFumula x ℓx
    almostFumulaExtrusion = record { isAlmostFumulaExtrusion = isAlmostFumulaExtrusion }

module _ (F : ReversibleFumula f ℓf) where
  private
    module F = ReversibleFumula F

  record ReversibleFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ ℓf ⊔ suc ℓx) where
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      ◆ : Carrier
      isReversibleFumulaExtrusion : IsReversibleFumulaExtrusion F _≈_ ❲_❳⤙_⤚_ _⤙_⤚❲_❳ ◆
    open IsReversibleFumulaExtrusion isReversibleFumulaExtrusion public

    fumulaExtrusion : FumulaExtrusion F.fumula x ℓx
    fumulaExtrusion = record { isFumulaExtrusion = isFumulaExtrusion }
    open FumulaExtrusion fumulaExtrusion public
      using (❲❳⤙⤚-leftFumulaExtrusion; ⤙⤚❲❳-rightFumulaExtrusion;
             ❲❳⤙⤚-leftAlmostFumulaExtrusion; ⤙⤚❲❳-rightAlmostFumulaExtrusion;
             biFumulaExtrusion; biAlmostFumulaExtrusion; almostFumulaExtrusion)
