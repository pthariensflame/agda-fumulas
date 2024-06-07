------------------------------------------------------------------------
-- Raw bundles for fumula extrusions.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Bundles.Raw where

open import Level using (Level; _⊔_; suc)
open import Relation.Binary.Core using (Rel)
open import Algebra.Fumula.Bundles.Raw
open import Algebra.Fumula.Extrusion.Core

private
  variable
    f ℓf fₗ ℓfₗ fᵣ ℓfᵣ : Level

module _ (F : RawAlmostFumula f ℓf) where
  private
    module F = RawAlmostFumula F

  record RawLeftAlmostFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier

  record RawRightAlmostFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ suc ℓx) where
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier

module _ (Fₗ : RawAlmostFumula fₗ ℓfₗ) (Fᵣ : RawAlmostFumula fᵣ ℓfᵣ) where
  private
    module Fₗ = RawAlmostFumula Fₗ
    module Fᵣ = RawAlmostFumula Fᵣ

  record RawDoubleAlmostFumulaExtrusion (x ℓx : Level) : Set (fₗ ⊔ fᵣ ⊔ suc x ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ Fₗ.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ Fᵣ.Carrier Carrier

    ❲❳⤙⤚-rawLeftAlmostFumulaExtrusion : RawLeftAlmostFumulaExtrusion Fₗ x ℓx
    ❲❳⤙⤚-rawLeftAlmostFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; ❲_❳⤙_⤚_ = ❲_❳⤙_⤚_
      }

    ⤙⤚❲❳-rawRightAlmostFumulaExtrusion : RawRightAlmostFumulaExtrusion Fᵣ x ℓx
    ⤙⤚❲❳-rawRightAlmostFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _⤙_⤚❲_❳ = _⤙_⤚❲_❳
      }

module _ (F : RawAlmostFumula f ℓf) where
  private
    module F = RawAlmostFumula F

  record RawAlmostFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier

    rawDoubleAlmostFumulaExtrusion : RawDoubleAlmostFumulaExtrusion F F x ℓx
    rawDoubleAlmostFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; ❲_❳⤙_⤚_ = ❲_❳⤙_⤚_
      ; _⤙_⤚❲_❳ = _⤙_⤚❲_❳
      }
    open RawDoubleAlmostFumulaExtrusion rawDoubleAlmostFumulaExtrusion public
      using (❲❳⤙⤚-rawLeftAlmostFumulaExtrusion; ⤙⤚❲❳-rawRightAlmostFumulaExtrusion)

module _ (F : RawFumula f ℓf) where
  private
    module F = RawFumula F

  record RawLeftFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      ◆ : Carrier

    rawLeftAlmostFumulaExtrusion : RawLeftAlmostFumulaExtrusion F.rawAlmostFumula x ℓx
    rawLeftAlmostFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; ❲_❳⤙_⤚_ = ❲_❳⤙_⤚_
      }

  record RawRightFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ suc ℓx) where
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      ◆ : Carrier

    rawRightAlmostFumulaExtrusion : RawRightAlmostFumulaExtrusion F.rawAlmostFumula x ℓx
    rawRightAlmostFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _⤙_⤚❲_❳ = _⤙_⤚❲_❳
      }

module _ (Fₗ : RawFumula fₗ ℓfₗ) (Fᵣ : RawFumula fᵣ ℓfᵣ) where
  private
    module Fₗ = RawFumula Fₗ
    module Fᵣ = RawFumula Fᵣ

  record RawDoubleFumulaExtrusion (x ℓx : Level) : Set (fₗ ⊔ fᵣ ⊔ suc x ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ Fₗ.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ Fᵣ.Carrier Carrier
      ◆ : Carrier

    ❲❳⤙⤚-rawLeftFumulaExtrusion : RawLeftFumulaExtrusion Fₗ x ℓx
    ❲❳⤙⤚-rawLeftFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; ❲_❳⤙_⤚_ = ❲_❳⤙_⤚_
      ; ◆ = ◆
      }
    open RawLeftFumulaExtrusion ❲❳⤙⤚-rawLeftFumulaExtrusion public
      using () renaming (rawLeftAlmostFumulaExtrusion to ❲❳⤙⤚-rawLeftAlmostFumulaExtrusion)

    ⤙⤚❲❳-rawRightFumulaExtrusion : RawRightFumulaExtrusion Fᵣ x ℓx
    ⤙⤚❲❳-rawRightFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; _⤙_⤚❲_❳ = _⤙_⤚❲_❳
      ; ◆ = ◆
      }
    open RawRightFumulaExtrusion ⤙⤚❲❳-rawRightFumulaExtrusion public
      using () renaming (rawRightAlmostFumulaExtrusion to ⤙⤚❲❳-rawRightAlmostFumulaExtrusion)

    rawDoubleAlmostFumulaExtrusion : RawDoubleAlmostFumulaExtrusion Fₗ.rawAlmostFumula Fᵣ.rawAlmostFumula x ℓx
    rawDoubleAlmostFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; ❲_❳⤙_⤚_ = ❲_❳⤙_⤚_
      ; _⤙_⤚❲_❳ = _⤙_⤚❲_❳
      }

module _ (F : RawFumula f ℓf) where
  private
    module F = RawFumula F

  record RawFumulaExtrusion (x ℓx : Level) : Set (f ⊔ suc x ⊔ suc ℓx) where
    infix 7 ❲_❳⤙_⤚_
    infix 7 _⤙_⤚❲_❳
    infix 4 _≈_
    field
      Carrier : Set x
      _≈_ : Rel Carrier ℓx
      ❲_❳⤙_⤚_ : Op₃ₗ F.Carrier Carrier
      _⤙_⤚❲_❳ : Op₃ᵣ F.Carrier Carrier
      ◆ : Carrier

    rawDoubleFumulaExtrusion : RawDoubleFumulaExtrusion F F x ℓx
    rawDoubleFumulaExtrusion = record
      { Carrier = Carrier
      ; _≈_ = _≈_
      ; ❲_❳⤙_⤚_ = ❲_❳⤙_⤚_
      ; _⤙_⤚❲_❳ = _⤙_⤚❲_❳
      ; ◆ = ◆
      }
    open RawDoubleFumulaExtrusion rawDoubleFumulaExtrusion public
      using (❲❳⤙⤚-rawLeftFumulaExtrusion; ❲❳⤙⤚-rawLeftAlmostFumulaExtrusion;
             ⤙⤚❲❳-rawRightFumulaExtrusion; ⤙⤚❲❳-rawRightAlmostFumulaExtrusion;
             rawDoubleAlmostFumulaExtrusion)
