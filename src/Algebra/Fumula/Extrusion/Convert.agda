------------------------------------------------------------------------
-- Conversion of fumula extrusions to and from modules over rings.
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Algebra.Fumula.Extrusion`.

module Algebra.Fumula.Extrusion.Convert where

open import Data.Product using (_,_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Algebra.Fumula.Bundles
open import Algebra.Fumula.Extrusion.Structures
open import Algebra.Fumula.Extrusion.Bundles

module FromModule where

module FromFumulaExtrusion where
