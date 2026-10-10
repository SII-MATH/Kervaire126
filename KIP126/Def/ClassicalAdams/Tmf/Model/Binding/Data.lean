import KIP126.Def.ClassicalAdams.Tmf.Model.Data
import Mathlib.CategoryTheory.Monoidal.Mon
/-!
# Chosen tmf algebra and coordinates

These are parameterized mathematical definitions, independent of fixed program data
and stage witnesses. Existing public declaration names are preserved.
-/

namespace KIP126.Challenge2

open CategoryTheory CategoryTheory.MonoidalCategory
open Classical.Adams Core.SpectralSequence

universe u v w

/-- The chosen algebra object and fixed tmf coordinates, before the BR21 claim. -/
structure TmfModel {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    (H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C)) where
  target : Mon C
  coordinates : Tmf.E2Presentation H target

end KIP126.Challenge2
