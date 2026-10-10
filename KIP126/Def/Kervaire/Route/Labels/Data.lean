import KIP126.Def.ClassicalAdams.SphereClasses.Hi.Internal.Data
import KIP126.Def.ClassicalAdams.SphereClasses.Product.Data

/-! Names needed by Proposition 7.8. The four nonstandard generators are
elements of the same actual classical E₂ page. Their CSV identification is
C(M), not a field asserting any differential, independence or survival.
`U`, `W`, `target` below are expressions, not additional arbitrary elements. -/
namespace KIP126.Kervaire.Route
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology KIP126.Classical.Adams
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  (H : Mod2EilenbergMacLane (C := C))

noncomputable abbrev E2 (X : C) (s t : ℤ) :=
  (adamsTowerInternalSpectralSequence H.unit X).Page 2 (s, t)

structure Labels where
  x_126_8_4 : E2 H SphereSpectrum 8 134
  x_126_8 : E2 H SphereSpectrum 8 134
  x_124_8 : E2 H SphereSpectrum 8 132
  x_109_12 : E2 H SphereSpectrum 12 121

namespace Labels
noncomputable section
variable {H} (L : Labels H) (M : MilnorCooperations H)
def W : E2 H SphereSpectrum 8 134 := L.x_126_8_4 + L.x_126_8
def U : E2 H SphereSpectrum 10 134 :=
  Sphere.Internal.product H M (s := 2) (t := 2) (s' := 8) (t' := 132)
    (Sphere.Internal.hiSquare H M 0) L.x_124_8
def target : E2 H SphereSpectrum 14 139 :=
  Sphere.Internal.product H M (s := 2) (t := 18) (s' := 12) (t' := 121)
    (Sphere.Internal.product H M (s := 1) (t := 2) (s' := 1) (t' := 16)
      (Sphere.Internal.hi H M 1) (Sphere.Internal.hi H M 4)) L.x_109_12
end
end Labels
end KIP126.Kervaire.Route
