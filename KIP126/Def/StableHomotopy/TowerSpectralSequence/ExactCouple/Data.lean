import KIP126.Def.StableHomotopy.DescendingTower.Layer.Data
import KIP126.Def.StableHomotopy.RepresentedHom.Data

/-! The actual exact-couple arrows of a descending tower, tested against
ordinary suspensions of a specified object. Exactness is a property of the
cofiber triangles, not an independently supplied exact-couple witness. -/

namespace KIP126.StableHomotopy.TowerSpectralSequence

open CategoryTheory

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

/-- The first-page representatives, before any differential is discarded. -/
abbrev E1 (k n : ℤ) := ShiftedHom P n (T.layer k)

/-- The actual composite of adjacent tower arrows on represented Hom. -/
noncomputable def I (n s t : ℤ) (h : s ≤ t) :
    ShiftedHom P n (T.obj t) →ₗ[ℤ] ShiftedHom P n (T.obj s) :=
  postcomposeLinearMap P n (T.map s t h)

/-- The actual layer inclusion on represented Hom. -/
noncomputable def J (k n : ℤ) :
    ShiftedHom P n (T.obj k) →ₗ[ℤ] E1 T P k n :=
  postcomposeLinearMap P n (T.layerIncl k)

/-- The actual layer boundary with its ordinary suspension transport. -/
noncomputable def K (k n : ℤ) :
    E1 T P k n →ₗ[ℤ] ShiftedHom P (n - 1) (T.obj (k + 1)) :=
  connectingLinearMap P (T.layerCofiberSequence k) n

end KIP126.StableHomotopy.TowerSpectralSequence
