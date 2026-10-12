module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Level.Data
public import Mathlib.CategoryTheory.Limits.Types.Filtered

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

theorem sequentialColimitLevelInclusion_map (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ)
    {k l : ℕ} (h : k ⟶ l) (x : (F.obj k).level n) :
    sequentialColimitLevelInclusion F n l ((F.map h).level n x) =
      sequentialColimitLevelInclusion F n k x :=
  ConcreteCategory.congr_hom (colimit.w (sequentialLevelDiagram F n) h) x

theorem sequentialColimitLevelInclusion_point (F : ℕ ⥤ Prespectrum.{u}) (n k : ℕ) :
    sequentialColimitLevelInclusion F n k ((F.obj k).level n).point =
      (sequentialColimitLevel F n).point := by
  rw [← (F.map (homOfLE (Nat.zero_le k))).point n]
  exact sequentialColimitLevelInclusion_map F n _ _

/-- Every point of an actual level colimit comes from an actual stage. -/
theorem sequentialColimitLevelInclusion_jointly_surjective (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ)
    (x : sequentialColimitLevel F n) :
    ∃ k, ∃ y : (F.obj k).level n, sequentialColimitLevelInclusion F n k y = x :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (colimit.isColimit (sequentialLevelDiagram F n))) x

end KIP126.StableHomotopy.Implementation.Prespectrum
