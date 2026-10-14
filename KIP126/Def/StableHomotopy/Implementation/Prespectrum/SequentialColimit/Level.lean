module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual spaces at a fixed level of a sequential diagram of prespectra. -/
def sequentialLevelDiagram (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) : ℕ ⥤ TopCat.{u} where
  obj k := (F.obj k).level n |>.space
  map h := TopCat.ofHom ((F.map h).level n)
  map_id k := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun f : F.obj k ⟶ F.obj k => f.level n x) (F.map_id k)
  map_comp h k := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun f => f.level n x) (F.map_comp h k)

/-- The actual topological colimit level, based at the common image of the
initial stage's basepoint. -/
noncomputable def sequentialColimitLevel (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) : BasedSpace.{u} where
  space := colimit (sequentialLevelDiagram F n)
  point := colimit.ι (sequentialLevelDiagram F n) 0 ((F.obj 0).level n).point

/-- The actual level inclusion into the displayed topological colimit. -/
noncomputable def sequentialColimitLevelInclusion (F : ℕ ⥤ Prespectrum.{u}) (n k : ℕ) :
    C((F.obj k).level n, sequentialColimitLevel F n) :=
  (colimit.ι (sequentialLevelDiagram F n) k).hom

end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

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

end
