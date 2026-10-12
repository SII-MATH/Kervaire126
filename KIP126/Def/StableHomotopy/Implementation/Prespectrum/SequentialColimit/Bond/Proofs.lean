module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Bond.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual colimit bond agrees exactly with each original stage bond. -/
theorem sequentialColimitBond_inclusion (F : ℕ ⥤ Prespectrum.{u}) (n k : ℕ)
    (x : (F.obj k).level n) (t : I) :
    sequentialColimitBond F n (sequentialColimitLevelInclusion F n k x, t) =
      sequentialColimitLevelInclusion F (n+1) k ((F.obj k).bond n (x, t)) :=
  congrArg (fun f : C(I, sequentialColimitLevel F (n+1)) => f t)
    (ConcreteCategory.congr_hom
      (colimit.ι_desc (sequentialColimitBondCocone F n) k) x)

theorem sequentialColimitBond_point (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ) (t : I) :
    sequentialColimitBond F n ((sequentialColimitLevel F n).point, t) =
      (sequentialColimitLevel F (n+1)).point := by
  change sequentialColimitBond F n
    (sequentialColimitLevelInclusion F n 0 ((F.obj 0).level n).point, t) = _
  rw [sequentialColimitBond_inclusion, (F.obj 0).bond_point]
  rfl

theorem sequentialColimitBond_zero (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ)
    (x : sequentialColimitLevel F n) :
    sequentialColimitBond F n (x, 0) = (sequentialColimitLevel F (n+1)).point := by
  obtain ⟨k, y, rfl⟩ := sequentialColimitLevelInclusion_jointly_surjective F n x
  rw [sequentialColimitBond_inclusion, (F.obj k).bond_zero, sequentialColimitLevelInclusion_point]

theorem sequentialColimitBond_one (F : ℕ ⥤ Prespectrum.{u}) (n : ℕ)
    (x : sequentialColimitLevel F n) :
    sequentialColimitBond F n (x, 1) = (sequentialColimitLevel F (n+1)).point := by
  obtain ⟨k, y, rfl⟩ := sequentialColimitLevelInclusion_jointly_surjective F n x
  rw [sequentialColimitBond_inclusion, (F.obj k).bond_one, sequentialColimitLevelInclusion_point]

end KIP126.StableHomotopy.Implementation.Prespectrum
