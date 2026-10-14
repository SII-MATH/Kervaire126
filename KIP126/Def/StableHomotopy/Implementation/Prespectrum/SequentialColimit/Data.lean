module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Bond

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The actual sequential colimit prespectrum, with its constructed continuous bonds. -/
noncomputable def sequentialColimit (F : ℕ ⥤ Prespectrum.{u}) : Prespectrum.{u} where
  level := sequentialColimitLevel F
  bond := sequentialColimitBond F
  bond_point := sequentialColimitBond_point F
  bond_zero := sequentialColimitBond_zero F
  bond_one := sequentialColimitBond_one F

/-- Every actual stage maps strictly into the constructed colimit prespectrum. -/
noncomputable def sequentialColimitInclusion (F : ℕ ⥤ Prespectrum.{u}) (k : ℕ) :
    F.obj k ⟶ sequentialColimit F where
  level n := sequentialColimitLevelInclusion F n k
  point n := sequentialColimitLevelInclusion_point F n k
  bond n x t := (sequentialColimitBond_inclusion F n k x t).symm

/-- The actual sequential colimit cocone in strict prespectra. -/
noncomputable def sequentialColimitCocone (F : ℕ ⥤ Prespectrum.{u}) : Cocone F where
  pt := sequentialColimit F
  ι :=
    { app := sequentialColimitInclusion F
      naturality := fun k l h => by
        apply Hom.ext
        funext n
        apply ContinuousMap.ext
        intro x
        exact sequentialColimitLevelInclusion_map F n h x }

/-- The actual level cocone determined by any cocone of strict prespectra. -/
def sequentialCoconeLevel {F : ℕ ⥤ Prespectrum.{u}} (c : Cocone F) (n : ℕ) :
    Cocone (sequentialLevelDiagram F n) where
  pt := (c.pt.level n).space
  ι :=
    { app := fun k => TopCat.ofHom ((c.ι.app k).level n)
      naturality := fun k l h => by
        apply ConcreteCategory.hom_ext
        intro x
        exact congrArg (fun f => f.level n x) (c.w h) }

/-- Descent into any cocone, constructed with the actual topological level colimits. -/
noncomputable def sequentialColimitDesc {F : ℕ ⥤ Prespectrum.{u}} (c : Cocone F) :
    sequentialColimit F ⟶ c.pt where
  level n := (colimit.desc (sequentialLevelDiagram F n) (sequentialCoconeLevel c n)).hom
  point n := by
    have h := ConcreteCategory.congr_hom
      (colimit.ι_desc (sequentialCoconeLevel c n) 0)
      ((F.obj 0).level n).point
    exact h.trans ((c.ι.app 0).point n)
  bond n x t := by
    obtain ⟨k, y, rfl⟩ := sequentialColimitLevelInclusion_jointly_surjective F n x
    change (colimit.desc (sequentialLevelDiagram F (n+1)) (sequentialCoconeLevel c (n+1)))
      (sequentialColimitBond F n (sequentialColimitLevelInclusion F n k y, t)) = _
    rw [sequentialColimitBond_inclusion]
    have h (n : ℕ) (z : (F.obj k).level n) := ConcreteCategory.congr_hom
      (colimit.ι_desc (sequentialCoconeLevel c n) k) z
    exact (h (n+1) ((F.obj k).bond n (y, t))).trans
      (((c.ι.app k).bond n y t).trans
        (congrArg (fun z => c.pt.bond n (z, t)) (h n y).symm))

end KIP126.StableHomotopy.Implementation.Prespectrum
