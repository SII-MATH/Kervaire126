module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SequentialColimit.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency false

/-- The displayed actual sequential cocone satisfies the prespectrum colimit
universal property. No stability or convergence premise is used. -/
noncomputable def sequentialColimitCocone_isColimit (F : ℕ ⥤ Prespectrum.{u}) :
    IsColimit (sequentialColimitCocone F) where
  desc := sequentialColimitDesc
  fac c k := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact ConcreteCategory.congr_hom
      (colimit.ι_desc (sequentialCoconeLevel c n) k) x
  uniq c m hm := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    obtain ⟨k, y, rfl⟩ := sequentialColimitLevelInclusion_jointly_surjective F n x
    exact (congrArg (fun f => f.level n y) (hm k)).trans
      (ConcreteCategory.congr_hom
        (colimit.ι_desc (sequentialCoconeLevel c n) k) y).symm

instance prespectrumHasSequentialColimits : HasColimitsOfShape ℕ Prespectrum.{u} :=
  ⟨fun F => ⟨⟨sequentialColimitCocone F, sequentialColimitCocone_isColimit F⟩⟩⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
