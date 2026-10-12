module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Source.Exact.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Iteration.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual cone boundary gives the next exact position on maps into
every object of the original source, using the actual Puppe comparison. -/
theorem source_coneBoundary_exact
    {X Y : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    (hY : IsCubicallyCofibrant Y) (f : X ⟶ Y)
    (A : SourceCategory.{u}) (a : sourceLocalization.obj (cone f) ⟶ A) :
    sourceLocalization.map (coneInclusion f) ≫ a = 0 ↔
      ∃ b : sourceLocalization.obj X.suspension ⟶ A,
        sourceLocalization.map (coneBoundary f) ≫ b = a := by
  letI := stableEquivalences.Q_inverts _ (coneIterationComparison_stableEquivalence f)
  rw [source_coneInclusion_exact hY (hX.cone hY f) (coneInclusion f) A a]
  have h : sourceLocalization.map (coneInclusion (coneInclusion f)) ≫
      sourceLocalization.map (coneIterationComparison f) = sourceLocalization.map (coneBoundary f) := by
    rw [← sourceLocalization.map_comp, coneIterationComparison_inclusion]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨inv (sourceLocalization.map (coneIterationComparison f)) ≫ b, ?_⟩
    rw [← h, Category.assoc, IsIso.hom_inv_id_assoc]
    exact hb
  · rintro ⟨b, hb⟩
    refine ⟨sourceLocalization.map (coneIterationComparison f) ≫ b, ?_⟩
    rw [← Category.assoc, h, hb]

/-- The two displayed consecutive positions of the literal Puppe
sequence are exact on the actual additive source hom groups. -/
theorem source_coneBoundary_hom_exact
    {X Y : Prespectrum.{u}} (hX : IsCubicallyCofibrant X)
    (hY : IsCubicallyCofibrant Y) (f : X ⟶ Y) (A : SourceCategory.{u}) :
    Function.Exact (Preadditive.leftComp A (sourceLocalization.map (coneBoundary f)))
      (Preadditive.leftComp A (sourceLocalization.map (coneInclusion f))) :=
  source_coneBoundary_exact hX hY f A

end KIP126.StableHomotopy.Implementation.Prespectrum
