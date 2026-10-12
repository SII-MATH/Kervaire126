module

public import KIP126.Def.StableHomotopy.Implementation.Realization.Cellular.AdjoinPoint.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Parameter.Cells.Finite.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Iso.Proofs
public import KIP126.Def.Topology.SimplicialRealization.FiniteSkeleton.Induction.Proofs
public import KIP126.Def.Topology.SimplicialRealization.CompactlyGenerated.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits Simplicial HomotopicalAlgebra
open KIP126.Topology.SimplicialRealization
set_option backward.isDefEq.respectTransparency false

/-- Smashing with the actual realization of a finite simplicial set,
with a disjoint specified point, preserves every stable equivalence of
the original spectra. No condition on their levels is imposed. -/
theorem spaceSmashMap_finiteRealization_adjoinPoint_stableEquivalence
    (K : SSet.{0}) [K.Finite] {X Y : Prespectrum.{0}}
    (f : X ⟶ Y) (hf : stableEquivalences f) :
    stableEquivalences (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (SSet.toTop.obj K))) f) := by
  let P (L : SSet.{0}) :=
    stableEquivalences (spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (SSet.toTop.obj L))) f)
  apply finite_simplicial_cellular_induction P ?_ ?_ ?_ K
  · intro L hL
    letI : IsEmpty (SSet.toTop.obj L) := ⟨fun x =>
      PEmpty.elim (((hL.isInitialObj SSet.toTop).to (TopCat.of PEmpty)) x)⟩
    let a := spaceSmashMap (𝟙 (BasedSpace.adjoinPoint (SSet.toTop.obj L))) f
    letI : IsIso a := (spaceSmash_adjoinPoint_isZero (SSet.toTop.obj L) X).isIso
      (spaceSmash_adjoinPoint_isZero (SSet.toTop.obj L) Y) a
    exact (stableEquivalence_iff_source_isIso a).mpr inferInstance
  · intro L M e hL
    exact (spaceSmashMap_stableEquivalence_iff_of_iso
      ((SSet.toTop ⋙ BasedSpace.adjoinPointFunctor).mapIso e) f).mp hL
  · intro n L M _ g c hfinite hL
    letI := hfinite
    letI := realization_uCompactlyGeneratedSpace L
    letI : UCompactlyGeneratedSpace.{0} (BasedSpace.adjoinPoint (SSet.toTop.obj L)) :=
      inferInstanceAs (UCompactlyGeneratedSpace.{0} ((SSet.toTop.obj L) ⊕ PUnit))
    let d := realizedAdjoinPointCubeAttachCells n c
    letI : Finite d.ι := inferInstanceAs (Finite c.ι)
    exact spaceSmashMap_finiteCubeAttachCells_stableEquivalence d f hf hL

end KIP126.StableHomotopy.Implementation.Prespectrum
