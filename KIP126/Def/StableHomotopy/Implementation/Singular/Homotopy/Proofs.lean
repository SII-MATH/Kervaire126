module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Homotopy.Data
public import KIP126.Def.Topology.Simplex.ClosedBall.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.ClosedBall
public import KIP126.Def.Topology.SimplicialRealization.Boundary.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Relative.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory Topology Simplicial Opposite
open scoped unitInterval Topology.Homotopy

set_option backward.isDefEq.respectTransparency false

universe u

private theorem realization_const_apply {K L : SSet.{u}} (v : L.obj (op ⦋0⦌))
    (x : |K|) :
    SSet.toTop.map (SSet.const (X := K) v) x =
      TopCat.toSSetObj₀Equiv ((sSetTopAdj.unit.app L).app (op ⦋0⦌) v) := by
  let q : K ⟶ (Δ[0] : SSet.{u}) := SSet.const (SSet.yonedaEquiv (𝟙 _))
  have h : SSet.const (X := K) v = q ≫ SSet.const v := (SSet.comp_const q v).symm
  rw [h, Functor.map_comp, TopCat.comp_app]
  rw [Subsingleton.elim (SSet.toTop.map q x) default]
  exact KIP126.Topology.SimplicialRealization.realization_vertex_eq_unit L v

/-- Every actual cubical loop has an exact based lift through singular
evaluation. A single singular simplex suffices after identifying the
simplex--boundary pair with the cube--boundary pair. -/
theorem singularEvaluationLoop_surjective (A : BasedSpace.{u}) (n : ℕ) :
    Function.Surjective (singularEvaluationLoop A n) := by
  intro p
  obtain ⟨e,he⟩ := KIP126.Topology.Simplex.exists_stdSimplex_closedBall_homeomorph n
  let c := KIP126.Topology.HomotopyLifting.cubeClosedBallHomeomorph n
  let E := e.trans c.symm
  have hE (z : stdSimplex ℝ (Fin (n+1))) :
      E z ∈ _root_.Cube.boundary (Fin n) ↔ ∃ i, z i = 0 := by
    change E z ∈ _root_.Cube.boundary (Fin n) ↔ ∃ i, z.val i = 0
    rw [KIP126.Topology.HomotopyLifting.cubeClosedBallHomeomorph_boundary]
    simpa only [E, c, Homeomorph.trans_apply, Homeomorph.apply_symm_apply] using (he z).symm
  let a : |(Δ[n] : SSet.{u})| ⟶ A.space :=
    TopCat.ofHom (p.val.comp ((⟨E,E.continuous⟩ : C(_, _)).comp
      ⟨SimplexCategory.toTopHomeo ⦋n⦌,(SimplexCategory.toTopHomeo ⦋n⦌).continuous⟩))
  let s : (Δ[n] : SSet.{u}) ⟶ TopCat.toSSet.obj A.space := sSetTopAdj.homEquiv _ _ a
  have ha : SSet.toTop.map (∂Δ[n]).ι ≫ a = TopCat.const A.point := by
    apply ConcreteCategory.hom_ext
    intro z
    apply p.property
    apply (hE _).mpr
    exact (KIP126.Topology.SimplicialRealization.boundary_realization_range n _).mp ⟨z,rfl⟩
  have hs : (∂Δ[n]).ι ≫ s = SSet.const (TopCat.toSSetObj₀Equiv.symm A.point) := by
    rw [← sSetTopAdj.homEquiv_naturality_left, ha]
    simp [Adjunction.homEquiv_unit]
  let l : C(Fin n → I, singularRealization A) :=
    (SSet.toTop.map s).hom.comp
      ((⟨(SimplexCategory.toTopHomeo ⦋n⦌).symm,
        (SimplexCategory.toTopHomeo ⦋n⦌).symm.continuous⟩ : C(_, _)).comp
          ⟨E.symm,E.symm.continuous⟩)
  have hl (t : Fin n → I) (ht : t ∈ _root_.Cube.boundary (Fin n)) :
      l t = (singularRealization A).point := by
    have hz : ∃ i, E.symm t i = 0 := (hE (E.symm t)).mp (by simpa using ht)
    obtain ⟨z,hz⟩ :=
      (KIP126.Topology.SimplicialRealization.boundary_realization_range n (E.symm t)).mpr hz
    have heq : (SimplexCategory.toTopHomeo ⦋n⦌).symm (E.symm t) =
        SSet.toTop.map (∂Δ[n]).ι z := by
      rw [← hz, Homeomorph.symm_apply_apply]
    change SSet.toTop.map s ((SimplexCategory.toTopHomeo ⦋n⦌).symm (E.symm t)) = _
    rw [heq, ← TopCat.comp_app, ← Functor.map_comp, hs]
    exact realization_const_apply _ z
  refine ⟨⟨l,hl⟩, ?_⟩
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  have h := (sSetTopAdj.homEquiv _ _).symm_apply_apply a
  rw [Adjunction.homEquiv_counit] at h
  have ht := ConcreteCategory.congr_hom h ((SimplexCategory.toTopHomeo ⦋n⦌).symm (E.symm t))
  change singularEvaluation A
    (SSet.toTop.map s ((SimplexCategory.toTopHomeo ⦋n⦌).symm (E.symm t))) = p t
  calc
    _ = a ((SimplexCategory.toTopHomeo ⦋n⦌).symm (E.symm t)) := ht
    _ = p t := by
      change p (E ((SimplexCategory.toTopHomeo ⦋n⦌)
        ((SimplexCategory.toTopHomeo ⦋n⦌).symm (E.symm t)))) = p t
      rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

/-- The actual singular counit is surjective on every cubical homotopy
set, including degree zero. This statement does not assert injectivity. -/
theorem singularEvaluationHomotopy_surjective (A : BasedSpace.{u}) (n : ℕ) :
    Function.Surjective (singularEvaluationHomotopy A n) := by
  intro x
  induction x using Quotient.inductionOn with
  | h p =>
    obtain ⟨q,hq⟩ := singularEvaluationLoop_surjective A n p
    exact ⟨⟦q⟧, congrArg Quotient.mk'' hq⟩

end KIP126.StableHomotopy.Implementation
