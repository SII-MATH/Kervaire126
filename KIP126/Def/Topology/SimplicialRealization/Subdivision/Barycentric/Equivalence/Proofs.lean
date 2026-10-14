module

public import KIP126.Def.Topology.SimplicialRealization.Subdivision.Barycentric.Proofs
public import KIP126.Def.Topology.Simplex.BarycentricDecomposition.Uniqueness.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory Simplicial Opposite

universe u

set_option backward.isDefEq.respectTransparency false

/-- Every actual subdivided-simplex point lies in a strict flag with
strictly positive barycentric weights. -/
theorem exists_simplexSubdivision_positive_flag (n : SimplexCategory)
    (x : |SimplexCategory.sd.{u}.obj n|) :
    ∃ (d : ℕ) (s : (SimplexCategory.sd.{u}.obj n).obj (op ⦋d⦌))
      (w : stdSimplex ℝ (Fin (d+1))),
      StrictMono (fun k => (s.obj k).finset) ∧
      (∀ k, 0 < w k) ∧ simplexPoint _ s w = x := by
  obtain ⟨d,s,t,ht,he⟩ := exists_nondegenerate_interior (SimplexCategory.sd.obj n) x
  let w := SimplexCategory.toTopHomeo ⦋d⦌ t
  have htw : (SimplexCategory.toTopHomeo ⦋d⦌).symm w = t :=
    (SimplexCategory.toTopHomeo ⦋d⦌).symm_apply_apply t
  refine ⟨d,s.val,w,?_,?_,?_⟩
  · exact (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property
  · exact (simplex_interior_iff_positive d w).mp (by rw [htw]; exact ht)
  · rw [simplexPoint_eq_yoneda,htw]
    exact he

/-- Sorting the positive coordinates into upper level sets constructs
an actual preimage under geometric barycentric subdivision. -/
theorem simplexSubdivisionBarycentric_surjective (n : SimplexCategory) :
    Function.Surjective (simplexSubdivisionBarycentric.{u} n) := by
  classical
  intro y
  let y' : stdSimplex ℝ (ULift.{u} (Fin (n.len+1))) := stdSimplex.map ULift.up y
  obtain ⟨m,hm,c,w,hc,hmono,_,hrecon⟩ :=
    Simplex.BarycentricDecomposition.exists_strict_flag y'
  cases m with
  | zero => omega
  | succ d =>
    let q (k : Fin (d+1)) : PartialOrder.NonemptyFiniteChains
        (ULift.{u} (Fin (n.len+1))) := {
      finset := c k
      nonempty := hc k
      comparable := fun a b => le_total a b }
    have hq : Monotone q := fun a b hab => hmono.monotone hab
    let s : (SimplexCategory.sd.{u}.obj n).obj (op ⦋d⦌) := hq.functor
    refine ⟨simplexPoint _ s w,?_⟩
    rw [simplexSubdivisionBarycentric_simplex]
    apply stdSimplex.ext
    funext j
    change (∑ k, w k * finiteChainBarycenter n (q k) j) = y j
    simp only [finiteChainBarycenter_apply]
    calc
      _ = y' (ULift.up j) := by
        convert (hrecon (ULift.up j)).symm using 1
        apply Finset.sum_congr rfl
        intro k _
        by_cases hj : ULift.up j ∈ c k <;> simp [q,hj]
      _ = y j := simplex_map_apply_injective ULift.up ULift.up_injective y j

/-- The actual projection has exactly the uniform-face coordinate
formula in the universe-lifted vertex set used by subdivision. -/
theorem simplexSubdivisionBarycentric_flag_coordinates (n : SimplexCategory)
    {d : ℕ} (s : (SimplexCategory.sd.{u}.obj n).obj (op ⦋d⦌))
    (w : stdSimplex ℝ (Fin (d+1))) (j : ULift.{u} (Fin (n.len+1))) :
    stdSimplex.map ULift.up (simplexSubdivisionBarycentric n (simplexPoint _ s w)) j =
      ∑ k, w k * (if j ∈ (s.obj k).finset then ((s.obj k).finset.card : ℝ)⁻¹ else 0) := by
  classical
  cases j with | up j =>
    rw [simplex_map_apply_injective ULift.up ULift.up_injective,
      simplexSubdivisionBarycentric_simplex]
    change (∑ k, w k * finiteChainBarycenter n (s.obj k) j) = _
    apply Finset.sum_congr rfl
    intro k _
    rw [finiteChainBarycenter_apply]

/-- Strict positive flag coordinates detect equality in the actual
realization, proving injectivity of geometric subdivision. -/
theorem simplexSubdivisionBarycentric_injective (n : SimplexCategory) :
    Function.Injective (simplexSubdivisionBarycentric.{u} n) := by
  classical
  intro x y hxy
  obtain ⟨d,s,w,hsm,hw,hs⟩ := exists_simplexSubdivision_positive_flag n x
  obtain ⟨e,r,v,hrm,hv,hr⟩ := exists_simplexSubdivision_positive_flag n y
  let z : stdSimplex ℝ (ULift.{u} (Fin (n.len+1))) :=
    stdSimplex.map ULift.up (simplexSubdivisionBarycentric n x)
  have hzs (j : ULift.{u} (Fin (n.len+1))) :
      z j = ∑ k, w k * (if j ∈ (s.obj k).finset then ((s.obj k).finset.card : ℝ)⁻¹ else 0) := by
    dsimp only [z]
    rw [← hs]
    exact simplexSubdivisionBarycentric_flag_coordinates n s w j
  have hzr (j : ULift.{u} (Fin (n.len+1))) :
      z j = ∑ k, v k * (if j ∈ (r.obj k).finset then ((r.obj k).finset.card : ℝ)⁻¹ else 0) := by
    dsimp only [z]
    rw [hxy,← hr]
    exact simplexSubdivisionBarycentric_flag_coordinates n r v j
  obtain ⟨hde,hflag,hweight⟩ := Simplex.BarycentricDecomposition.strict_flag_unique z
    (m := d+1) (n := e+1)
    (fun k => (s.obj k).finset) hsm (fun k => (s.obj k).nonempty) w hw (by
      intro j
      rw [hzs j]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hj : j ∈ (s.obj k).finset <;> simp [hj])
    (fun k => (r.obj k).finset) hrm (fun k => (r.obj k).nonempty) v hv (by
      intro j
      rw [hzr j]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hj : j ∈ (r.obj k).finset <;> simp [hj])
  have hde' : d = e := by omega
  subst e
  have hsr : s = r := by
    change @Eq (Fin (d+1) ⥤ PartialOrder.NonemptyFiniteChains
      (ULift.{u} (Fin (n.len+1)))) s r
    exact CategoryTheory.Functor.ext
      (fun k => PartialOrder.NonemptyFiniteChains.ext (congrFun (eq_of_heq hflag) k))
  have hwv : w = v := eq_of_heq hweight
  rw [← hs,← hr,hsr,hwv]

/-- Geometric barycentric subdivision is genuinely bijective. -/
theorem simplexSubdivisionBarycentric_bijective (n : SimplexCategory) :
    Function.Bijective (simplexSubdivisionBarycentric.{u} n) :=
  ⟨simplexSubdivisionBarycentric_injective n,simplexSubdivisionBarycentric_surjective n⟩

/-- The actual realization of the flag subdivision is homeomorphic to
the standard topological simplex by its barycentric projection. -/
theorem exists_simplexSubdivisionBarycentric_homeomorph (n : SimplexCategory) :
    ∃ h : |SimplexCategory.sd.{u}.obj n| ≃ₜ stdSimplex ℝ (Fin (n.len+1)),
      ∀ x, h x = simplexSubdivisionBarycentric n x := by
  letI := compactSpace_simplexSubdivision.{u} n
  let e := Equiv.ofBijective _ (simplexSubdivisionBarycentric_bijective.{u} n)
  exact ⟨Continuous.homeoOfEquivCompactToT2
    (f := e) (simplexSubdivisionBarycentric n).continuous,fun _ => rfl⟩

end KIP126.Topology.SimplicialRealization
