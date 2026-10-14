module

public import KIP126.LinProgram.Model.ModulePresentation.Proofs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section


/-! The universal property of the existing complete native module quotient.
The coefficients remain the original `LinE2.E2`, and every original relation
must vanish. No native map or actual Ext comparison is constructed here. -/
namespace KIP126.LinModule.Presentation
noncomputable section
variable {M : Type*} [AddCommGroup M] [Module LinE2.E2 M]
  {n : Nat} (g : Fin n → M)

/-- This is a wrapper around the existing native word evaluation, with exactly
the same comma/semicolon parser as `relationVector`. -/
def evaluateRelation (code : String) : M :=
  ((code.splitOn ";").map fun mon =>
    evaluatePowers g ((mon.splitOn ",").map (fun a => a.toNat?.getD 0))).sum

theorem linearCombination_ofPowers (word : List Nat) :
    Finsupp.linearCombination LinE2.E2 g (ofPowers n word) = evaluatePowers g word := by
  induction word using ofPowers.induct n with
  | case1 j hj =>
    simp only [ofPowers, evaluatePowers, dif_pos hj,
      Finsupp.linearCombination_single, one_smul]
  | case2 j hj => simp only [ofPowers, evaluatePowers, dif_neg hj, map_zero]
  | case3 i a rest hi ih =>
    simp only [ofPowers, evaluatePowers, dif_pos hi, map_smul, ih]
  | case4 i a rest hi =>
    simp only [ofPowers, evaluatePowers, dif_neg hi, map_zero]
  | case5 => simp only [ofPowers, evaluatePowers, map_zero]

theorem linearCombination_monomialVector (code : String) :
    Finsupp.linearCombination LinE2.E2 g (monomialVector n code) =
      evaluatePowers g ((code.splitOn ",").map (fun a => a.toNat?.getD 0)) :=
  linearCombination_ofPowers g _

theorem linearCombination_relationVector (code : String) :
    Finsupp.linearCombination LinE2.E2 g (relationVector n code) =
      evaluateRelation g code := by
  simp only [relationVector, map_list_sum, List.map_map,
    Function.comp_def, linearCombination_monomialVector, evaluateRelation]

/-- All rows of the supplied complete relation list are used. -/
theorem definingSubmodule_le_ker (relations : List String)
    (hrel : ∀ code ∈ relations, evaluateRelation g code = 0) :
    definingSubmodule n relations ≤ LinearMap.ker (Finsupp.linearCombination LinE2.E2 g) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨code, hcode, rfl⟩
  change Finsupp.linearCombination LinE2.E2 g (relationVector n code) = 0
  rw [linearCombination_relationVector, hrel code hcode]

/-- Descend the standard free-module linear combination through the original
quotient, conditional on vanishing of every relation. -/
def desc (relations : List String)
    (hrel : ∀ code ∈ relations, evaluateRelation g code = 0) :
    Model n relations →ₗ[LinE2.E2] M :=
  (definingSubmodule n relations).liftQ (Finsupp.linearCombination LinE2.E2 g)
    (definingSubmodule_le_ker g relations hrel)

@[simp] theorem desc_projection (relations : List String)
    (hrel : ∀ code ∈ relations, evaluateRelation g code = 0) (v : Free n) :
    desc g relations hrel (projection n relations v) =
      Finsupp.linearCombination LinE2.E2 g v := rfl

@[simp] theorem desc_generator (relations : List String)
    (hrel : ∀ code ∈ relations, evaluateRelation g code = 0) (i : Fin n) :
    desc g relations hrel (generator n relations i) = g i := by
  simp only [generator, desc_projection, Finsupp.linearCombination_single, one_smul]

/-- The same map computes on every word, including out-of-range words under
the existing parser's semantics; no degree cutoff is introduced. -/
theorem desc_ofPowers (relations : List String)
    (hrel : ∀ code ∈ relations, evaluateRelation g code = 0) (word : List Nat) :
    desc g relations hrel (projection n relations (ofPowers n word)) =
      evaluatePowers g word := by
  rw [desc_projection, linearCombination_ofPowers]

theorem desc_monomialVector (relations : List String)
    (hrel : ∀ code ∈ relations, evaluateRelation g code = 0) (code : String) :
    desc g relations hrel (projection n relations (monomialVector n code)) =
      evaluatePowers g ((code.splitOn ",").map (fun a => a.toNat?.getD 0)) :=
  desc_ofPowers g relations hrel _

theorem desc_relationVector (relations : List String)
    (hrel : ∀ code ∈ relations, evaluateRelation g code = 0) (code : String) :
    desc g relations hrel (projection n relations (relationVector n code)) =
      evaluateRelation g code := by
  rw [desc_projection, linearCombination_relationVector]

omit g in
/-- Maps out of the whole quotient are determined by all native generators. -/
theorem hom_ext (relations : List String)
    (f f' : Model n relations →ₗ[LinE2.E2] M)
    (h : ∀ i : Fin n, f (generator n relations i) = f' (generator n relations i)) :
    f = f' := by
  apply Submodule.linearMap_qext
  apply Finsupp.lhom_ext
  intro i c
  have he : Finsupp.single i c = c • Finsupp.single i (1 : LinE2.E2) := by simp
  simp only [he, map_smul, LinearMap.comp_apply]
  exact congrArg (c • ·) (h i)

theorem desc_unique (relations : List String)
    (hrel : ∀ code ∈ relations, evaluateRelation g code = 0)
    (f : Model n relations →ₗ[LinE2.E2] M)
    (hf : ∀ i : Fin n, f (generator n relations i) = g i) :
    f = desc g relations hrel := by
  apply hom_ext relations
  intro i
  rw [hf, desc_generator]

theorem existsUnique_desc (relations : List String)
    (hrel : ∀ code ∈ relations, evaluateRelation g code = 0) :
    ∃! f : Model n relations →ₗ[LinE2.E2] M,
      ∀ i : Fin n, f (generator n relations i) = g i :=
  ⟨desc g relations hrel, desc_generator g relations hrel,
    fun f hf => desc_unique g relations hrel f hf⟩

end
end KIP126.LinModule.Presentation
