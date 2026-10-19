module

public import KIP126.Def.Topology.SimplicialRealization.FiniteSkeleton.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization

open CategoryTheory CategoryTheory.Limits Simplicial Opposite HomotopicalAlgebra

universe u

set_option backward.isDefEq.respectTransparency false

/-- At every finite dimension bound, the actual simplicial cell
filtration itself reaches its target by an isomorphism. -/
theorem simplicialCellComplex_inclusion_isIso_of_dimension (X : SSet.{u}) (d : ℕ)
    [X.HasDimensionLT d] : IsIso (X.relativeCellComplex.incl.app d) := by
  change IsIso (SSet.Subcomplex.ι
    (SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) d))
  have h : SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) d = ⊤ := by
    simp [SSet.skeletonOfMono,skeleton_eq_top_of_dimension X d]
  rw [h]
  infer_instance

/-- The actual simplicial skeletal attachment has finitely many cells
when the original simplicial set is finite. -/
theorem finite_simplicialCellComplex_stage_cells (X : SSet.{u}) [X.Finite] (n : ℕ) :
    Finite (X.relativeCellComplex.attachCells n (by simp)).ι := by
  change Finite (SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) n)
  exact Finite.of_injective (fun c => c.simplex) (by intro a b h; cases a; cases b; cases h; rfl)

/-- Finite simplicial sets admit induction from the empty object by
genuine finite collections of standard simplex boundary attachments.
No triangulation or order-complex presentation is assumed. -/
theorem finite_simplicial_cellular_induction (P : SSet.{u} → Prop)
    (h_initial : ∀ X, IsInitial X → P X)
    (h_iso : ∀ {X Y : SSet.{u}}, (X ≅ Y) → P X → P Y)
    (h_attach : ∀ (n : ℕ) {X Y : SSet.{u}} [X.Finite] (f : X ⟶ Y)
      (a : AttachCells.{u} (fun (_ : Unit) => ∂Δ[n].ι) f), Finite a.ι → P X → P Y)
    (X : SSet.{u}) [X.Finite] : P X := by
  let c := X.relativeCellComplex
  have hp : ∀ n : ℕ, P (c.F.obj n) := by
    intro n
    induction n with
    | zero =>
      exact h_iso c.isoBot.symm (h_initial _ (SSet.Subcomplex.isInitialBot (X := X)))
    | succ n ih =>
      letI : (c.F.obj n).Finite :=
        inferInstanceAs (SSet.Finite
          (SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : X.Subcomplex)) n))
      exact h_attach n (c.F.map (homOfLE (Nat.le_succ n))) (c.attachCells n (by simp))
        (finite_simplicialCellComplex_stage_cells X n) ih
  obtain ⟨d,hd⟩ := X.hasDimensionLT_of_finite
  letI := hd
  letI : IsIso (c.incl.app d) := simplicialCellComplex_inclusion_isIso_of_dimension X d
  exact h_iso (asIso (c.incl.app d)) (hp d)

end KIP126.Topology.SimplicialRealization
