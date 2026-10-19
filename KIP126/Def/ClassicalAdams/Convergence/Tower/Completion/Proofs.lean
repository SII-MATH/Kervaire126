module

public import KIP126.Def.Algebra.Completion.Residual.Proofs
public import KIP126.Def.ClassicalAdams.Convergence.Tower.Data
public import KIP126.Def.ClassicalAdams.Convergence.Tower.Kernels.Proofs
public import KIP126.Def.ClassicalAdams.Completion.Predicates
public import KIP126.Def.StableHomotopy.InverseSequence.Proofs

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory CategoryTheory.Limits MonoidalCategory KIP126.StableHomotopy
set_option backward.isDefEq.respectTransparency false
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
  {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Nilpotent completeness and finite projection kernels make the actual
Adams image filtration complete. This constructs the canonical quotient
limit witness, using the same residual tower and the same homotopy groups. -/
noncomputable def adamsHomotopyFiltration_complete_of_finite_kernels
    (hX : IsENilpotentComplete unit X) (n : ℤ)
    [∀ k : ℕ, Finite (inducedMap (adamsTowerMap unit X 0 k (Nat.zero_le k)) n).ker] :
    Core.Algebra.Filtration.CompletionWitness (adamsHomotopyFiltration unit X) n := by
  let p : ∀ k : ℕ, HomotopyGroup n (adamsTower unit X k) →+ towerAbutment X n :=
    fun k => inducedMap (adamsTowerMap unit X 0 k (Nat.zero_le k)) n
  letI : ∀ k : ℕ, Finite (p k).ker := fun k => by
    exact (inferInstance : Finite (inducedMap (adamsTowerMap unit X 0 k (Nat.zero_le k)) n).ker)
  refine Core.Algebra.Filtration.CompletionWitness.of_residual_sequence
    (adamsHomotopyFiltration unit X) n
    p
    (fun k => inducedMap (adamsTowerStep unit X k) n) ?_ ?_ ?_
  · intro k a
    change (a ≫ adamsTowerStep unit X k) ≫ adamsTowerMap unit X 0 k (Nat.zero_le k) =
      a ≫ adamsTowerMap unit X 0 (k + 1) (Nat.zero_le (k + 1))
    rw [Category.assoc, ← adamsTowerMap_succ]
  · exact (show (adamsResidualSequence unit X).IsAcyclic from hX).bijective_sub_shift (Sphere n)
  · intro k a
    have hk := Core.Algebra.Filtration.quotientProjection_eq_zero_iff
      (adamsHomotopyFiltration unit X) (k : ℤ) n a
    apply hk.trans
    simp only [adamsHomotopyFiltration, OrderIso.apply_symm_apply]
    change (∃ b, inducedMap (adamsTowerToSpectrum unit X (k : ℤ)) n b = a) ↔ _
    simp only [adamsTowerToSpectrum, Int.toNat_natCast, p]
    rfl

/-- Finite homotopy groups in the actual Adams layers supply the finite-kernel
hypothesis, so nilpotent completeness gives completeness of the image filtration. -/
noncomputable def adamsHomotopyFiltration_complete_of_finite_layers
    (hX : IsENilpotentComplete unit X) (n : ℤ)
    [∀ k : ℕ, Finite (HomotopyGroup (n + 1) (H ⊗ adamsTower unit X k))] :
    Core.Algebra.Filtration.CompletionWitness (adamsHomotopyFiltration unit X) n := by
  letI : ∀ k : ℕ, Finite (inducedMap (adamsTowerMap unit X 0 k (Nat.zero_le k)) n).ker :=
    fun k => finite_adamsTowerMap_kernel unit X n k
  exact adamsHomotopyFiltration_complete_of_finite_kernels unit X hX n

end KIP126.Classical.Adams
