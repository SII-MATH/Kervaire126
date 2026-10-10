import KIP126.Def.Synthetic.Completion.Predicates

namespace KIP126.Synthetic.Context

open CategoryTheory

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

private theorem source_transport {I : Type*} (F : I → Syn) {i j : I}
    (h : i = j) {A : Syn} (f : F i ⟶ A) :
    eqToHom (congrArg F h.symm) ≫ f = (h ▸ f) := by
  subst j
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The residual sequence uses the same actual λ powers as the quotient
objects, including their specified suspension comparisons. -/
theorem lambdaResidualSequence_step_comp_lambdaPow (A : Syn) (n : ℕ) :
    (lambdaResidualSequence A).step n ≫ lambdaPow n A = lambdaPow (n + 1) A := by
  simp only [lambdaResidualSequence, lambdaPow, Category.assoc]
  exact source_transport (fun p => (SyntheticCategory.biShift p).obj A) _ _

end KIP126.Synthetic.Context
