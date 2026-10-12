module

public import KIP126.Def.Topology.HomotopyGroup.Basepoint.Proofs

@[expose] public section

namespace KIP126.Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual path transport of cubical homotopy groups, constructed by
cube-boundary extension and independent of its choices. -/
noncomputable def homotopyBasepointEquiv {Y : Type u} [TopologicalSpace Y]
    {a b : Y} (γ : Path a b) (n : ℕ) :
    HomotopyGroup.Pi n Y a ≃ HomotopyGroup.Pi n Y b where
  toFun := Quotient.map (fun p => (exists_genLoopTransport γ p).choose) (by
    intro p p' h
    exact (exists_genLoopTransport γ p).choose_spec.unique
      ((exists_genLoopTransport γ p').choose_spec.pre_homotopic h))
  invFun := Quotient.map (fun p => (exists_genLoopTransport γ.symm p).choose) (by
    intro p p' h
    exact (exists_genLoopTransport γ.symm p).choose_spec.unique
      ((exists_genLoopTransport γ.symm p').choose_spec.pre_homotopic h))
  left_inv := by
    intro p
    induction p using Quotient.inductionOn with
    | h p =>
      exact Quotient.sound ((exists_genLoopTransport γ.symm
        (exists_genLoopTransport γ p).choose).choose_spec.unique
          (exists_genLoopTransport γ p).choose_spec.symm)
  right_inv := by
    intro p
    induction p using Quotient.inductionOn with
    | h p =>
      have h := (exists_genLoopTransport γ.symm p).choose_spec.symm
      rw [Path.symm_symm] at h
      exact Quotient.sound ((exists_genLoopTransport γ
        (exists_genLoopTransport γ.symm p).choose).choose_spec.unique h)

/-- The path traced by one point under an actual continuous homotopy. -/
def homotopyPointPath {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X,Y)} (H : f.Homotopy g) (x : X) : Path (f x) (g x) where
  toFun t := H (t,x)
  continuous_toFun := H.continuous.comp (continuous_id.prodMk continuous_const)
  source' := H.apply_zero x
  target' := H.apply_one x

end KIP126.Topology
