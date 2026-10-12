module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Desuspension.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

/-- Desuspending a stabilization is the actual transition to the cylinder stage. -/
theorem spectrificationDesuspend_stabilize (X : Prespectrum.{u}) (n r : ℕ)
    (x : _root_.HomotopyGroup (Fin r) (X.level n) (X.level n).point) :
    spectrificationDesuspend X n r (stabilizeHomotopy X n r x) =
      (spectrificationCylinderUnit X).levelHomotopy n r x := by
  induction x using Quotient.inductionOn with
  | h p =>
    exact Quotient.sound (mappingCylinder_loop_deformation (spectrificationStepUnit X) n r
      ((spectrificationCylinderUnit X).levelLoop n r p)).symm

/-- Stabilizing the displayed desuspension is the same actual stage transition. -/
theorem stabilize_spectrificationDesuspend (X : Prespectrum.{u}) (n r : ℕ)
    (x : _root_.HomotopyGroup (Fin (r+1)) (X.level (n+1)) (X.level (n+1)).point) :
    stabilizeHomotopy (spectrificationCylinderStep X) n r (spectrificationDesuspend X n r x) =
      (spectrificationCylinderUnit X).levelHomotopy (n+1) (r+1) x := by
  induction x using Quotient.inductionOn with
  | h p =>
    let q := (spectrificationCylinderUnit X).levelLoop (n+1) (r+1) p
    have he : stabilizeLoop (spectrificationCylinderStep X) n r
        (spectrificationDesuspendLoop X n r p) =
        (mappingCylinderSection (spectrificationStepUnit X)).levelLoop (n+1) (r+1)
          ((mappingCylinderProjection (spectrificationStepUnit X)).levelLoop (n+1) (r+1) q) := by
      apply GenLoop.ext
      intro t
      change mappingCylinderMk (spectrificationStepUnit X) (n+1)
        (.inr { toFun := fun s => X.bond (n+1) (p (Fin.cases (t 0) (fun j => t j.succ)),s)
                continuous_toFun := _
                source' := _
                target' := _ }) = _
      have ht : Fin.cases (t 0) (fun j => t j.succ) = t := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      simp only [ht]
      rfl
    apply Eq.trans (congrArg Quotient.mk' he)
    exact Quotient.sound (mappingCylinder_loop_deformation (spectrificationStepUnit X)
      (n+1) (r+1) q).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
