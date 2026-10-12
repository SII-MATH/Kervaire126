module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Currying.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Spectrification.Telescope.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval Topology.Homotopy

universe u

set_option backward.isDefEq.respectTransparency false

/-- Curry one actual cubical coordinate and include the result in the
attached end of the next cylinder stage. -/
noncomputable def spectrificationDesuspendLoop (X : Prespectrum.{u}) (n r : ℕ)
    (p : GenLoop (Fin (r+1)) (X.level (n+1)) (X.level (n+1)).point) :
    GenLoop (Fin r) ((spectrificationCylinderStep X).level n)
      ((spectrificationCylinderStep X).level n).point :=
  (mappingCylinderSection (spectrificationStepUnit X)).levelLoop n r
    (loopCurryFirst (X.level (n+1)) r p)

/-- The explicit one-stage desuspension on actual based homotopy classes. -/
noncomputable def spectrificationDesuspend (X : Prespectrum.{u}) (n r : ℕ) :
    _root_.HomotopyGroup (Fin (r+1)) (X.level (n+1)) (X.level (n+1)).point →
      _root_.HomotopyGroup (Fin r) ((spectrificationCylinderStep X).level n)
        ((spectrificationCylinderStep X).level n).point :=
  Quotient.map (spectrificationDesuspendLoop X n r) (fun p q h =>
    (show GenLoop.Homotopic (loopCurryFirst (X.level (n+1)) r p)
      (loopCurryFirst (X.level (n+1)) r q) from
        ⟨loopCurryFirstHomotopy (X.level (n+1)) r h.some⟩).comp_continuousMap
          ((mappingCylinderSection (spectrificationStepUnit X)).level n))

end KIP126.StableHomotopy.Implementation.Prespectrum
