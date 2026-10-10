import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Cooperations.Iterated.Data

/-! All-filtration coordinates derived by iterating the actual tower recurrence.
The coordinate factors are genuine reduced cooperations, not Milnor polynomials. -/

namespace KIP126.Classical.Adams

noncomputable section

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R)
  [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

/-- Coordinates on every actual tower homology group, derived recursively. -/
def adamsTowerHomologyIteratedEquiv (X : C) : ∀ (s : ℕ) (n : ℤ),
    mod2HomologyF2 H R n (adamsTower H.unit X s) ≃ₗ[ZMod 2]
      iteratedReducedCooperations H R (fun i => mod2HomologyF2 H R i X) s n
  | 0, n => LinearEquiv.refl (ZMod 2) (mod2HomologyF2 H R n X)
  | s + 1, n =>
    (LinearEquiv.cast (R := ZMod 2)
      (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit X (s + 1)))
      (show n = (n + 1) - 1 by omega)).trans
        ((adamsTowerHomologyTensorEquiv H R K X s (n + 1)).trans
          (reducedCooperationTensorCongr H R (fun i => mod2HomologyF2 H R i (adamsTower H.unit X s))
            (fun i => adamsTowerHomologyIteratedEquiv X s i) (n + 1)))

/-- Actual first-page coordinates in every nonnegative filtration, with the
Adams grading `n = t - s`. The coordinates are a conclusion, not an input. -/
def adamsFirstPageIteratedEquiv (X : C) (s : ℕ) (t : ℤ) :
    letI := adamsPageF2Module H R X 1 le_rfl s t
    adamsPage H.unit X 1 le_rfl s t ≃ₗ[ZMod 2]
      iteratedReducedCooperations H R (fun i => mod2HomologyF2 H R i X) s (t - s) :=
  letI := adamsPageF2Module H R X 1 le_rfl s t
  (adamsPageOneHomologyF2Equiv H R X s t).trans
    (adamsTowerHomologyIteratedEquiv H R K X s (t - s))

end

end KIP126.Classical.Adams
