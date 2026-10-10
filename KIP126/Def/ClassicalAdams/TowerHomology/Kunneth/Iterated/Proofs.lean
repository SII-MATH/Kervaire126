import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Iterated.Data

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

@[simp]
theorem adamsTowerHomologyIteratedEquiv_zero (X : C) (n : ℤ)
    (x : mod2HomologyF2 H R n X) :
    adamsTowerHomologyIteratedEquiv H R K X 0 n x = x := rfl

/-- Each recursive step uses the proved actual-fiber tensor recurrence. -/
theorem adamsTowerHomologyIteratedEquiv_succ (X : C) (s : ℕ) (n : ℤ)
    (x : mod2HomologyF2 H R n (adamsTower H.unit X (s + 1))) :
    adamsTowerHomologyIteratedEquiv H R K X (s + 1) n x =
      reducedCooperationTensorCongr H R (fun i => mod2HomologyF2 H R i (adamsTower H.unit X s))
        (fun i => adamsTowerHomologyIteratedEquiv H R K X s i) (n + 1)
        (adamsTowerHomologyTensorEquiv H R K X s (n + 1)
          (LinearEquiv.cast (R := ZMod 2)
            (M := fun i => mod2HomologyF2 H R i (adamsTower H.unit X (s + 1)))
            (show n = (n + 1) - 1 by omega) x)) := rfl

/-- The actual first quotient page enters through its proved layer comparison. -/
theorem adamsFirstPageIteratedEquiv_apply (X : C) (s : ℕ) (t : ℤ)
    (x : adamsPage H.unit X 1 le_rfl s t) :
    adamsFirstPageIteratedEquiv H R K X s t x =
      adamsTowerHomologyIteratedEquiv H R K X s (t - s)
        (adamsPageOneHomologyEquiv H.unit X s t x) := rfl

end

end KIP126.Classical.Adams
