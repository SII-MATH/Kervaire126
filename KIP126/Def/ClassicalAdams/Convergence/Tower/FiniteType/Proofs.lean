module

public import KIP126.Def.ClassicalAdams.Convergence.Tower.Proofs
public import KIP126.Def.ClassicalAdams.TowerHomology.Finiteness.Proofs

@[expose] public section

namespace KIP126.Classical.Adams
open CategoryTheory CategoryTheory.Limits MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology
universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  [HasFunctorialCofiber (C := C)] [HasProductsOfShape ℕ C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

include R K B in
/-- Finite mod-two homology with a lower bound supplies all layer-finiteness
hypotheses in the actual strong-convergence criterion. -/
theorem IsAdamsTowerStronglyConvergent.of_nilpotent_complete_of_finiteMod2Type (X : C)
    (hX : IsENilpotentComplete H.unit X) (hfinite : FiniteMod2Type H X)
    (hbelow : BoundedBelow (H.HF2 ⊗ X)) (hdetect : TowerDetection.Convergence H.unit X) :
    IsAdamsTowerStronglyConvergent H.unit X := by
  letI : ∀ (n : ℤ) (k : ℕ), Finite (HomotopyGroup (n + 1) (H.HF2 ⊗ adamsTower H.unit X k)) :=
    fun n k => (adamsTower_finiteMod2Type_bounded H R K B X hfinite hbelow k).1 (n + 1)
  exact IsAdamsTowerStronglyConvergent.of_nilpotent_complete_of_finite_layers
    H.unit X hX hdetect

include R K B in
/-- For the sphere, finite bounded coefficient homology is already proved;
nilpotent completeness and the specified detection comparison suffice. -/
theorem sphereAdamsTower_stronglyConvergent_of_nilpotent_complete
    (hX : IsENilpotentComplete H.unit SphereSpectrum)
    (hdetect : TowerDetection.Convergence H.unit SphereSpectrum) :
    IsAdamsTowerStronglyConvergent H.unit SphereSpectrum := by
  exact IsAdamsTowerStronglyConvergent.of_nilpotent_complete_of_finiteMod2Type
    H R K B SphereSpectrum hX (finiteMod2Type_sphere H) (boundedBelow_sphere_homology H) hdetect

include R K B in
/-- The same conclusion for an actual sphere cofiber, including the
selected ν cofiber, with its finite-layer hypotheses proved. -/
theorem sphereCofiberAdamsTower_stronglyConvergent_of_nilpotent_complete (k : ℤ)
    (f : Sphere (C := C) k ⟶ SphereSpectrum)
    (hX : IsENilpotentComplete H.unit (HasFunctorialCofiber.cofib f))
    (hdetect : TowerDetection.Convergence H.unit (HasFunctorialCofiber.cofib f)) :
    IsAdamsTowerStronglyConvergent H.unit (HasFunctorialCofiber.cofib f) := by
  letI : ∀ (n : ℤ) (s : ℕ), Finite (HomotopyGroup (n + 1)
      (H.HF2 ⊗ adamsTower H.unit (HasFunctorialCofiber.cofib f) s)) :=
    fun n s => (sphereCofiberAdamsTower_finiteMod2Type_bounded H R K B k f s).1 (n + 1)
  exact IsAdamsTowerStronglyConvergent.of_nilpotent_complete_of_finite_layers
    H.unit (HasFunctorialCofiber.cofib f) hX hdetect

end KIP126.Classical.Adams
