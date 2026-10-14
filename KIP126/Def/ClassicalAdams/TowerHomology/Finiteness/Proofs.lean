module

public import KIP126.Def.Algebra.Graded.Tensor.Finiteness.Proofs
public import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Data
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Full.Finiteness.Proofs
public import KIP126.Def.StableHomotopy.FiniteType.Triangle.Proofs

@[expose] public section

/-! Finiteness of the actual coefficient-smash Adams tower, using bounded
coefficient homology and the existing cooperation Künneth comparison. -/

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Core.Algebra

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)

omit [MonoidalPreadditive C] in
/-- The sphere's coefficient homology is bounded below directly from the
Eilenberg--Mac Lane coefficients and the tensor unit. -/
theorem boundedBelow_sphere_homology : BoundedBelow (H.HF2 ⊗ SphereSpectrum) := by
  refine ⟨0, fun n hn => ?_⟩
  letI := H.homotopy_vanishes n (by omega)
  have hi : Function.Injective
      (fun a : HomotopyGroup n (H.HF2 ⊗ SphereSpectrum) => a ≫ (ρ_ H.HF2).hom) :=
    fun _ _ h => (cancel_mono (ρ_ H.HF2).hom).1 h
  exact hi.subsingleton

include R K B in
/-- Applying a further coefficient smash preserves a lower homotopy bound. -/
theorem boundedBelow_double_hf2_tensor {X : C}
    (hX : BoundedBelow (H.HF2 ⊗ X)) : BoundedBelow (H.HF2 ⊗ (H.HF2 ⊗ X)) := by
  obtain ⟨N, hN⟩ := hX
  refine ⟨N, fun n hn => ?_⟩
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI := gradedTensor_subsingleton_of_lt (R := ZMod 2)
    (Mod2Cooperations H) (fun i => mod2HomologyF2 H R i X) 0 N n
    (mod2Cooperations_negative_subsingleton H R B) hN (by omega)
  exact (K.comparison X n).injective.subsingleton

include R K B in
/-- Finite coefficient homology remains finite after a coefficient smash
when its grading is bounded below. -/
theorem finiteMod2Type_hf2_tensor {X : C} (hX : FiniteMod2Type H X)
    (hbelow : BoundedBelow (H.HF2 ⊗ X)) : FiniteMod2Type H (H.HF2 ⊗ X) := by
  obtain ⟨N, hN⟩ := hbelow
  intro n
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI := gradedTensor_finite (R := ZMod 2)
    (Mod2Cooperations H) (fun i => mod2HomologyF2 H R i X) 0 N n
    (mod2Cooperations_negative_subsingleton H R B) hN
    (finiteMod2Type_hf2 H R B) hX
  exact Finite.of_injective (K.comparison X n) (K.comparison X n).injective

variable [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

include R K B in
/-- Every residual tower stage has finite mod-two homology with a lower
bound, derived inductively from the actual fiber triangles. -/
theorem adamsTower_finiteMod2Type_bounded (X : C)
    (hX : FiniteMod2Type H X) (hbelow : BoundedBelow (H.HF2 ⊗ X)) :
    ∀ s : ℕ, FiniteMod2Type H (adamsTower H.unit X s) ∧
      BoundedBelow (H.HF2 ⊗ adamsTower H.unit X s) := by
  intro s
  induction s with
  | zero => exact ⟨hX, hbelow⟩
  | succ s ih =>
    let Y := adamsTower H.unit X s
    let T : HoCofiberSequence (C := C) := {
      X := fiber (adamsUnit H.unit Y)
      Y := Y
      Z := H.HF2 ⊗ Y
      f := fiberι (adamsUnit H.unit Y)
      g := adamsUnit H.unit Y
      h := adamsResolutionConnecting H.unit Y 0
      distinguished := adamsResolutionTriangle_distinguished H.unit Y 0 }
    exact ⟨FiniteMod2Type.of_cofiber_left T ih.1
      (finiteMod2Type_hf2_tensor H R K B ih.1 ih.2),
      BoundedBelow.of_cofiber_left (adamsHomologySequence H Y) ih.2
        (boundedBelow_double_hf2_tensor H R K B ih.2)⟩

include R K B in
/-- The actual sphere Adams tower satisfies the finite homology hypotheses
without a separate sphere connectivity or convergence premise. -/
theorem sphereAdamsTower_finiteMod2Type_bounded (s : ℕ) :
    FiniteMod2Type H (adamsTower H.unit SphereSpectrum s) ∧
      BoundedBelow (H.HF2 ⊗ adamsTower H.unit SphereSpectrum s) :=
  adamsTower_finiteMod2Type_bounded H R K B SphereSpectrum
    (finiteMod2Type_sphere H) (boundedBelow_sphere_homology H) s

include R K B in
/-- This includes the selected ν cofiber. The finite homology of its
whole Adams tower only needs its actual two-cell construction. -/
theorem sphereCofiberAdamsTower_finiteMod2Type_bounded (k : ℤ)
    (f : Sphere (C := C) k ⟶ SphereSpectrum) (s : ℕ) :
    FiniteMod2Type H (adamsTower H.unit (HasFunctorialCofiber.cofib f) s) ∧
      BoundedBelow (H.HF2 ⊗ adamsTower H.unit (HasFunctorialCofiber.cofib f) s) := by
  let T := HoCofiberSequence.ofMorphism f
  have hS := finiteMod2Type_sphere H
  have hbS := boundedBelow_sphere_homology H
  have hbX : BoundedBelow (H.HF2 ⊗ Sphere (C := C) k) :=
    (hbS.shift k).of_iso (((tensorLeft H.HF2).commShiftIso k).app SphereSpectrum).symm
  exact adamsTower_finiteMod2Type_bounded H R K B T.Z
    (FiniteMod2Type.of_cofiber T (hS.shift k) hS)
    (BoundedBelow.of_cofiber (T.map (tensorLeft H.HF2)) hbX hbS) s

end KIP126.Classical.Adams
