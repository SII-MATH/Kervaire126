module

public import KIP126.Def.Algebra.Graded.Tensor.Finiteness.Proofs
public import KIP126.Def.ClassicalAdams.TowerHomology.Kunneth.Data
public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Full.Basic.Proofs
public import KIP126.Def.StableHomotopy.FiniteType.Predicates

@[expose] public section

/-! The reduced cooperation recurrence preserves one fixed lower bound
throughout the actual Adams tower. Its positive cooperation degree cancels
the degree shift in the fiber recurrence. -/

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory KIP126.Steenrod.Milnor

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

include B in
/-- The reduced cooperation basis has strictly positive degrees. -/
theorem reducedCooperations_nonpositive_subsingleton (n : ℤ) (hn : n < 1) :
    letI := mod2HomologyModule H R n H.HF2
    letI := mod2HF2HomotopyModule H R n
    Subsingleton (LinearMap.ker (cooperationCounitF2 H R n)) := by
  letI := mod2HomologyModule H R n H.HF2
  letI := mod2HF2HomotopyModule H R n
  letI : IsEmpty (PositiveMonomial n) := ⟨fun d => by
    have := positiveMonomial_degree_pos d
    omega⟩
  exact (B.basis n).repr.injective.subsingleton

end KIP126.StableHomotopy.Cohomology

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology KIP126.Core.Algebra

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (K : Mod2CooperationKunneth H R) (B : Mod2ReducedMilnorBasis H R)
  [HasFunctorialCofiber (C := C)]
  [(tensorLeft H.HF2).CommShift ℤ] [(tensorLeft H.HF2).IsTriangulated]

include R K B in
/-- A residual Adams step preserves the given lower bound on coefficient
homology, since its tensor recurrence uses reduced cooperations. -/
theorem adamsNextHomology_subsingleton_of_lt (X : C) (N : ℤ)
    (hX : ∀ n : ℤ, n < N → Subsingleton (Mod2Homology H n X))
    (n : ℤ) (hn : n < N) :
    Subsingleton (Mod2Homology H n (fiber (adamsUnit H.unit X))) := by
  letI : ∀ i, Module (ZMod 2) (Mod2Cooperations H i) :=
    fun i => mod2HomologyModule H R i H.HF2
  letI : ∀ i, Module (ZMod 2) (HomotopyGroup i H.HF2) :=
    fun i => mod2HF2HomotopyModule H R i
  letI := gradedTensor_subsingleton_of_lt (R := ZMod 2)
    (fun i => LinearMap.ker (cooperationCounitF2 H R i))
    (fun i => mod2HomologyF2 H R i X) 1 N (n + 1)
    (reducedCooperations_nonpositive_subsingleton H R B) hX (by omega)
  have h := (adamsNextHomologyTensorEquiv H R K X (n + 1)).injective.subsingleton
  change Subsingleton (Mod2Homology H ((n + 1) - 1)
    (fiber (adamsUnit H.unit X))) at h
  simpa using h

include R K B in
/-- Every Adams tower stage retains the same coefficient-homology lower
bound as its initial object. -/
theorem adamsTower_homology_bounded_uniform (X : C) (N : ℤ)
    (hX : ∀ n : ℤ, n < N → Subsingleton (Mod2Homology H n X)) :
    ∀ s : ℕ, ∀ n : ℤ, n < N →
      Subsingleton (Mod2Homology H n (adamsTower H.unit X s)) := by
  intro s
  induction s with
  | zero => exact hX
  | succ s ih =>
    exact adamsNextHomology_subsingleton_of_lt H R K B
      (adamsTower H.unit X s) N ih

include R K B in
/-- Bounded initial coefficient homology provides a single lower bound
for the entire coefficient-smash residual tower. -/
theorem adamsTower_homology_exists_uniform_bound (X : C)
    (hX : BoundedBelow (H.HF2 ⊗ X)) :
    ∃ N : ℤ, ∀ s : ℕ, ∀ n : ℤ, n < N →
      Subsingleton (HomotopyGroup n (H.HF2 ⊗ adamsTower H.unit X s)) := by
  obtain ⟨N, hN⟩ := hX
  exact ⟨N, adamsTower_homology_bounded_uniform H R K B X N hN⟩

end KIP126.Classical.Adams
