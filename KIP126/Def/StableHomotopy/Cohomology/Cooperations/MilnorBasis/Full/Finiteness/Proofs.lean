module

public import KIP126.Def.StableHomotopy.Cohomology.Cooperations.MilnorBasis.Full.Data
public import KIP126.Def.StableHomotopy.FiniteType.Predicates
public import Mathlib.Data.Finsupp.Fintype

@[expose] public section

namespace KIP126.StableHomotopy.Cohomology

open CategoryTheory KIP126.Steenrod.Milnor

universe u v

variable {C : Type u} [StableHomotopyCategory.{u, v} C] [MonoidalPreadditive C]
  (H : Mod2EilenbergMacLane (C := C)) (R : Mod2RingStructure H)
  (B : Mod2ReducedMilnorBasis H R)

include R B in
/-- The actual Eilenberg--Mac Lane spectrum has finite mod-two homology
in each degree, by the constructed Milnor cooperation coordinates. -/
theorem finiteMod2Type_hf2 : FiniteMod2Type H H.HF2 := by
  classical
  intro n
  letI := milnorMonomial_finite n
  letI := Fintype.ofFinite (MilnorMonomial n)
  exact Finite.of_injective (cooperationMilnorEquiv H R B n)
    (cooperationMilnorEquiv H R B n).injective

include R B in
/-- The actual cooperations vanish in negative degrees, as their Milnor
monomials all have nonnegative weight. -/
theorem mod2Cooperations_negative_subsingleton (n : ℤ) (hn : n < 0) :
    Subsingleton (Mod2Cooperations H n) := by
  letI : IsEmpty (MilnorMonomial n) := ⟨fun d => by
    have h := d.property
    have hp := Int.natCast_nonneg (slotWeight d.val)
    omega⟩
  exact (cooperationMilnorEquiv H R B n).injective.subsingleton

include R B in
/-- An actual map into HF₂ that is injective on mod-two homology gives
finite type. For tmf, the remaining premise is the homology embedding
of its augmentation, which must be proved on the selected spectrum. -/
theorem finiteMod2Type_of_homology_injective {X : C} (f : X ⟶ H.HF2)
    (hf : ∀ n : ℤ, Function.Injective (Mod2Homology.pushforward H f n)) :
    FiniteMod2Type H X := by
  intro n
  letI := finiteMod2Type_hf2 H R B n
  exact Finite.of_injective (Mod2Homology.pushforward H f n) (hf n)

end KIP126.StableHomotopy.Cohomology
