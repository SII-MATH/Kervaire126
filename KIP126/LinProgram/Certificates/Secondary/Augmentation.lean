module

public import KIP126.LinProgram.Certificates.Secondary.Expansion

@[expose] public section


/-!
Augmentation of the original Milnor coefficient semantics. This identifies the
native zero-monomial extraction with augmentation, and proves multiplicativity
and compatibility with the existing partial composition. It neither assumes
resolution exactness nor identifies an augmented lift with an Adams differential.
-/
namespace KIP126.Computation.Secondary
open MilnorCertificates

/-- The original coproduct of the algebra unit has exactly its two unit factors. -/
theorem coproduct_unit (rank : Nat) :
    coproduct rank (unitMonomial rank) = [(unitMonomial rank, unitMonomial rank)] := by
  unfold coproduct
  have hzero (j : Nat) : (unitMonomial rank)[j]?.getD 0 = 0 := by
    by_cases h : j < rank <;> simp [unitMonomial, h]
  simp only [hzero, tensorPower]
  have hu : tensorMultiply [(unitMonomial rank, unitMonomial rank)]
      [(unitMonomial rank, unitMonomial rank)] =
      [(unitMonomial rank, unitMonomial rank)] := by
    apply tensor_unit_right
    simp [TensorArity, unitMonomial]
  generalize List.range rank = indices
  induction indices with
  | nil => rfl
  | cons a rest ih => simp only [List.map_cons, List.foldl_cons, hu]; exact ih

theorem pairTensor_unit (rank : Nat) (left right : Polynomial) :
    pairTensor left right (coproduct rank (unitMonomial rank)) =
      (coefficient left (unitMonomial rank) && coefficient right (unitMonomial rank)) := by
  rw [coproduct_unit]
  cases hl : coefficient left (unitMonomial rank) <;>
    cases hr : coefficient right (unitMonomial rank) <;> simp [pairTensor, hl, hr]

/-- Augmentation is multiplicative for the original all-monomial product predicate. -/
theorem product_augmentation (rank : Nat) (left right output : Polynomial)
    (h : IsMilnorProductAll rank left right output) :
    coefficient output (unitMonomial rank) =
      (coefficient left (unitMonomial rank) && coefficient right (unitMonomial rank)) := by
  rw [h.2.2.2 (unitMonomial rank) (by simp [unitMonomial]), pairTensor_unit]

/-- Retain precisely the unit-coefficient generator terms; repetitions retain F₂ parity. -/
def augmentationTerms (rank : Nat) (a : ModuleExpression) : List Nat :=
  (a.filter fun t => t.sq == unitMonomial rank).map (·.generator)

def augmentationCoefficient (a : List Nat) (target : Nat) : Bool :=
  (a.filter (· == target)).length % 2 == 1

theorem augmentationTerms_coefficient (rank : Nat) (a : ModuleExpression) (target : Nat) :
    augmentationCoefficient (augmentationTerms rank a) target =
      expressionCoefficient a target (unitMonomial rank) := by
  simp only [augmentationCoefficient, augmentationTerms, expressionCoefficient, coefficient,
    List.filter_map, List.length_map, List.filter_filter]
  congr 3
  apply List.filter_congr
  intro t ht
  exact Bool.and_comm _ _

/-- Resolving paths happens before augmentation, so missing nonunit paths are not erased. -/
def augmentedPathCoefficient (rank target : Nat) : List CompositionPath → Bool
  | [] => false
  | p :: rest => xor
      (if p.target = target then
        (p.left == unitMonomial rank && p.right == unitMonomial rank) else false)
      (augmentedPathCoefficient rank target rest)

theorem coefficient_singleton_eq (a b : Monomial) : coefficient [a] b = (a == b) := by
  by_cases h : a = b <;> simp [coefficient, h]

theorem pathCoefficient_unit (rank target : Nat) (paths : List CompositionPath) :
    pathCoefficient rank target (unitMonomial rank) paths =
      augmentedPathCoefficient rank target paths := by
  induction paths with
  | nil => rfl
  | cons p rest ih =>
    simp only [pathCoefficient, augmentedPathCoefficient, pairTensor_unit,
      coefficient_singleton_eq, ih]

theorem compose_augmentation (rank : Nat) (images : Nat → Option ModuleExpression)
    (a : ModuleExpression) :
    (compose rank images a).map (fun f target =>
      f target ⟨unitMonomial rank, by simp [unitMonomial]⟩) =
      (resolvePaths images a).map (fun paths target =>
        augmentedPathCoefficient rank target paths) := by
  simp only [compose, Option.map_map]
  congr 1
  funext paths target
  exact pathCoefficient_unit rank target paths

/-- Equal recorded generator lists identify the original algebra's augmented coefficients. -/
theorem augmentation_eq_of_terms (rank : Nat) (a : ModuleExpression) (recorded : List Nat)
    (h : augmentationTerms rank a = recorded) (target : Nat) :
    expressionCoefficient a target (unitMonomial rank) =
      augmentationCoefficient recorded target := by
  rw [← h, augmentationTerms_coefficient]

end KIP126.Computation.Secondary
