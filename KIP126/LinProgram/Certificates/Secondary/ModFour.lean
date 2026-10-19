module

public import KIP126.LinProgram.Certificates.Secondary.Proofs

@[expose] public section


/-!
# Mod-four coefficients of the specified integer lift

The original `MilnorCertificates.coproduct` is a list whose multiplicities give
one specified lift to integer coefficients. This module counts those same
multiplicities modulo four and proves that reduction modulo two recovers the
original `pairTensor`, `pathCoefficient`, and `compose` semantics, for every
original rank, target generator, and monomial of that rank.

No mod-four coalgebra laws are asserted. The half-coefficient depends on this
specified lift: it is not invariant under F₂ normalization of the original
lists. In particular, two equal paths have zero F₂ coefficient but can have
nonzero half-coefficient. The characteristic-two `fastCoproduct` is not used.
These results do not prove the full secondary-associator formula or identify
any input resolution or differential with the actual sphere.
-/

namespace KIP126.Computation.Secondary
open MilnorCertificates

/-- Multiplicity in the original list coproduct, before reducing coefficients. -/
def singletonPairCount (left right : Monomial) (terms : List TensorMonomial) : Nat :=
  (terms.filter fun t => (left == t.1) && (right == t.2)).length

private theorem singleton_coefficient (a b : Monomial) : coefficient [a] b = (a == b) := by
  by_cases h : a = b <;> simp [coefficient, h]

theorem singletonPairCount_parity (left right : Monomial) (terms : List TensorMonomial) :
    (singletonPairCount left right terms % 2 == 1) = pairTensor [left] [right] terms := by
  simp only [singletonPairCount, pairTensor, singleton_coefficient]

/-- The coefficient of the integral list coproduct reduced modulo four.
This deliberately uses the original coproduct, retaining all multiplicities. -/
def singletonProductCoefficientMod4 (rank : Nat) (left right m : Monomial) : Nat :=
  singletonPairCount left right (coproduct rank m) % 4

theorem singletonProductCoefficientMod4_lt_four (rank : Nat) (left right m : Monomial) :
    singletonProductCoefficientMod4 rank left right m < 4 := Nat.mod_lt _ (by decide)

theorem singletonProductCoefficientMod4_mod_two (rank : Nat) (left right m : Monomial) :
    (singletonProductCoefficientMod4 rank left right m % 2 == 1) =
      pairTensor [left] [right] (coproduct rank m) := by
  rw [← singletonPairCount_parity]
  unfold singletonProductCoefficientMod4
  congr 1
  omega

/-- Natural multiplicity of a fixed target coefficient along the complete original
path list. Paths are not discarded or normalized modulo two. -/
def pathMultiplicity (rank target : Nat) (m : Monomial) : List CompositionPath → Nat
  | [] => 0
  | p :: paths =>
      (if p.target = target then singletonPairCount p.left p.right (coproduct rank m) else 0) +
      pathMultiplicity rank target m paths

private theorem parity_add (a b : Nat) :
    ((a + b) % 2 == 1) = xor (a % 2 == 1) (b % 2 == 1) := by
  have ha : a % 2 < 2 := Nat.mod_lt _ (by decide)
  have hb : b % 2 < 2 := Nat.mod_lt _ (by decide)
  have hab := Nat.add_mod a b 2
  by_cases ha0 : a % 2 = 0
  · by_cases hb0 : b % 2 = 0
    · simp [ha0, hb0, hab]
    · have hb1 : b % 2 = 1 := by omega
      simp [ha0, hb1, hab]
  · have ha1 : a % 2 = 1 := by omega
    by_cases hb0 : b % 2 = 0
    · simp [ha1, hb0, hab]
    · have hb1 : b % 2 = 1 := by omega
      simp [ha1, hb1, hab]

theorem pathMultiplicity_parity (rank target : Nat) (m : Monomial)
    (paths : List CompositionPath) :
    (pathMultiplicity rank target m paths % 2 == 1) = pathCoefficient rank target m paths := by
  induction paths with
  | nil => rfl
  | cons p paths ih =>
    simp only [pathMultiplicity, pathCoefficient, parity_add, ih]
    by_cases h : p.target = target
    · simp only [h, ↓reduceIte, singletonPairCount_parity]
    · simp [h]

def pathCoefficientMod4 (rank target : Nat) (m : Monomial)
    (paths : List CompositionPath) : Nat := pathMultiplicity rank target m paths % 4

theorem pathCoefficientMod4_lt_four (rank target : Nat) (m : Monomial)
    (paths : List CompositionPath) : pathCoefficientMod4 rank target m paths < 4 :=
  Nat.mod_lt _ (by decide)

theorem pathCoefficientMod4_cons (rank target : Nat) (m : Monomial)
    (p : CompositionPath) (paths : List CompositionPath) :
    pathCoefficientMod4 rank target m (p :: paths) =
      ((if p.target = target then singletonProductCoefficientMod4 rank p.left p.right m else 0) +
        pathCoefficientMod4 rank target m paths) % 4 := by
  simp only [pathCoefficientMod4, pathMultiplicity]
  by_cases h : p.target = target <;> simp [h, singletonProductCoefficientMod4, Nat.add_mod]

theorem pathCoefficientMod4_mod_two (rank target : Nat) (m : Monomial)
    (paths : List CompositionPath) :
    (pathCoefficientMod4 rank target m paths % 2 == 1) = pathCoefficient rank target m paths := by
  rw [← pathMultiplicity_parity]
  unfold pathCoefficientMod4
  congr 1
  omega

/-- Vanishing of the original F₂ path coefficient makes its accumulated residue
modulo four genuinely two-torsion, before division by two. -/
theorem pathCoefficientMod4_zero_or_two (rank target : Nat) (m : Monomial)
    (paths : List CompositionPath) (hz : pathCoefficient rank target m paths = false) :
    pathCoefficientMod4 rank target m paths = 0 ∨ pathCoefficientMod4 rank target m paths = 2 := by
  have hp := pathCoefficientMod4_mod_two rank target m paths
  rw [hz] at hp
  have he : pathCoefficientMod4 rank target m paths % 2 ≠ 1 := by simpa using hp
  have hb := pathCoefficientMod4_lt_four rank target m paths
  omega

/-- The zero-composition premise is the original full-rank `compose`, with the
same required intermediate images and all original target generators. -/
theorem compose_zero_implies_mod4_two_torsion (rank : Nat)
    (images : Nat → Option ModuleExpression) (a : ModuleExpression)
    (hz : compose rank images a = some (fun _ _ => false)) :
    ∃ paths, resolvePaths images a = some paths ∧
      ∀ target m, m.length = rank →
        pathCoefficientMod4 rank target m paths = 0 ∨
        pathCoefficientMod4 rank target m paths = 2 := by
  cases hr : resolvePaths images a with
  | none => simp [compose, hr] at hz
  | some paths =>
    refine ⟨paths, rfl, ?_⟩
    intro target m hm
    have hc : pathCoefficient rank target m paths = false := by
      simp only [compose, hr, Option.map_some, Option.some.injEq] at hz
      exact congrFun (congrFun hz target) ⟨m, hm⟩
    exact pathCoefficientMod4_zero_or_two rank target m paths hc

/-- Division by two is partial on the canonical mod-four residue: odd residues
are rejected, and the result is one F₂ coefficient. -/
def halveMod4 : Nat → Option Bool
  | 0 => some false
  | 2 => some true
  | _ => none

theorem halveMod4_eq_some_iff (c : Nat) (b : Bool) :
    halveMod4 c = some b ↔ c = 2 * b.toNat := by
  cases c with
  | zero => cases b <;> decide
  | succ c =>
    cases c with
    | zero => cases b <;> decide
    | succ c =>
      cases c with
      | zero => cases b <;> decide
      | succ c => cases b <;> simp [halveMod4]

theorem halveMod4_exists_iff (c : Nat) :
    (∃ b, halveMod4 c = some b) ↔ c = 0 ∨ c = 2 := by
  constructor
  · rintro ⟨b, hb⟩
    have he := (halveMod4_eq_some_iff c b).mp hb
    cases b <;> simp_all
  · rintro (h | h)
    · subst c; exact ⟨false, rfl⟩
    · subst c; exact ⟨true, rfl⟩

theorem halveMod4_path_of_zero (rank target : Nat) (m : Monomial)
    (paths : List CompositionPath) (hz : pathCoefficient rank target m paths = false) :
    ∃ b, halveMod4 (pathCoefficientMod4 rank target m paths) = some b ∧
      pathCoefficientMod4 rank target m paths = 2 * b.toNat := by
  obtain ⟨b, hb⟩ := (halveMod4_exists_iff _).mpr
    (pathCoefficientMod4_zero_or_two rank target m paths hz)
  exact ⟨b, hb, (halveMod4_eq_some_iff _ b).mp hb⟩

theorem compose_zero_implies_mod4_halving (rank : Nat)
    (images : Nat → Option ModuleExpression) (a : ModuleExpression)
    (hz : compose rank images a = some (fun _ _ => false)) :
    ∃ paths, resolvePaths images a = some paths ∧
      ∀ target m, m.length = rank →
        ∃ b, halveMod4 (pathCoefficientMod4 rank target m paths) = some b ∧
          pathCoefficientMod4 rank target m paths = 2 * b.toNat := by
  obtain ⟨paths, hp, hz⟩ := compose_zero_implies_mod4_two_torsion rank images a hz
  refine ⟨paths, hp, ?_⟩
  intro target m hm
  obtain ⟨b, hb⟩ := (halveMod4_exists_iff _).mpr (hz target m hm)
  exact ⟨b, hb, (halveMod4_eq_some_iff _ b).mp hb⟩

end KIP126.Computation.Secondary
