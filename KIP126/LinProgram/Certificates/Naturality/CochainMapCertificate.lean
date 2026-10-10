import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! Finite native augmented columns and their genuine linear dual maps.
No Steenrod chain equation, exactness, archived representative comparison or
actual spectrum comparison is supplied by this certificate layer. -/
namespace KIP126.LinModule.CochainMapCertificate

abbrev F2 := ZMod 2

structure GeneratorRecord where
  id : Nat
  s : Nat
  t : Nat
  deriving Repr, DecidableEq

/-- The index refers to the entire specified finite generator family. -/
structure Term (n : Nat) where
  powers : List Nat
  generator : Fin n
  deriving Repr, DecidableEq

structure Entry (m n : Nat) where
  source : Fin n
  targets : List (Fin m)
  nativeBasisId : Nat
  deriving Repr, DecidableEq

/-- Larger native degree windows use sums of dual generators for both sides.
Lists are evaluated in F2, so repeated entries cancel; the source decoder
separately checks the canonical encoding of archived representative lists. -/
structure CombinationEntry (m n : Nat) where
  sources : List (Fin n)
  targets : List (Fin m)
  nativeBasisId : Nat
  deriving Repr, DecidableEq

/-- Internal degree of a Milnor exponent vector, beginning at xi_(k+1). -/
def degreeFrom (k : Nat) : List Nat → Nat
  | [] => 0
  | a :: rest => a * (2 ^ (k + 1) - 1) + degreeFrom (k + 1) rest

def Term.degree {n : Nat} (t : Term n) : Nat := degreeFrom 0 t.powers

/-- Augmentation kills every nonconstant Milnor coefficient. -/
def Term.scalar {n : Nat} (t : Term n) : Bool := t.powers.all (· == 0)

def columnValue {n : Nat} : List (Term n) → (Fin n → F2) → F2
  | [], _ => 0
  | t :: rest, x => (if t.scalar then x t.generator else 0) + columnValue rest x

def termLinear {n : Nat} (t : Term n) : (Fin n → F2) →ₗ[F2] F2 :=
  if t.scalar then LinearMap.proj t.generator else 0

def columnLinear {n : Nat} : List (Term n) → (Fin n → F2) →ₗ[F2] F2
  | [] => 0
  | t :: rest => termLinear t + columnLinear rest

@[simp] theorem columnLinear_apply {n : Nat} (ts : List (Term n)) (x : Fin n → F2) :
    columnLinear ts x = columnValue ts x := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [columnLinear, LinearMap.add_apply, ih, columnValue, termLinear]
    split <;> rfl

/-- All columns are evaluated by one F2-linear map on cochain coordinates. -/
def pullback {m n : Nat} (columns : Fin m → List (Term n)) :
    (Fin n → F2) →ₗ[F2] (Fin m → F2) :=
  LinearMap.pi (fun i => columnLinear (columns i))

@[simp] theorem pullback_apply {m n : Nat} (columns : Fin m → List (Term n))
    (x : Fin n → F2) (i : Fin m) :
    pullback columns x i = columnValue (columns i) x := by
  exact columnLinear_apply (columns i) x

def basis {n : Nat} (i : Fin n) : Fin n → F2 := fun j => if j = i then 1 else 0

def targetValue {m : Nat} (indices : List (Fin m)) (j : Fin m) : F2 :=
  (indices.map (fun i => basis i j)).sum

def check {m n : Nat} (columns : Fin m → List (Term n)) (e : Entry m n) : Bool :=
  (List.finRange m).all (fun j =>
    decide (columnValue (columns j) (basis e.source) = targetValue e.targets j))

/-- A finite successful check proves equality on every column of the same map. -/
theorem check_sound {m n : Nat} (columns : Fin m → List (Term n)) (e : Entry m n)
    (h : check columns e = true) :
    pullback columns (basis e.source) = targetValue e.targets := by
  funext j
  have hj := (List.all_eq_true.mp h) j (List.mem_finRange j)
  simpa only [pullback_apply] using (of_decide_eq_true hj)

/-- Coordinates are interpreted as linear functionals on the full finite free space. -/
noncomputable def functional {n : Nat} (x : Fin n → F2) : (Fin n →₀ F2) →ₗ[F2] F2 :=
  Finsupp.linearCombination F2 x

noncomputable def columnChain {n : Nat} : List (Term n) → (Fin n →₀ F2)
  | [] => 0
  | t :: ts => (if t.scalar then Finsupp.single t.generator 1 else 0) + columnChain ts

/-- The augmented linear map, on the entire specified source generator family. -/
noncomputable def augmentedMap {m n : Nat} (columns : Fin m → List (Term n)) :
    (Fin m →₀ F2) →ₗ[F2] (Fin n →₀ F2) :=
  Finsupp.linearCombination F2 (fun i => columnChain (columns i))

theorem functional_columnChain {n : Nat} (x : Fin n → F2) (ts : List (Term n)) :
    functional x (columnChain ts) = columnValue ts x := by
  induction ts with
  | nil => simp [columnChain, columnValue]
  | cons t ts ih =>
    simp only [columnChain, map_add, ih, columnValue]
    congr 1
    split <;> simp [functional]

/-- The coordinate map really is precomposition of linear functionals by the
augmented native map; it is not only a successful Boolean calculation. -/
theorem functional_pullback {m n : Nat} (columns : Fin m → List (Term n))
    (x : Fin n → F2) :
    functional (pullback columns x) = (functional x).comp (augmentedMap columns) := by
  apply Finsupp.lhom_ext
  intro i c
  have hc : Finsupp.linearCombination F2 x (columnChain (columns i)) =
      columnValue (columns i) x := functional_columnChain x (columns i)
  simp [functional, augmentedMap, Finsupp.linearCombination_single, hc]

theorem check_sound_precomposition {m n : Nat} (columns : Fin m → List (Term n))
    (e : Entry m n) (h : check columns e = true) :
    (functional (basis e.source)).comp (augmentedMap columns) =
      functional (targetValue e.targets) := by
  rw [← functional_pullback, check_sound columns e h]

/-- Check a complete linear combination against every column of one map. -/
def checkCombination {m n : Nat} (columns : Fin m → List (Term n))
    (e : CombinationEntry m n) : Bool :=
  (List.finRange m).all (fun j =>
    decide (columnValue (columns j) (targetValue e.sources) = targetValue e.targets j))

theorem checkCombination_sound {m n : Nat} (columns : Fin m → List (Term n))
    (e : CombinationEntry m n) (h : checkCombination columns e = true) :
    pullback columns (targetValue e.sources) = targetValue e.targets := by
  funext j
  have hj := (List.all_eq_true.mp h) j (List.mem_finRange j)
  simpa only [pullback_apply] using (of_decide_eq_true hj)

/-- The sum certificate proves actual equality of finite linear functionals. -/
theorem checkCombination_sound_precomposition {m n : Nat}
    (columns : Fin m → List (Term n)) (e : CombinationEntry m n)
    (h : checkCombination columns e = true) :
    (functional (targetValue e.sources)).comp (augmentedMap columns) =
      functional (targetValue e.targets) := by
  rw [← functional_pullback, checkCombination_sound columns e h]

/-- A reusable auxiliary witness removes positive-degree terms once per column. -/
def augmentationSupport {n : Nat} : List (Term n) → List (Fin n)
  | [] => []
  | t :: ts => if t.scalar then t.generator :: augmentationSupport ts else augmentationSupport ts

def supportValue {n : Nat} (indices : List (Fin n)) (x : Fin n → F2) : F2 :=
  (indices.map x).sum

theorem columnValue_augmentationSupport {n : Nat} (ts : List (Term n))
    (x : Fin n → F2) : columnValue ts x = supportValue (augmentationSupport ts) x := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [columnValue, augmentationSupport]
    split <;> simp_all [supportValue]

/-- The small support table can be reused only after it has been equated to
every full native column. It supplies no assumption about omitted generators. -/
def checkCombinationSupport {m n : Nat} (supports : Fin m → List (Fin n))
    (e : CombinationEntry m n) : Bool :=
  (List.finRange m).all (fun j =>
    decide (supportValue (supports j) (targetValue e.sources) = targetValue e.targets j))

theorem checkCombination_of_support {m n : Nat} (columns : Fin m → List (Term n))
    (supports : Fin m → List (Fin n)) (e : CombinationEntry m n)
    (hs : ∀ j, augmentationSupport (columns j) = supports j)
    (h : checkCombinationSupport supports e = true) : checkCombination columns e = true := by
  apply List.all_eq_true.mpr
  intro j _
  apply decide_eq_true
  rw [columnValue_augmentationSupport, hs j]
  exact of_decide_eq_true ((List.all_eq_true.mp h) j (List.mem_finRange j))

private theorem degreeFrom_zero_of_all (k : Nat) (xs : List Nat)
    (h : xs.all (· == 0) = true) : degreeFrom k xs = 0 := by
  induction xs generalizing k with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    simp [degreeFrom, h.1, ih (k+1) h.2]

theorem termLinear_eq_zero_of_degree_pos {n : Nat} (t : Term n)
    (h : 0 < t.degree) : termLinear t = 0 := by
  unfold termLinear
  split
  next ht =>
    have hz := degreeFrom_zero_of_all 0 t.powers ht
    change 0 < degreeFrom 0 t.powers at h
    omega
  next => rfl

def minimalCheck {m n : Nat} (columns : Fin m → List (Term n)) : Bool :=
  (List.finRange m).all (fun i => (columns i).all (fun t => decide (0 < t.degree)))

theorem minimalCheck_sound {m n : Nat} (columns : Fin m → List (Term n))
    (h : minimalCheck columns = true) :
    ∀ i, ∀ t ∈ columns i, 0 < t.degree := by
  intro i t ht
  have hi := (List.all_eq_true.mp h) i (List.mem_finRange i)
  exact of_decide_eq_true ((List.all_eq_true.mp hi) t ht)

private theorem columnLinear_eq_zero {n : Nat} (ts : List (Term n))
    (h : ∀ t ∈ ts, 0 < t.degree) : columnLinear ts = 0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [columnLinear, termLinear_eq_zero_of_degree_pos t (h t (by simp)),
      ih (fun t ht => h t (by simp [ht])), zero_add]

/-- Positive-degree native differential coefficients yield the zero dual
operator on all cochains of the specified finite family. This does not assert
that the finite data is an exact Steenrod resolution. -/
theorem pullback_eq_zero_of_minimalCheck {m n : Nat}
    (columns : Fin m → List (Term n)) (h : minimalCheck columns = true) :
    pullback columns = 0 := by
  apply LinearMap.ext
  intro x
  funext i
  change columnLinear (columns i) x = 0
  rw [columnLinear_eq_zero (columns i) (minimalCheck_sound columns h i)]
  rfl

end KIP126.LinModule.CochainMapCertificate
