module

public import KIP126.LinProgram.Certificates.Secondary.Proofs

@[expose] public section


namespace KIP126.Computation.Secondary
open MilnorCertificates

theorem expressionCoefficient_append (a b : ModuleExpression) (target : Nat) (m : Monomial) :
    expressionCoefficient (a ++ b) target m =
      xor (expressionCoefficient a target m) (expressionCoefficient b target m) := by
  simp only [expressionCoefficient, List.filter_append, List.map_append, coefficient_append]

theorem expressionCoefficient_singleton (t : ModuleTerm) (target : Nat) (m : Monomial) :
    expressionCoefficient [t] target m = decide (t.generator = target ∧ t.sq = m) := by
  by_cases hg : t.generator = target <;> by_cases hm : t.sq = m <;>
    simp [expressionCoefficient, coefficient, hg, hm]

theorem expressionCoefficient_cons (t : ModuleTerm) (a : ModuleExpression)
    (target : Nat) (m : Monomial) :
    expressionCoefficient (t :: a) target m =
      xor (decide (t.generator = target ∧ t.sq = m)) (expressionCoefficient a target m) := by
  change expressionCoefficient ([t] ++ a) target m = _
  rw [expressionCoefficient_append, expressionCoefficient_singleton]

theorem expressionCoefficient_duplicate_cancel (a : ModuleExpression) (target : Nat) (m : Monomial) :
    expressionCoefficient (a ++ a) target m = false := by
  rw [expressionCoefficient_append, Bool.xor_self]

theorem expressionCoefficient_of_not_mem (a : ModuleExpression) (target : Nat) (m : Monomial)
    (h : (⟨m, target⟩ : ModuleTerm) ∉ a) : expressionCoefficient a target m = false := by
  induction a with
  | nil => rfl
  | cons t a ih =>
    have ht : ¬ (t.generator = target ∧ t.sq = m) := by
      rintro ⟨hg, hm⟩
      have he : t = (⟨m, target⟩ : ModuleTerm) := by cases t; simp_all
      exact h (by simp [he])
    rw [expressionCoefficient_cons, decide_eq_false ht, Bool.false_xor]
    exact ih (fun ha => h (List.mem_cons_of_mem _ ha))

/-- The finite support is the union of both full expressions, not a degree window. -/
def expressionEqCheck (a b : ModuleExpression) : Bool :=
  (a ++ b).all fun t => expressionCoefficient a t.generator t.sq ==
    expressionCoefficient b t.generator t.sq

theorem expressionEqCheck_sound (a b : ModuleExpression)
    (h : expressionEqCheck a b = true) (target : Nat) (m : Monomial) :
    expressionCoefficient a target m = expressionCoefficient b target m := by
  by_cases hm : (⟨m, target⟩ : ModuleTerm) ∈ a ++ b
  · exact beq_iff_eq.mp ((List.all_eq_true.mp h) _ hm)
  · rw [expressionCoefficient_of_not_mem a target m (fun ha => hm (List.mem_append_left _ ha)),
      expressionCoefficient_of_not_mem b target m (fun hb => hm (List.mem_append_right _ hb))]

/-- Check an untrusted duplicate-free F₂ normalization in the original syntax. -/
def normalizationCheck (a normal : ModuleExpression) : Bool :=
  decide normal.Nodup && expressionEqCheck a normal

theorem normalizationCheck_sound (a normal : ModuleExpression)
    (h : normalizationCheck a normal = true) :
    normal.Nodup ∧ ∀ target m, expressionCoefficient a target m =
      expressionCoefficient normal target m := by
  simp only [normalizationCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, expressionEqCheck_sound a normal h.2⟩

/-- An absent certified product is a failure, not an empty polynomial. -/
def expandPaths (products : Monomial → Monomial → Option Polynomial) :
    List CompositionPath → Option ModuleExpression
  | [] => some []
  | p :: rest => do
      let product ← products p.left p.right
      let tail ← expandPaths products rest
      pure ((product.map fun m => (⟨m, p.target⟩ : ModuleTerm)) ++ tail)

theorem expressionCoefficient_at_target (p : Polynomial) (slot target : Nat) (m : Monomial) :
    expressionCoefficient (p.map fun sq => (⟨sq, slot⟩ : ModuleTerm)) target m =
      if slot = target then coefficient p m else false := by
  by_cases h : slot = target
  · subst target
    simp [expressionCoefficient, List.filter_map, Function.comp_def]
  · have hb : (slot == target) = false := beq_eq_false_iff_ne.mpr h
    simp [expressionCoefficient, List.filter_map, hb, h, coefficient]

theorem expandPaths_sound (rank : Nat)
    (products : Monomial → Monomial → Option Polynomial)
    (paths : List CompositionPath) (out : ModuleExpression)
    (hp : ∀ p ∈ paths, ∀ product, products p.left p.right = some product →
      IsMilnorProductAll rank [p.left] [p.right] product)
    (he : expandPaths products paths = some out) :
    ∀ target m, m.length = rank →
      expressionCoefficient out target m = pathCoefficient rank target m paths := by
  induction paths generalizing out with
  | nil => simp only [expandPaths, Option.some.injEq] at he; subst out; intros; rfl
  | cons p paths ih =>
    cases hprod : products p.left p.right with
    | none => simp [expandPaths, hprod] at he
    | some product =>
      cases htail : expandPaths products paths with
      | none => simp [expandPaths, hprod, htail] at he
      | some tail =>
        simp [expandPaths, hprod, htail] at he
        subst out
        intro target m hm
        rw [expressionCoefficient_append, expressionCoefficient_at_target]
        rw [ih tail (fun q hq => hp q (List.mem_cons_of_mem _ hq)) htail target m hm]
        rw [(hp p (by simp) product hprod).2.2.2 m hm]
        rfl

def expandCompose (products : Monomial → Monomial → Option Polynomial)
    (images : Nat → Option ModuleExpression) (a : ModuleExpression) : Option ModuleExpression := do
  let paths ← resolvePaths images a
  expandPaths products paths

theorem expandPaths_none_of_missing
    (products : Monomial → Monomial → Option Polynomial)
    (paths : List CompositionPath) (p : CompositionPath)
    (hmem : p ∈ paths) (hmissing : products p.left p.right = none) :
    expandPaths products paths = none := by
  induction paths with
  | nil => simp at hmem
  | cons q paths ih =>
    rcases List.mem_cons.mp hmem with he | hmem
    · subst q
      simp [expandPaths, hmissing]
    · have ht := ih hmem
      cases hq : products q.left q.right <;> simp [expandPaths, hq, ht]

theorem resolvePaths_none_of_missing (images : Nat → Option ModuleExpression)
    (a : ModuleExpression) (term : ModuleTerm) (hmem : term ∈ a)
    (hmissing : images term.generator = none) : resolvePaths images a = none := by
  induction a with
  | nil => simp at hmem
  | cons q a ih =>
    rcases List.mem_cons.mp hmem with he | hmem
    · subst q
      simp [resolvePaths, hmissing]
    · have ht := ih hmem
      cases hq : images q.generator <;> simp [resolvePaths, hq, ht]

theorem expandCompose_none_of_missing_image
    (products : Monomial → Monomial → Option Polynomial)
    (images : Nat → Option ModuleExpression) (a : ModuleExpression)
    (term : ModuleTerm) (hmem : term ∈ a) (hmissing : images term.generator = none) :
    expandCompose products images a = none := by
  simp [expandCompose, resolvePaths_none_of_missing images a term hmem hmissing]

theorem expandCompose_none_of_missing_product
    (products : Monomial → Monomial → Option Polynomial)
    (images : Nat → Option ModuleExpression) (a : ModuleExpression)
    (paths : List CompositionPath) (hr : resolvePaths images a = some paths)
    (p : CompositionPath) (hmem : p ∈ paths) (hmissing : products p.left p.right = none) :
    expandCompose products images a = none := by
  simp [expandCompose, hr, expandPaths_none_of_missing products paths p hmem hmissing]

theorem compose_of_expansion (rank : Nat)
    (products : Monomial → Monomial → Option Polynomial)
    (images : Nat → Option ModuleExpression) (a out : ModuleExpression)
    (hp : ∀ paths, resolvePaths images a = some paths → ∀ p ∈ paths,
      ∀ product, products p.left p.right = some product →
        IsMilnorProductAll rank [p.left] [p.right] product)
    (he : expandCompose products images a = some out) :
    compose rank images a = some (fun target m => expressionCoefficient out target m.val) := by
  cases hr : resolvePaths images a with
  | none => simp [expandCompose, hr] at he
  | some paths =>
    simp [expandCompose, hr] at he
    simp only [compose, hr, Option.map_some]
    congr 1
    funext target m
    exact (expandPaths_sound rank products paths out (hp paths hr) he target m.val m.property).symm

theorem compose_of_checked_expansion (rank : Nat)
    (products : Monomial → Monomial → Option Polynomial)
    (images : Nat → Option ModuleExpression) (a out normal : ModuleExpression)
    (hp : ∀ paths, resolvePaths images a = some paths → ∀ p ∈ paths,
      ∀ product, products p.left p.right = some product →
        IsMilnorProductAll rank [p.left] [p.right] product)
    (he : expandCompose products images a = some out)
    (hn : expressionEqCheck out normal = true) :
    compose rank images a = some (fun target m => expressionCoefficient normal target m.val) := by
  rw [compose_of_expansion rank products images a out hp he]
  congr 1
  funext target m
  exact expressionEqCheck_sound out normal hn target m.val

/-- No source-image or product lookup failure is accepted as zero. -/
def compositionCheck (products : Monomial → Monomial → Option Polynomial)
    (images : Nat → Option ModuleExpression) (a expected : ModuleExpression) : Bool :=
  match expandCompose products images a with
  | none => false
  | some out => expressionEqCheck out expected

theorem compositionCheck_sound (rank : Nat)
    (products : Monomial → Monomial → Option Polynomial)
    (images : Nat → Option ModuleExpression) (a expected : ModuleExpression)
    (hp : ∀ left right product, products left right = some product →
      IsMilnorProductAll rank [left] [right] product)
    (hc : compositionCheck products images a expected = true) :
    compose rank images a = some (fun target m => expressionCoefficient expected target m.val) := by
  cases he : expandCompose products images a with
  | none => simp [compositionCheck, he] at hc
  | some out =>
    simp only [compositionCheck, he] at hc
    exact compose_of_checked_expansion rank products images a out expected
      (fun _ _ p _ => hp p.left p.right) he hc

end KIP126.Computation.Secondary
