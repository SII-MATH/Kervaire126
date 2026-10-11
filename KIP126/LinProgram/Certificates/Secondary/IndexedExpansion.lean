module

public import KIP126.LinProgram.Certificates.Secondary.Expansion

@[expose] public section


namespace KIP126.Computation.Secondary
open MilnorCertificates

/-- Certificate table data; composition still uses the original `CompositionPath`. -/
structure ProductEntry where
  left : Monomial
  right : Monomial
  output : Polynomial
  deriving DecidableEq, Repr

/-- A certified table can assemble independently checked product blocks. -/
structure CertifiedProductEntry (rank : Nat) where
  entry : ProductEntry
  certified : IsMilnorProductAll rank [entry.left] [entry.right] entry.output

def certifiedProductTable (entries : Array (CertifiedProductEntry rank)) (id : Nat) :
    Option ProductEntry := entries[id]?.map (·.entry)

theorem certifiedProductTable_sound (entries : Array (CertifiedProductEntry rank))
    (id : Nat) (entry : ProductEntry) (h : certifiedProductTable entries id = some entry) :
    IsMilnorProductAll rank [entry.left] [entry.right] entry.output := by
  rcases Option.map_eq_some_iff.mp h with ⟨certified, _, rfl⟩
  exact certified.certified

/-- An untrusted plan refers to a required product and preserves its target. -/
structure IndexedPath where
  productId : Nat
  target : Nat
  deriving DecidableEq, Repr

theorem expressionCoefficient_perm {a b : ModuleExpression} (h : a.Perm b)
    (target : Nat) (m : Monomial) :
    expressionCoefficient a target m = expressionCoefficient b target m := by
  unfold expressionCoefficient coefficient
  rw [(((h.filter (fun t => t.generator == target)).map (·.sq)).filter (· == m)).length_eq]

/-- Cancel adjacent equal pairs. Sorting is a performance aid, not a soundness premise. -/
def cancelAdjacent : ModuleExpression → ModuleExpression
  | [] => []
  | [a] => [a]
  | a :: b :: rest => if a = b then cancelAdjacent rest else a :: cancelAdjacent (b :: rest)

theorem cancelAdjacent_sound (a : ModuleExpression) (target : Nat) (m : Monomial) :
    expressionCoefficient (cancelAdjacent a) target m = expressionCoefficient a target m := by
  induction a using cancelAdjacent.induct with
  | case1 => rfl
  | case2 a => rfl
  | case3 a rest ih =>
    simp only [cancelAdjacent, ↓reduceIte, expressionCoefficient_cons]
    rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
    exact ih
  | case4 a b rest h ih =>
    simp only [cancelAdjacent, h, ↓reduceIte, expressionCoefficient_cons]
    rw [ih, expressionCoefficient_cons]

def termLE (a b : ModuleTerm) : Bool :=
  (compareLex (fun x y : ModuleTerm => compare x.generator y.generator)
    (fun x y => compare x.sq y.sq) a b) != Ordering.gt

/-- Fuel exposes a structurally recursive merge to kernel reduction. -/
def mergeExpression : Nat → ModuleExpression → ModuleExpression → ModuleExpression
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a, [] => a
  | n + 1, a :: as, b :: bs =>
      if termLE a b then a :: mergeExpression n as (b :: bs)
      else b :: mergeExpression n (a :: as) bs

theorem mergeExpression_perm (fuel : Nat) (a b : ModuleExpression) :
    (mergeExpression fuel a b).Perm (a ++ b) := by
  induction fuel generalizing a b with
  | zero => simp [mergeExpression]
  | succ n ih =>
    cases a with
    | nil => simp [mergeExpression]
    | cons a as =>
      cases b with
      | nil => simp [mergeExpression]
      | cons b bs =>
        simp only [mergeExpression]
        split
        · exact (ih as (b :: bs)).cons a
        · exact ((ih (a :: as) bs).cons b).trans
            ((List.Perm.swap a b _).trans (List.perm_middle.symm.cons a))

/-- Fuelled mergesort avoids proof casts in the kernel's executable path. -/
def sortExpression : Nat → ModuleExpression → ModuleExpression
  | 0, a => a
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | n + 1, a :: b :: rest =>
      let xs := a :: b :: rest
      let k := xs.length / 2
      mergeExpression xs.length (sortExpression n (xs.take k))
        (sortExpression n (xs.drop k))

theorem sortExpression_perm (fuel : Nat) (a : ModuleExpression) :
    (sortExpression fuel a).Perm a := by
  induction fuel generalizing a with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases a with
    | nil => exact List.Perm.refl _
    | cons a as =>
      cases as with
      | nil => exact List.Perm.refl _
      | cons b rest =>
        simp only [sortExpression]
        apply (mergeExpression_perm _ _ _).trans
        have hp := List.Perm.append
          (ih ((a :: b :: rest).take ((a :: b :: rest).length / 2)))
          (ih ((a :: b :: rest).drop ((a :: b :: rest).length / 2)))
        simpa using hp

/-- A deterministic F₂ normalization in the original expression syntax. -/
def normalizeExpression (a : ModuleExpression) : ModuleExpression :=
  cancelAdjacent (sortExpression a.length a)

theorem normalizeExpression_sound (a : ModuleExpression) (target : Nat) (m : Monomial) :
    expressionCoefficient (normalizeExpression a) target m = expressionCoefficient a target m := by
  rw [normalizeExpression, cancelAdjacent_sound]
  exact expressionCoefficient_perm (sortExpression_perm a.length a) target m

def fastExpressionEqCheck (a b : ModuleExpression) : Bool :=
  decide (normalizeExpression a = normalizeExpression b)

theorem fastExpressionEqCheck_sound (a b : ModuleExpression)
    (h : fastExpressionEqCheck a b = true) (target : Nat) (m : Monomial) :
    expressionCoefficient a target m = expressionCoefficient b target m := by
  have he : normalizeExpression a = normalizeExpression b := of_decide_eq_true h
  rw [← normalizeExpression_sound a target m, he, normalizeExpression_sound]

/-- Missing product IDs fail, including when the missing product could have cancelled. -/
def indexedExpansion (table : Nat → Option ProductEntry) :
    List IndexedPath → Option (List CompositionPath × ModuleExpression)
  | [] => some ([], [])
  | p :: rest => do
      let entry ← table p.productId
      let tail ← indexedExpansion table rest
      pure ((⟨entry.left, entry.right, p.target⟩ : CompositionPath) :: tail.1,
        (entry.output.map fun m => (⟨m, p.target⟩ : ModuleTerm)) ++ tail.2)

theorem indexedExpansion_sound (rank : Nat) (table : Nat → Option ProductEntry)
    (plan : List IndexedPath) (paths : List CompositionPath) (out : ModuleExpression)
    (hp : ∀ id entry, table id = some entry →
      IsMilnorProductAll rank [entry.left] [entry.right] entry.output)
    (he : indexedExpansion table plan = some (paths, out)) :
    ∀ target m, m.length = rank →
      expressionCoefficient out target m = pathCoefficient rank target m paths := by
  induction plan generalizing paths out with
  | nil => simp only [indexedExpansion, Option.some.injEq, Prod.mk.injEq] at he
           rcases he with ⟨rfl, rfl⟩; intros; rfl
  | cons p plan ih =>
    cases hentry : table p.productId with
    | none => simp [indexedExpansion, hentry] at he
    | some entry =>
      cases htail : indexedExpansion table plan with
      | none => simp [indexedExpansion, hentry, htail] at he
      | some tail =>
        rcases tail with ⟨tailPaths, tailOut⟩
        simp [indexedExpansion, hentry, htail] at he
        rcases he with ⟨rfl, rfl⟩
        intro target m hm
        rw [expressionCoefficient_append, expressionCoefficient_at_target,
          ih tailPaths tailOut htail target m hm,
          (hp p.productId entry hentry).2.2.2 m hm]
        rfl

/-- Check every original resolved path before comparing all coefficients by normalization. -/
def indexedCompositionCheck (table : Nat → Option ProductEntry)
    (images : Nat → Option ModuleExpression) (a : ModuleExpression)
    (plan : List IndexedPath) (expected : ModuleExpression) : Bool :=
  match resolvePaths images a, indexedExpansion table plan with
  | some paths, some (plannedPaths, out) =>
      decide (paths = plannedPaths) && fastExpressionEqCheck out expected
  | _, _ => false

theorem indexedCompositionCheck_sound (rank : Nat) (table : Nat → Option ProductEntry)
    (images : Nat → Option ModuleExpression) (a : ModuleExpression)
    (plan : List IndexedPath) (expected : ModuleExpression)
    (hp : ∀ id entry, table id = some entry →
      IsMilnorProductAll rank [entry.left] [entry.right] entry.output)
    (hc : indexedCompositionCheck table images a plan expected = true) :
    compose rank images a = some (fun target m => expressionCoefficient expected target m.val) := by
  cases hr : resolvePaths images a with
  | none => simp [indexedCompositionCheck, hr] at hc
  | some paths =>
    cases he : indexedExpansion table plan with
    | none => simp [indexedCompositionCheck, hr, he] at hc
    | some expansion =>
      rcases expansion with ⟨plannedPaths, out⟩
      simp only [indexedCompositionCheck, hr, he, Bool.and_eq_true, decide_eq_true_eq] at hc
      rcases hc with ⟨rfl, hc⟩
      simp only [compose, hr, Option.map_some]
      congr 1
      funext target m
      exact (indexedExpansion_sound rank table plan paths out hp he target m.val m.property).symm.trans
        (fastExpressionEqCheck_sound out expected hc target m.val)

theorem indexedExpansion_none_of_missing (table : Nat → Option ProductEntry)
    (plan : List IndexedPath) (p : IndexedPath) (hmem : p ∈ plan)
    (hmissing : table p.productId = none) : indexedExpansion table plan = none := by
  induction plan with
  | nil => simp at hmem
  | cons q plan ih =>
    rcases List.mem_cons.mp hmem with he | hmem
    · subst q; simp [indexedExpansion, hmissing]
    · cases hq : table q.productId <;> simp [indexedExpansion, hq, ih hmem]

end KIP126.Computation.Secondary
