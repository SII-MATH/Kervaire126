module

public import KIP126.Def.StableHomotopy.Implementation.Suspension.HomotopyMap.Data
public import KIP126.Def.Topology.Cube.Rotation.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology KIP126.Topology.Cube
open scoped unitInterval Topology.Homotopy
universe u
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- The alternating orientation used by the suspension/desuspension comparison. -/
def suspensionDesuspensionSign (n : ℕ) : C(I, I) :=
  ⟨unitInterval.symm^[n], unitInterval.continuous_symm.iterate n⟩

@[simp] theorem suspensionDesuspensionSign_succ (n : ℕ) (s : I) :
    suspensionDesuspensionSign (n + 1) s = σ (suspensionDesuspensionSign n s) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem suspensionDesuspensionSign_twice (n : ℕ) (s : I) :
    suspensionDesuspensionSign n (suspensionDesuspensionSign n s) = s := by
  change (unitInterval.symm^[n]) ((unitInterval.symm^[n]) s) = s
  rw [← Function.iterate_add_apply]
  have htwo : unitInterval.symm^[2] = id := by funext t; exact unitInterval.symm_symm t
  rw [show n+n=2*n by omega, Function.iterate_mul, htwo]
  simp

theorem suspensionDesuspensionSign_boundary (n : ℕ) (s : I) (hs : s = 0 ∨ s = 1) :
    suspensionDesuspensionSign n s = 0 ∨ suspensionDesuspensionSign n s = 1 := by
  induction n with
  | zero => exact hs
  | succ n ih =>
      rw [suspensionDesuspensionSign_succ]
      rcases ih with h | h <;> simp [h]

variable (X : Prespectrum.{u})

theorem comparisonLevel_collapsed (n : ℕ) (p : X.level n × I)
    (hp : BasedSpace.SuspensionCollapsed (X.level n) p) :
    X.bond n (p.1, suspensionDesuspensionSign n p.2) = (X.level (n + 1)).point := by
  rcases hp with h | h | h
  · rw [h, X.bond_point]
  · rcases suspensionDesuspensionSign_boundary n p.2 (Or.inl h) with h' | h'
    · rw [h', X.bond_zero]
    · rw [h', X.bond_one]
  · rcases suspensionDesuspensionSign_boundary n p.2 (Or.inr h) with h' | h'
    · rw [h', X.bond_zero]
    · rw [h', X.bond_one]

/-- At a positive level, collapse suspension using the original bonding map
with its prescribed alternating interval orientation. -/
def suspensionDesuspensionLevelSucc (n : ℕ) : C((X.level n).suspension, X.level (n + 1)) := by
  let raw : C(X.level n × I, X.level (n + 1)) :=
    (X.bond n).comp ⟨fun p => (p.1, suspensionDesuspensionSign n p.2),
      continuous_fst.prodMk ((suspensionDesuspensionSign n).continuous.comp continuous_snd)⟩
  have hr : ∀ a b, BasedSpace.SuspensionRelation (X.level n) a b → raw a = raw b := by
    intro a b h
    exact (comparisonLevel_collapsed X n a h.1).trans (comparisonLevel_collapsed X n b h.2).symm
  exact ⟨Quot.lift raw hr, continuous_quot_lift hr raw.continuous⟩

@[simp] theorem suspensionDesuspensionLevelSucc_apply (n : ℕ) (x : X.level n) (s : I) :
    suspensionDesuspensionLevelSucc X n (BasedSpace.suspensionProjection _ (x,s)) =
      X.bond n (x, suspensionDesuspensionSign n s) := rfl

@[simp] theorem suspensionDesuspensionLevelSucc_point (n : ℕ) :
    suspensionDesuspensionLevelSucc X n (X.level n).suspension.point =
      (X.level (n + 1)).point := X.bond_point n _

/-- The rotation homotopy before passing to the suspension quotient. -/
def suspensionDesuspensionRotationRaw (n : ℕ) :
    C((X.level n × I) × (I × I), X.level (n + 2)) := by
  let r (z : (X.level n × I) × (I × I)) :=
    squareRotation (σ z.2.1) (suspensionDesuspensionSign n z.1.2, z.2.2)
  have htime : Continuous (fun z : (X.level n × I) × (I × I) => σ z.2.1) :=
    unitInterval.continuous_symm.comp continuous_snd.fst
  have hsign : Continuous (fun z : (X.level n × I) × (I × I) =>
      suspensionDesuspensionSign n z.1.2) :=
    (suspensionDesuspensionSign n).continuous.comp continuous_fst.snd
  have hlast : Continuous (fun z : (X.level n × I) × (I × I) => z.2.2) := continuous_snd.snd
  have hr : Continuous r := by
    change Continuous ((fun p : I × (I × I) => squareRotation p.1 p.2) ∘
      (fun z : (X.level n × I) × (I × I) =>
        (σ z.2.1, (suspensionDesuspensionSign n z.1.2, z.2.2))))
    exact continuous_squareRotation.comp (htime.prodMk (hsign.prodMk hlast))
  exact ⟨fun z => X.bond (n + 1) (X.bond n (z.1.1, (r z).1), (r z).2),
    (X.bond (n + 1)).continuous.comp
      (((X.bond n).continuous.comp (continuous_fst.fst.prodMk hr.fst)).prodMk hr.snd)⟩

private theorem comparisonRotation_boundary (n : ℕ) (x : X.level n) (p : I × I)
    (hp : p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) :
    X.bond (n + 1) (X.bond n (x,p.1),p.2) = (X.level (n + 2)).point := by
  rcases hp with h | h | h | h
  · rw [h, X.bond_zero, X.bond_point]
  · rw [h, X.bond_one, X.bond_point]
  · rw [h, X.bond_zero]
  · rw [h, X.bond_one]

theorem comparisonRotation_collapsed (n : ℕ) (p : X.level n × I) (q : I × I)
    (hp : BasedSpace.SuspensionCollapsed (X.level n) p) :
    suspensionDesuspensionRotationRaw X n (p,q) = (X.level (n + 2)).point := by
  change X.bond (n + 1)
    (X.bond n (p.1, (squareRotation (σ q.1) (suspensionDesuspensionSign n p.2,q.2)).1),
      (squareRotation (σ q.1) (suspensionDesuspensionSign n p.2,q.2)).2) = _
  rcases hp with h | h | h
  · rw [h, X.bond_point, X.bond_point]
  · apply comparisonRotation_boundary
    apply squareRotation_preserves_boundary
    rcases suspensionDesuspensionSign_boundary n p.2 (Or.inl h) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · apply comparisonRotation_boundary
    apply squareRotation_preserves_boundary
    rcases suspensionDesuspensionSign_boundary n p.2 (Or.inr h) with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')

/-- The rotation descends because the entire square boundary stays collapsed. -/
def suspensionDesuspensionRotation (n : ℕ) :
    C((X.level n).suspension × (I × I), X.level (n + 2)) := by
  have hr (q : I × I) : ∀ a b, BasedSpace.SuspensionRelation (X.level n) a b →
      suspensionDesuspensionRotationRaw X n (a,q) = suspensionDesuspensionRotationRaw X n (b,q) := by
    intro a b h
    exact (comparisonRotation_collapsed X n a q h.1).trans (comparisonRotation_collapsed X n b q h.2).symm
  refine ⟨fun z => Quot.lift (fun a => suspensionDesuspensionRotationRaw X n (a,z.2))
    (hr z.2) z.1, ?_⟩
  apply isQuotientMap_quot_mk.continuous_lift_prod_left
  exact (suspensionDesuspensionRotationRaw X n).continuous

@[simp] theorem suspensionDesuspensionRotation_zero (n : ℕ)
    (x : X.level n) (s t : I) :
    suspensionDesuspensionRotation X n (BasedSpace.suspensionProjection _ (x,s),(0,t)) =
      X.bond (n + 1) (X.bond n (x,t),suspensionDesuspensionSign (n+1) s) := by
  change X.bond (n + 1)
    (X.bond n (x,(squareRotation (σ 0) (suspensionDesuspensionSign n s,t)).1),
      (squareRotation (σ 0) (suspensionDesuspensionSign n s,t)).2) = _
  rw [unitInterval.symm_zero, squareRotation_one, suspensionDesuspensionSign_succ]

@[simp] theorem suspensionDesuspensionRotation_one (n : ℕ)
    (x : X.level n) (s t : I) :
    suspensionDesuspensionRotation X n (BasedSpace.suspensionProjection _ (x,s),(1,t)) =
      X.bond (n + 1) (X.bond n (x,suspensionDesuspensionSign n s),t) := by
  change X.bond (n + 1)
    (X.bond n (x,(squareRotation (σ 1) (suspensionDesuspensionSign n s,t)).1),
      (squareRotation (σ 1) (suspensionDesuspensionSign n s,t)).2) = _
  rw [unitInterval.symm_one, squareRotation_zero]

/-- Suspension followed by padded desuspension compares to the original
spectrum through an explicit rotation of its two bonding coordinates. -/
def suspensionDesuspensionComparison : HomotopyMap (desuspension X).suspension X where
  level
    | 0 => ContinuousMap.const _ (X.level 0).point
    | n+1 => suspensionDesuspensionLevelSucc X n
  point := by
    intro n
    cases n with
    | zero => rfl
    | succ n => exact suspensionDesuspensionLevelSucc_point X n
  bondHomotopy
    | 0 => ContinuousMap.const _ (X.level 1).point
    | n+1 => (suspensionDesuspensionRotation X n).comp
        ⟨fun z => (z.2.1,(z.1,z.2.2)), continuous_snd.fst.prodMk (continuous_fst.prodMk continuous_snd.snd)⟩
  bondHomotopy_zero := by
    intro n x t
    cases n with
    | zero =>
        refine Quot.inductionOn x ?_
        intro p
        change (X.level 1).point = X.bond 0 ((X.level 0).point, suspensionDesuspensionSign 0 p.2)
        exact (X.bond_point 0 _).symm
    | succ n =>
        refine Quot.inductionOn x ?_
        rintro ⟨x,s⟩
        exact suspensionDesuspensionRotation_zero X n x s t
  bondHomotopy_one := by
    intro n x t
    cases n with
    | zero => exact (X.bond_point 0 t).symm
    | succ n =>
        refine Quot.inductionOn x ?_
        rintro ⟨x,s⟩
        exact suspensionDesuspensionRotation_one X n x s t
  bondHomotopy_collapsed := by
    intro n u x t h
    cases n with
    | zero => rfl
    | succ n =>
        rcases h with h | h | h
        · subst x
          exact comparisonRotation_collapsed X n ((X.level n).point,0) (u,t) (Or.inl rfl)
        · subst t
          refine Quot.inductionOn x ?_
          rintro ⟨x,s⟩
          apply comparisonRotation_boundary
          apply squareRotation_preserves_boundary
          exact Or.inr (Or.inr (Or.inl rfl))
        · subst t
          refine Quot.inductionOn x ?_
          rintro ⟨x,s⟩
          apply comparisonRotation_boundary
          apply squareRotation_preserves_boundary
          exact Or.inr (Or.inr (Or.inr rfl))

@[simp] theorem suspensionDesuspensionComparison_level_succ_apply
    (n : ℕ) (x : X.level n) (s : I) :
    (suspensionDesuspensionComparison X).level (n + 1)
      (BasedSpace.suspensionProjection _ (x,s)) = X.bond n (x,suspensionDesuspensionSign n s) := rfl

end
end KIP126.StableHomotopy.Implementation.Prespectrum
