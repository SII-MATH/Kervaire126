import KIP126.Def.StableHomotopy.TowerSpectralSequence.Differential.Proofs

/-! The next-cycle and next-boundary arguments on the existing actual tower.
These are the exact-couple representative arguments used in KIPBase's
geometric Adams pages, without introducing another page construction. -/
namespace KIP126.StableHomotopy.TowerSpectralSequence
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)] (T : DescendingTower C) (P : C)

omit [HasFunctorialCofiber (C := C)] in
@[simp] theorem I_comp (n s t z : ℤ) (hst : s ≤ t) (htz : t ≤ z)
    (x : ShiftedHom P n (T.obj z)) :
    I T P n s t hst (I T P n t z htz x) = I T P n s z (hst.trans htz) x := by
  change (x ≫ _) ≫ _ = x ≫ _
  rw [Category.assoc, T.map_comp]

omit [HasFunctorialCofiber (C := C)] in
theorem I_range_eq (n a s t : ℤ) (hst : s = t) (has : a ≤ s) :
    LinearMap.range (I T P n a s has) = LinearMap.range (I T P n a t (by omega)) := by
  subst t
  rfl

theorem JToPage_I_zero (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (y : ShiftedHom P n (T.obj (k + 1))) :
    JToPage T P q hq k n (I T P n k (k + 1) (by omega) y) = 0 := by
  have hj : J T P k n (I T P n k (k + 1) (by omega) y) = 0 := by
    have h := (RepresentedHom.exact_f P (T.layerCofiberSequence k) n _).2 ⟨y, rfl⟩
    simpa only [I, J, RepresentedHom.postcomposeLinearMap_apply, T.map_adjacent, DescendingTower.layerCofiberSequence, K] using h
  have hc : JToCycles T P q hq k n (I T P n k (k + 1) (by omega) y) = 0 := Subtype.ext hj
  change (cycleBoundaries T P q hq k n).mkQ _ = 0
  rw [hc, map_zero]

theorem JToPage_eq_zero_iff (q : ℕ) (hq : 1 ≤ q) (k n a : ℤ)
    (ha : a = k - q + 1) (y : ShiftedHom P n (T.obj k)) :
    JToPage T P q hq k n y = 0 ↔
      ∃ z : ShiftedHom P n (T.obj (k + 1)),
        I T P n a (k + 1) (by omega) z = I T P n a k (by omega) y := by
  subst a
  constructor
  · intro h
    have hb : J T P k n y ∈ boundaries T P q hq k n :=
      (Submodule.Quotient.mk_eq_zero (cycleBoundaries T P q hq k n)).mp h
    obtain ⟨w, hw, hj⟩ := hb
    have he : J T P k n (y - w) = 0 := by rw [map_sub, hj, sub_self]
    obtain ⟨z, hz⟩ := (RepresentedHom.exact_f P (T.layerCofiberSequence k) n (y - w)).1 he
    have hz' : I T P n k (k + 1) (by omega) z = y - w := by
      simpa only [I, RepresentedHom.postcomposeLinearMap_apply, T.map_adjacent, DescendingTower.layerCofiberSequence, K] using hz
    refine ⟨z, ?_⟩
    rw [← I_comp T P n (k - q + 1) k (k + 1) (by omega) (by omega), hz', map_sub]
    change I T P n (k - q + 1) k _ w = 0 at hw
    rw [hw, sub_zero]
  · rintro ⟨z, hz⟩
    rw [JToPage_eq T P q hq k n y (I T P n k (k + 1) (by omega) z) (by
      rw [I_comp, hz])]
    exact JToPage_I_zero T P q hq k n z

/-- The differential kernel is exactly the next cycle condition on the same representative. -/
theorem differentialValue_eq_zero_iff (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : cycles T P q hq k n) :
    differentialValue T P q hq k n x = 0 ↔ x.val ∈ cycles T P (q + 1) (by omega) k n := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (JToPage_eq_zero_iff T P q hq (k + q) (n - 1) (k + 1)
      (by omega) (cycleLift T P q hq k n x)).1 h
    rw [cycleLift_spec] at hz
    change K T P k n x ∈ LinearMap.range _
    rw [← I_range_eq T P (n - 1) (k + 1) ((k + q) + 1) (k + (q + 1 : ℕ))
      (by omega) (by omega)]
    exact ⟨z, hz⟩
  · intro hx
    change K T P k n x ∈ LinearMap.range _ at hx
    rw [← I_range_eq T P (n - 1) (k + 1) ((k + q) + 1) (k + (q + 1 : ℕ))
      (by omega) (by omega)] at hx
    obtain ⟨z, hz⟩ := hx
    rw [differentialValue_eq_of_lift T P q hq k n x
      (I T P (n - 1) (k + q) ((k + q) + 1) (by omega) z) (by
        rw [I_comp]
        exact hz)]
    exact JToPage_I_zero T P q hq (k + q) (n - 1) z

omit [HasFunctorialCofiber (C := C)] in
theorem I_image_zero_iff (n a b s : ℤ) (hab : a = b) (has : a ≤ s)
    (x : ShiftedHom P n (T.obj s)) :
    I T P n a s has x = 0 ↔ I T P n b s (by omega) x = 0 := by
  subst b
  rfl

theorem I_K_zero (k n : ℤ) (x : E1 T P k n) :
    I T P (n - 1) k (k + 1) (by omega) (K T P k n x) = 0 := by
  have h := (RepresentedHom.exact_h P (T.layerCofiberSequence k) n _).2 ⟨x, rfl⟩
  simpa only [I, RepresentedHom.postcomposeLinearMap_apply, T.map_adjacent, DescendingTower.layerCofiberSequence, K] using h

/-- Exactness produces a cycle with any specified lift killed one stage below. -/
theorem cycle_of_lift (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (y : ShiftedHom P (n - 1) (T.obj (k + q)))
    (hy : I T P (n - 1) k (k + q) (by omega) y = 0) :
    ∃ x : cycles T P q hq k n,
      K T P k n x = I T P (n - 1) (k + 1) (k + q) (by omega) y := by
  let a := I T P (n - 1) (k + 1) (k + q) (by omega) y
  have ha : I T P (n - 1) k (k + 1) (by omega) a = 0 := by
    dsimp only [a]
    rw [I_comp, hy]
  have ha' : postcomposeLinearMap P (n - 1) (T.layerCofiberSequence k).f a = 0 := by
    simpa only [I, RepresentedHom.postcomposeLinearMap_apply, T.map_adjacent, DescendingTower.layerCofiberSequence, K] using ha
  obtain ⟨x, hx⟩ := (RepresentedHom.exact_h P (T.layerCofiberSequence k) n a).1 ha'
  exact ⟨⟨x, ⟨y, hx.symm⟩⟩, hx⟩

theorem differential_lift_boundary (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : cycles T P q hq k n) :
    J T P (k + q) (n - 1) (cycleLift T P q hq k n x) ∈
      boundaries T P (q + 1) (by omega) (k + q) (n - 1) := by
  refine ⟨cycleLift T P q hq k n x, ?_, rfl⟩
  change I T P (n - 1) (k + q - (q + 1 : ℕ) + 1) (k + q) _ _ = 0
  apply (I_image_zero_iff T P (n - 1) _ k (k + q) (by omega) (by omega) _).2
  rw [← I_comp T P (n - 1) k (k + 1) (k + q) (by omega) (by omega),
    cycleLift_spec, I_K_zero]

/-- A quotient class is hit by the differential exactly when its representative
is a boundary on the next page. -/
theorem differential_range_iff (q : ℕ) (hq : 1 ≤ q) (k n : ℤ)
    (x : cycles T P q hq (k + q) (n - 1)) :
    (∃ y : page T P q hq k n, differential T P q hq k n y =
      (cycleBoundaries T P q hq (k + q) (n - 1)).mkQ x) ↔
    x.val ∈ boundaries T P (q + 1) (by omega) (k + q) (n - 1) := by
  constructor
  · rintro ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      have he : J T P (k + q) (n - 1) (cycleLift T P q hq k n y) - x.val ∈
          boundaries T P q hq (k + q) (n - 1) :=
        (Submodule.Quotient.eq (cycleBoundaries T P q hq (k + q) (n - 1))).1 hy
      have hm := (boundaries T P (q + 1) (by omega) (k + q) (n - 1)).sub_mem
        (differential_lift_boundary T P q hq k n y)
        (boundaries_monotone T P q (q + 1) hq (by omega) (Nat.le_succ q) (k + q) (n - 1) he)
      simpa only [sub_sub_cancel] using hm
  · rintro ⟨y, hy, hj⟩
    have hy' : I T P (n - 1) k (k + q) (by omega) y = 0 :=
      (I_image_zero_iff T P (n - 1) _ k (k + q) (by omega) (by omega) y).1 hy
    obtain ⟨z, hz⟩ := cycle_of_lift T P q hq k n y hy'
    refine ⟨(cycleBoundaries T P q hq k n).mkQ z, ?_⟩
    rw [differential_mk, differentialValue_eq_of_lift T P q hq k n z y hz.symm]
    change (cycleBoundaries T P q hq (k + q) (n - 1)).mkQ (JToCycles T P q hq (k + q) (n - 1) y) = _
    exact congrArg (cycleBoundaries T P q hq (k + q) (n - 1)).mkQ (Subtype.ext hj)

end KIP126.StableHomotopy.TowerSpectralSequence
