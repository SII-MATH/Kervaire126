module

public import KIP126.Def.ClassicalAdams.Detection.Proofs
public import KIP126.Def.ClassicalAdams.TowerSSData.Permanence.Proofs
public import KIP126.Def.ClassicalAdams.TowerSequence.NextCycles.Proofs

@[expose] public section


namespace KIP126.Classical.Adams.TowerDetection
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory KIP126.StableHomotopy
universe u v
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)] {H : C} (unit : 𝟙_ C ⟶ H) (X : C)

/-- Vanishing of the whole second page raises the tower-image filtration.
The lift criterion compares the two lifts at stage `s - 1`; composing down
to stage `-1`, which is definitionally stage `0`, preserves their image in `X`. -/
theorem filtration_raise_of_pageTwo_subsingleton (s t : ℤ) (hs : 0 ≤ s)
    (h : Subsingleton ((adamsTowerInternalSpectralSequence unit X).Page 2 (s,t))) :
    filtrationSubmodule unit X s (t-s) ≤ filtrationSubmodule unit X (s+1) (t-s) := by
  rintro x ⟨a, ha⟩
  let e := adamsTowerSSDataPageIso unit X s t 0
  have hz : adamsJToPage unit X 2 (by decide) s t a = 0 := by
    apply e.toLinearEquiv.symm.injective
    exact h.elim _ _
  obtain ⟨c, hc⟩ := (adamsJToPage_eq_zero_iff unit X 2 (by decide) s t a).mp hz
  have hh := congrArg (adamsI unit X (t-s) (-1) (s-(2:ℕ)+1) (by omega)) hc
  rw [adamsI_comp, adamsI_comp] at hh
  exact ⟨c, hh.trans ha⟩

/-- All nonnegative E2 filtration pieces, not a finite window, are used. -/
theorem mem_all_filtrations_of_pageTwo_zero (n : ℤ)
    (h : ∀ s : ℕ, Subsingleton
      ((adamsTowerInternalSpectralSequence unit X).Page 2 ((s:ℤ),(s:ℤ)+n)))
    (x : HomotopyGroup n X) :
    ∀ s : ℕ, x ∈ filtrationSubmodule unit X s n := by
  intro s
  induction s with
  | zero =>
    refine ⟨x, ?_⟩
    change x ≫ adamsTowerMap unit X 0 0 (by omega) = x
    rw [adamsTowerMap_self]
    change x ≫ 𝟙 X = x
    exact Category.comp_id x
  | succ s ih =>
    have hr := filtration_raise_of_pageTwo_subsingleton unit X s (s+n) (by omega) (h s)
    have hn : (s:ℤ)+n-s = n := by omega
    rw [hn] at hr
    simpa only [Nat.cast_add, Nat.cast_one] using hr ih

/-- Full-stem second-page vanishing forces zero homotopy under explicit
separation of the tower filtration. No convergence witness is assumed. -/
theorem homotopy_eq_zero_of_pageTwo_zero_of_separated (n : ℤ)
    (h : ∀ s : ℕ, Subsingleton
      ((adamsTowerInternalSpectralSequence unit X).Page 2 ((s:ℤ),(s:ℤ)+n)))
    (hsep : ∀ x : HomotopyGroup n X,
      (∀ s : ℕ, x ∈ filtrationSubmodule unit X s n) → x = 0)
    (x : HomotopyGroup n X) : x = 0 :=
  hsep x (mem_all_filtrations_of_pageTwo_zero unit X n h x)

end
end KIP126.Classical.Adams.TowerDetection
