module

public import KIP126.LinProgram.Certificates.Secondary.Proofs

@[expose] public section


namespace KIP126.Computation.Secondary
open MilnorCertificates

/-- Enumerate every monomial of exactly the requested weight. -/
def degreeBasis : Nat → Nat → List Monomial
  | 0, d => if d = 0 then [[]] else []
  | r + 1, d => (List.range (d+1)).flatMap fun e =>
      if e * (2^(r+1)-1) ≤ d then
        (degreeBasis r (d - e * (2^(r+1)-1))).map (fun m => m ++ [e])
      else []

theorem weight_append_singleton (m : Monomial) (e : Nat) :
    weight (m ++ [e]) = weight m + e * (2^(m.length+1)-1) := by
  rw [weight_eq_coordinateWeight, weight_eq_coordinateWeight]
  simp only [List.length_append, List.length_singleton]
  unfold coordinateWeight
  rw [Finset.sum_range_succ]
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [List.getElem?_append_left (Finset.mem_range.mp hj)]

theorem degreeBasis_mem (r d : Nat) (m : Monomial) :
    m ∈ degreeBasis r d ↔ m.length = r ∧ weight m = d := by
  induction r generalizing d m with
  | zero =>
    by_cases hd : d = 0 <;> cases m <;> simp_all [degreeBasis, weight, eq_comm]
  | succ r ih =>
    constructor
    · intro hm
      simp only [degreeBasis, List.mem_flatMap] at hm
      obtain ⟨e, he, hm⟩ := hm
      split at hm
      next h =>
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
        obtain ⟨hlen, hw⟩ := (ih _ a).mp ha
        refine ⟨by simp [hlen], ?_⟩
        rw [weight_append_singleton, hlen, hw]
        omega
      next h => simp at hm
    · rintro ⟨hm, hw⟩
      have hn : m ≠ [] := by intro h; simp [h] at hm
      obtain ⟨a, e, rfl⟩ := (List.eq_nil_or_concat' m).resolve_left hn
      have ha : a.length = r := by simpa using hm
      rw [weight_append_singleton, ha] at hw
      have hp : 0 < 2^(r+1)-1 := by
        have h : 2^1 ≤ 2^(r+1) := Nat.pow_le_pow_right (by omega) (by omega)
        simp only [Nat.pow_one] at h
        omega
      have hed : e * (2^(r+1)-1) ≤ d := by omega
      have he : e < d+1 := by
        have h := Nat.le_mul_of_pos_right e hp
        omega
      apply List.mem_flatMap.mpr
      refine ⟨e, List.mem_range.mpr he, ?_⟩
      rw [if_pos hed]
      apply List.mem_map.mpr
      refine ⟨a, (ih _ a).mpr ⟨ha, ?_⟩, rfl⟩
      omega

/-- Check the entire homogeneous output degree; other degrees are excluded
by the existing all-degree support theorem, rather than a truncated statement. -/
def homogeneousProductCheck (rank d e : Nat) (left right output : Polynomial) : Bool :=
  left.all (fun m => m.length == rank && weight m == d) &&
  right.all (fun m => m.length == rank && weight m == e) &&
  output.all (fun m => m.length == rank && weight m == d+e) &&
  (degreeBasis rank (d+e)).all fun m =>
    coefficient output m == pairTensor left right (coproduct rank m)

theorem homogeneousProductCheck_sound (rank d e : Nat) (left right output : Polynomial)
    (h : homogeneousProductCheck rank d e left right output = true) :
    IsMilnorProductAll rank left right output := by
  simp only [homogeneousProductCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hl, hr⟩, ho⟩, hc⟩ := h
  have all_spec (p : Polynomial) (n : Nat)
      (h : p.all (fun m => m.length == rank && weight m == n) = true) :
      ∀ m ∈ p, m.length = rank ∧ weight m = n := by
    intro m hm
    have hh := (List.all_eq_true.mp h) m hm
    simpa only [Bool.and_eq_true, beq_iff_eq] using hh
  have hleft := all_spec left d hl
  have hright := all_spec right e hr
  have hout := all_spec output (d+e) ho
  refine ⟨fun m hm => (hleft m hm).1, fun m hm => (hright m hm).1,
    fun m hm => (hout m hm).1, ?_⟩
  intro m hm
  by_cases hd : weight m = d+e
  · have hh := (List.all_eq_true.mp hc) m ((degreeBasis_mem rank (d+e) m).mpr ⟨hm, hd⟩)
    exact of_decide_eq_true hh
  · rw [product_degree_support rank d e left right
      (fun m hm => (hleft m hm).2) (fun m hm => (hright m hm).2) m hm hd]
    cases he : coefficient output m
    · rfl
    · exact False.elim (hd (hout m (coefficient_true_mem output m he)).2)

end KIP126.Computation.Secondary
