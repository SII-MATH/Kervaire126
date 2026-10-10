import KIP126.LinProgram.Certificates.Milnor.RankStability
import KIP126.LinProgram.Certificates.Milnor.GeneralTactic

namespace MilnorCertificates

theorem isMilnorProductAll_pad (rank d e bound : Nat) (left right output : Polynomial)
    (h : IsMilnorProductAll rank left right output)
    (hl : ∀ m ∈ left, weight m = d) (hr : ∀ m ∈ right, weight m = e)
    (ho : ∀ m ∈ output, weight m ≤ bound)
    (hde : d+e ≤ bound) (henough : bound < 2^(rank+1)-1) :
    IsMilnorProductAll (rank+1) (left.map pad) (right.map pad) (output.map pad) := by
  have lengths (p : Polynomial) (hp : ∀ m ∈ p, m.length = rank) :
      ∀ m ∈ p.map pad, m.length = rank+1 := by
    intro m hm
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    simp [pad,hp a ha]
  refine ⟨lengths left h.1,lengths right h.2.1,lengths output h.2.2.1,?_⟩
  intro m hm
  by_cases hw : weight m ≤ bound
  · have hp := bounded_succ_is_pad m rank bound hm hw henough
    conv_lhs => rw [hp]
    rw [coefficient_pad,bounded_rank_stability rank bound left right m hm hw henough]
    apply h.2.2.2
    simp [hm]
  · have hmout : m ∉ output.map pad := by
      intro hh
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hh
      exact hw (by rw [pad_weight]; exact ho a ha)
    have hcoeff : coefficient (output.map pad) m = false := by
      cases hc : coefficient (output.map pad) m
      · rfl
      · exact False.elim (hmout (coefficient_true_mem _ _ hc))
    rw [hcoeff]
    symm
    apply product_degree_support (rank+1) d e _ _ ?_ ?_ m hm (by omega)
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      rw [pad_weight,hl b hb]
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
      rw [pad_weight,hr b hb]

/-- A sufficiently large finite rank supports the same all-degree product
after any number of unused generators is adjoined. -/
theorem isMilnorProductAll_padMany (rank extra d e bound : Nat) (left right output : Polynomial)
    (h : IsMilnorProductAll rank left right output)
    (hl : ∀ m ∈ left, weight m = d) (hr : ∀ m ∈ right, weight m = e)
    (ho : ∀ m ∈ output, weight m ≤ bound)
    (hde : d+e ≤ bound) (henough : bound < 2^(rank+1)-1) :
    IsMilnorProductAll (rank+extra) (left.map (padMany extra))
      (right.map (padMany extra)) (output.map (padMany extra)) := by
  induction extra with
  | zero => simpa [padMany] using h
  | succ n ih =>
    have wt (a : Monomial) : weight (padMany n a) = weight a := by
      clear ih
      induction n with
      | zero => rfl
      | succ n ih => rw [padMany,pad_weight,ih]
    have hp : bound < 2^(rank+n+1)-1 := by
      have := Nat.pow_le_pow_right (n:=2) (by omega) (show rank+1 ≤ rank+n+1 by omega)
      omega
    have hh := isMilnorProductAll_pad (rank+n) d e bound _ _ _ ih
      (fun a ha => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; rw [wt,hl b hb])
      (fun a ha => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; rw [wt,hr b hb])
      (fun a ha => by obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha; rw [wt]; exact ho b hb) hde hp
    simpa [List.map_map,padMany,Function.comp_def,Nat.add_assoc] using hh

/-- The common minimal window choice: bound is precisely the input degree sum. -/
theorem stable_product (rank extra d e : Nat) (left right output : Polynomial)
    (h : IsMilnorProductAll rank left right output)
    (hl : ∀ m ∈ left, weight m = d) (hr : ∀ m ∈ right, weight m = e)
    (ho : ∀ m ∈ output, weight m ≤ d+e)
    (henough : d+e < 2^(rank+1)-1) :
    IsMilnorProductAll (rank+extra) (left.map (padMany extra))
      (right.map (padMany extra)) (output.map (padMany extra)) :=
  isMilnorProductAll_padMany rank extra d e (d+e) left right output h hl hr ho (by omega) henough

theorem sqOne_square_all_higher_ranks (extra : Nat) :
    IsMilnorProductAll (2+extra) ([[1,0]].map (padMany extra))
      ([[1,0]].map (padMany extra)) [] := by
  have hh : IsMilnorProductAll 2 [[1,0]] [[1,0]] [] := by
    milnor_cert_all using (⟨generate ⟨2,2⟩,1,1⟩ : AllCertificate)
  apply stable_product 2 extra 1 1 [[1,0]] [[1,0]] [] hh
  · intro m hm
    simp only [List.mem_singleton] at hm
    subst m
    rfl
  · intro m hm
    simp only [List.mem_singleton] at hm
    subst m
    rfl
  · simp
  · decide

#print axioms stable_product
#print axioms sqOne_square_all_higher_ranks


end MilnorCertificates
