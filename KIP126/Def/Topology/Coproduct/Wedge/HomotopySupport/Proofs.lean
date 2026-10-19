module

public import KIP126.Def.Topology.Coproduct.Wedge.HomotopySupport.Predicates
public import KIP126.Def.Topology.Coproduct.Wedge.Subfamily.Proofs

@[expose] public section

namespace KIP126.Topology

open Set
universe u v
variable {J : Type u} {X : J → Type v} [∀ j, TopologicalSpace (X j)] {x₀ : ∀ j, X j}

private theorem exists_wedge_open (U : ∀ j, Set (X j))
    (hU : ∀ j, IsOpen (U j)) (hp : ∀ j, x₀ j ∈ U j) :
    ∃ O : Set (Wedge X x₀), IsOpen O ∧ wedgePoint X x₀ ∈ O ∧
      ∀ j x, wedgeInclusion X x₀ j x ∈ O ↔ x ∈ U j := by
  let P : WedgeCarrier X → Prop := Sum.elim (fun z => z.2 ∈ U z.1) (fun _ => True)
  have hP (a : WedgeCarrier X) (ha : WedgeCollapsed X x₀ a) : P a := by
    rcases a with ⟨j,x⟩ | ⟨⟩
    · change x = x₀ j at ha
      subst x
      exact hp j
    · trivial
  have hr : ∀ a b, (wedgeSetoid X x₀).r a b → P a = P b := by
    intro a b hab
    rcases hab with rfl | ⟨ha,hb⟩
    · rfl
    · exact propext ⟨fun _ => hP b hb,fun _ => hP a ha⟩
  let O : Set (Wedge X x₀) := {z | Quotient.lift P hr z}
  refine ⟨O,?_,True.intro,fun _ _ => Iff.rfl⟩
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  apply isOpen_sum_iff.mpr
  constructor
  · exact isOpen_sigma_iff.mpr hU
  · exact isOpen_univ

/-- A compact subset of the genuine quotient wedge meets only finitely
many summands outside the intersection of the basepoint neighborhoods.
Unlike literal finite support, this needs no separation hypothesis. -/
theorem isCompact_wedge_finite_distinguishable_support
    {K : Set (Wedge X x₀)} (hK : IsCompact K) :
    {j | ∃ x : X j, x ∉ basepointNeighborhoodKernel (x₀ j) ∧
      wedgeInclusion X x₀ j x ∈ K}.Finite := by
  classical
  let s : Set J := {j | ∃ x : X j, x ∉ basepointNeighborhoodKernel (x₀ j) ∧
    wedgeInclusion X x₀ j x ∈ K}
  let x (j : J) : X j := if h : j ∈ s then h.choose else x₀ j
  have hx (j : J) (hj : j ∈ s) : x j ∉ basepointNeighborhoodKernel (x₀ j) ∧
      wedgeInclusion X x₀ j (x j) ∈ K := by
    dsimp only [x]
    rw [dif_pos hj]
    exact hj.choose_spec
  have hU (j : J) : ∃ U : Set (X j), IsOpen U ∧ x₀ j ∈ U ∧
      (j ∈ s → x j ∉ U) := by
    by_cases hj : j ∈ s
    · have h := (hx j hj).1
      simp only [basepointNeighborhoodKernel,mem_setOf_eq,not_forall] at h
      obtain ⟨U,h⟩ := h
      have hh : IsOpen U ∧ x₀ j ∈ U ∧ x j ∉ U := by tauto
      exact ⟨U,hh.1,hh.2.1,fun _ => hh.2.2⟩
    · exact ⟨univ,isOpen_univ,mem_univ _,fun h => (hj h).elim⟩
  choose U hU hp hxU using hU
  let V (a : Option J) (j : J) : Set (X j) := if a = some j then univ else U j
  have hV (a : Option J) : ∃ O : Set (Wedge X x₀), IsOpen O ∧
      wedgePoint X x₀ ∈ O ∧ ∀ j y, wedgeInclusion X x₀ j y ∈ O ↔ y ∈ V a j := by
    apply exists_wedge_open
    · intro j
      dsimp only [V]
      split_ifs <;> first | exact isOpen_univ | exact hU j
    · intro j
      dsimp only [V]
      split_ifs <;> first | exact mem_univ _ | exact hp j
  choose O hO hOp hOV using hV
  have hcover : K ⊆ ⋃ a, O a := by
    intro z _
    induction z using Quotient.inductionOn with
    | h z =>
      rcases z with ⟨j,y⟩ | ⟨⟩
      · apply mem_iUnion.mpr
        refine ⟨some j,(hOV (some j) j y).mpr ?_⟩
        simp [V]
      · exact mem_iUnion.mpr ⟨none,hOp none⟩
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover O hO hcover
  have hs : s ⊆ Option.some ⁻¹' (t : Set (Option J)) := by
    intro j hj
    obtain ⟨a,ha,hax⟩ := mem_iUnion₂.mp (ht (hx j hj).2)
    have hy := (hOV a j (x j)).mp hax
    by_cases haj : a = some j
    · simpa [haj] using ha
    · have hy' : x j ∈ U j := by simpa [V,haj] using hy
      exact (hxU j hj hy').elim
  exact (t.finite_toSet.preimage (fun _ _ _ _ h => Option.some.inj h)).subset hs

/-- Every compact-domain map has finite support after disregarding
points indistinguishable from the basepoint by its open neighborhoods. -/
theorem continuousMap_wedge_finite_distinguishable_support
    {A : Type*} [TopologicalSpace A] [CompactSpace A] (f : C(A,Wedge X x₀)) :
    {j | ∃ x : X j, x ∉ basepointNeighborhoodKernel (x₀ j) ∧
      wedgeInclusion X x₀ j x ∈ Set.range f}.Finite :=
  isCompact_wedge_finite_distinguishable_support (isCompact_range f.continuous)

/-- Collapsing only summands lying in their basepoint-neighborhood
kernels sends a point to a specialization of that same point. -/
theorem wedgeSubfamilyInclusion_retraction_mem_open (s : Set J) (z : Wedge X x₀)
    (hz : ∀ j (x : X j), wedgeInclusion X x₀ j x = z → j ∉ s →
      x ∈ basepointNeighborhoodKernel (x₀ j))
    {O : Set (Wedge X x₀)} (hO : IsOpen O)
    (h : wedgeSubfamilyInclusion X x₀ s (wedgeSubfamilyRetraction X x₀ s z) ∈ O) :
    z ∈ O := by
  classical
  induction z using Quotient.inductionOn with
  | h z =>
    rcases z with ⟨j,x⟩ | ⟨⟩
    · change wedgeInclusion X x₀ j x ∈ O
      change wedgeSubfamilyInclusion X x₀ s
        (wedgeSubfamilyRetraction X x₀ s (wedgeInclusion X x₀ j x)) ∈ O at h
      by_cases hj : j ∈ s
      · simpa only [wedgeSubfamilyRetraction_inclusion s j hj,
          wedgeSubfamilyInclusion_inclusion] using h
      · have hp : wedgePoint X x₀ ∈ O := by
          simpa [wedgeSubfamilyRetraction,wedgeDesc_inclusion,hj] using h
        exact hz j x rfl hj ((wedgeInclusion X x₀ j) ⁻¹' O)
          (hO.preimage (wedgeInclusion X x₀ j).continuous)
          (by simpa only [mem_preimage,wedgeInclusion_point] using hp)
    · exact h

/-- The actual finite-subfamily retraction has the open-preimage
inclusion needed for a homotopy, even when literal finite support fails. -/
theorem wedgeSubfamilyRetraction_comp_preimage_subset
    {A : Type*} [TopologicalSpace A] (s : Set J) (f : C(A,Wedge X x₀))
    (hs : ∀ j (x : X j), x ∉ basepointNeighborhoodKernel (x₀ j) →
      wedgeInclusion X x₀ j x ∈ Set.range f → j ∈ s)
    (O : Set (Wedge X x₀)) (hO : IsOpen O) :
    (((wedgeSubfamilyInclusion X x₀ s).comp
      (wedgeSubfamilyRetraction X x₀ s)).comp f) ⁻¹' O ⊆ f ⁻¹' O := by
  intro a ha
  apply wedgeSubfamilyInclusion_retraction_mem_open s (f a) ?_ hO ha
  intro j x he hj
  by_contra hx
  exact hj (hs j x hx ⟨a,he.symm⟩)

end KIP126.Topology
