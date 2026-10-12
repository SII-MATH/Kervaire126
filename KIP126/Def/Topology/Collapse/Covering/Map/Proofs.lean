module

public import KIP126.Def.Topology.Collapse.Covering.Proofs
public import KIP126.Def.Topology.Collapse.Map

@[expose] public section

namespace KIP126.Topology

open Set
open scoped OnePoint
set_option backward.isDefEq.respectTransparency false

/-- The finite-sheet wedge decomposition carries the map induced by the
original covering to the actual fold map. Thus every local sheet retains
its original target coordinate, not just its homeomorphism type. -/
theorem exists_covering_collapse_wedge_map
    {E Y I : Type*} [TopologicalSpace E] [CompactSpace E] [T2Space E]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    [TopologicalSpace I] [Finite I]
    (f : C(E, Y)) (y : Y) (x₀ : E) (hxy : f x₀ ≠ y)
    (h : IsEvenlyCovered f y I) :
    ∃ V : Set Y, y ∈ V ∧ IsOpen V ∧ f x₀ ∉ V ∧
      ∃ H : (f ⁻¹' V) ≃ₜ V × I,
        (∀ x, (H x).1.val = f x) ∧
        ∃ e : Quot (fun a b : E => f a ∉ V ∧ f b ∉ V) ≃ₜ
            Wedge (fun _ : I => OnePoint V) (fun _ => ∞),
        ∃ c : Quot (fun a b : Y => a ∉ V ∧ b ∉ V) ≃ₜ OnePoint V,
          e (Quot.mk _ x₀) = wedgePoint _ _ ∧
          c (Quot.mk _ (f x₀)) = ∞ ∧
          (∀ x : f ⁻¹' V, e (Quot.mk _ x.val) =
            wedgeInclusion _ _ (H x).2 ((H x).1 : OnePoint V)) ∧
          (∀ z : V, c (Quot.mk _ z.val) = (z : OnePoint V)) ∧
          ∀ q, c (collapsePreimageMap f Vᶜ q) =
            wedgeDesc (fun _ : I => OnePoint V) (fun _ => ∞) ∞
              (fun _ => ContinuousMap.id _) (fun _ => rfl) (e q) := by
  obtain ⟨V, hyV, hV, hxV, H, hH, e, he₀, he⟩ :=
    exists_covering_collapse_wedge f y x₀ hxy h
  obtain ⟨c₀, hc₀, hc⟩ :=
    exists_collapse_homeomorph_onePoint Vᶜ hV.isClosed_compl ⟨f x₀, hxV⟩
  let c := c₀.trans (Homeomorph.setCongr (compl_compl V)).onePointCongr
  have hcp : c (Quot.mk _ (f x₀)) = ∞ := by
    change (Homeomorph.setCongr (compl_compl V)).onePointCongr (c₀ _) = ∞
    rw [hc₀]
    rfl
  have hcv (z : V) : c (Quot.mk _ z.val) = (z : OnePoint V) := by
    change (Homeomorph.setCongr (compl_compl V)).onePointCongr (c₀ _) = _
    rw [hc ⟨z.val, by simpa using z.property⟩]
    rfl
  refine ⟨V, hyV, hV, hxV, H, hH, e, c, he₀, hcp, he, hcv, ?_⟩
  intro q
  induction q using Quot.inductionOn with
  | h x =>
    rw [collapsePreimageMap_mk]
    let fold := wedgeDesc (fun _ : I => OnePoint V) (fun _ => ∞) ∞
      (fun _ => ContinuousMap.id _) (fun _ => rfl)
    by_cases hx : f x ∈ V
    · calc
        c (Quot.mk _ (f x)) = ((⟨f x, hx⟩ : V) : OnePoint V) := hcv ⟨f x, hx⟩
        _ = ((H ⟨x, hx⟩).1 : OnePoint V) :=
          congrArg (fun z : V => (z : OnePoint V)) (Subtype.ext (hH ⟨x, hx⟩).symm)
        _ = fold (wedgeInclusion _ _ (H ⟨x, hx⟩).2 ((H ⟨x, hx⟩).1 : OnePoint V)) := rfl
        _ = fold (e (Quot.mk _ x)) := congrArg fold (he ⟨x, hx⟩).symm
    · have hEx : (Quot.mk (fun a b : E => f a ∉ V ∧ f b ∉ V) x) =
          Quot.mk _ x₀ := Quot.sound ⟨hx, hxV⟩
      have hYx : (Quot.mk (fun a b : Y => a ∉ V ∧ b ∉ V) (f x)) =
          Quot.mk _ (f x₀) := Quot.sound ⟨hx, hxV⟩
      calc
        c (Quot.mk _ (f x)) = c (Quot.mk _ (f x₀)) := congrArg c hYx
        _ = ∞ := hcp
        _ = fold (wedgePoint _ _) := rfl
        _ = fold (e (Quot.mk _ x₀)) := congrArg fold he₀.symm
        _ = fold (e (Quot.mk _ x)) := congrArg (fun q => fold (e q)) hEx.symm

end KIP126.Topology
