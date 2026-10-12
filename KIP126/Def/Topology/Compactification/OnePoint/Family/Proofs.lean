module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Homotopy.Basic

@[expose] public section

namespace KIP126.Topology

open Set Filter _root_.Topology
open scoped OnePoint Topology

/-- A continuous compactly parametrized family with continuous left
inverses extends continuously across infinity. Compactness of the
parameter gives the uniform properness required at infinity. -/
theorem continuous_onePoint_map_family_of_inverse
    {T X Y : Type*} [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
    (f : T × X → Y) (g : T × Y → X)
    (hf : Continuous f) (hg : Continuous g)
    (hgf : ∀ t x, g (t, f (t, x)) = x) :
    Continuous (fun z : T × OnePoint X => OnePoint.map (fun x => f (z.1, x)) z.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨t, x⟩
  induction x using OnePoint.rec with
  | infty =>
    change Tendsto _ (𝓝 (t, ∞)) (𝓝 (∞ : OnePoint Y))
    apply OnePoint.hasBasis_nhds_infty.tendsto_right_iff.mpr
    rintro K ⟨hKc, hK⟩
    let L : Set X := g '' (Set.univ ×ˢ K)
    have hL : IsCompact L := (isCompact_univ.prod hK).image hg
    have hU : IsOpen (((↑) : X → OnePoint X) '' L)ᶜ :=
      OnePoint.isOpen_compl_image_coe.mpr ⟨hL.isClosed, hL⟩
    have hmem : (((↑) : X → OnePoint X) '' L)ᶜ ∈ 𝓝 (∞ : OnePoint X) :=
      hU.mem_nhds OnePoint.infty_notMem_image_coe
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hmem] with z hz
    rcases z with ⟨s, z⟩
    induction z using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z =>
      refine Or.inl ⟨f (s, z), ?_, rfl⟩
      intro hzK
      apply hz
      refine ⟨z, ?_, rfl⟩
      exact ⟨(s, f (s, z)), ⟨Set.mem_univ _, hzK⟩, hgf s z⟩
  | coe x =>
    have he := (IsOpenEmbedding.id (X := T)).prodMap (OnePoint.isOpenEmbedding_coe (X := X))
    apply (he.continuousAt_iff (g := fun z : T × OnePoint X =>
      OnePoint.map (fun x => f (z.1, x)) z.2) (x := (t, x))).mp
    exact (OnePoint.continuous_coe.comp hf).continuousAt

end KIP126.Topology
