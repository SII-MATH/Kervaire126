module

public import KIP126.Def.Topology.Cube.Compression.Window.Data
public import KIP126.Def.Topology.Cube.Compression.Proofs

@[expose] public section

namespace KIP126.Topology.Cube

open Set
open scoped unitInterval

variable {N : Type*} (a b : N → I) (hab : ∀ i, a i < b i)
include hab

/-- Expanding into the window and then applying the original compression
recovers every point of the unit cube. -/
theorem windowCompression_expansion (u : N → I) :
    windowCompression a b (windowExpansion a b u) = u := by
  funext i
  change Set.projIcc 0 1 zero_le_one
    (((1 - (u i : ℝ)) * a i + (u i : ℝ) * b i - a i) /
      ((b i : ℝ) - a i)) = u i
  have hd : (b i : ℝ) - a i ≠ 0 := ne_of_gt (sub_pos.mpr (hab i))
  have he : ((1 - (u i : ℝ)) * a i + (u i : ℝ) * b i - a i) /
      ((b i : ℝ) - a i) = u i := by
    apply (div_eq_iff hd).mpr
    ring
  rw [he]
  exact Set.projIcc_val _ _

/-- Compression followed by affine expansion recovers every point of
the chosen closed window. -/
theorem windowExpansion_compression (x : N → I)
    (hx : ∀ i, a i ≤ x i ∧ x i ≤ b i) :
    windowExpansion a b (windowCompression a b x) = x := by
  funext i
  apply Subtype.ext
  have hd : 0 < (b i : ℝ) - a i := sub_pos.mpr (hab i)
  have hr : ((x i : ℝ) - a i) / ((b i : ℝ) - a i) ∈ Icc (0 : ℝ) 1 := by
    exact ⟨div_nonneg (sub_nonneg.mpr (hx i).1) hd.le,
      (div_le_one hd).mpr (sub_le_sub_right
        (show (x i : ℝ) ≤ b i from (hx i).2) _)⟩
  change (1 - (Set.projIcc (0 : ℝ) 1 zero_le_one
    (((x i : ℝ) - a i) / ((b i : ℝ) - a i)) : ℝ)) * a i +
    (Set.projIcc (0 : ℝ) 1 zero_le_one
      (((x i : ℝ) - a i) / ((b i : ℝ) - a i)) : ℝ) * b i = x i
  rw [Set.projIcc_of_mem zero_le_one hr]
  dsimp
  field_simp [ne_of_gt hd]
  ring

/-- The affine inclusion takes precisely interior cube coordinates to
strictly interior window coordinates. -/
theorem windowExpansion_mem_open_iff (u : N → I) :
    (∀ i, a i < windowExpansion a b u i ∧ windowExpansion a b u i < b i) ↔
      u ∉ _root_.Cube.boundary N := by
  have hi (i : N) :
      (a i < windowExpansion a b u i ∧ windowExpansion a b u i < b i) ↔
        (0 : ℝ) < u i ∧ (u i : ℝ) < 1 := by
    change ((a i : ℝ) < (1 - (u i : ℝ)) * a i + (u i : ℝ) * b i ∧
      (1 - (u i : ℝ)) * a i + (u i : ℝ) * b i < b i) ↔ _
    have hd : (a i : ℝ) < b i := hab i
    constructor
    · rintro ⟨h₁, h₂⟩
      constructor <;> nlinarith [(u i).property.1, (u i).property.2]
    · rintro ⟨h₁, h₂⟩
      constructor
      · nlinarith [mul_pos h₁ (sub_pos.mpr hd)]
      · nlinarith [mul_pos (sub_pos.mpr h₂) (sub_pos.mpr hd)]
  simp_rw [hi]
  constructor
  · rintro hu ⟨i, hi | hi⟩
    · exact (ne_of_gt (hu i).1) (congrArg Subtype.val hi)
    · exact (ne_of_lt (hu i).2) (congrArg Subtype.val hi)
  · intro hu i
    constructor
    · exact lt_of_le_of_ne (u i).property.1
        (fun he => hu ⟨i, Or.inl (Subtype.ext he.symm)⟩)
    · exact lt_of_le_of_ne (u i).property.2
        (fun he => hu ⟨i, Or.inr (Subtype.ext he)⟩)

/-- The inverse image of the original cube interior is exactly the
chosen open window. -/
theorem windowCompression_mem_interior_iff (x : N → I) :
    windowCompression a b x ∉ _root_.Cube.boundary N ↔
      ∀ i, a i < x i ∧ x i < b i := by
  constructor
  · intro hx i
    constructor
    · by_contra h
      exact hx ⟨i, Or.inl (windowCompression_apply_of_le a b hab x i (le_of_not_gt h))⟩
    · by_contra h
      exact hx ⟨i, Or.inr (windowCompression_apply_of_ge a b hab x i (le_of_not_gt h))⟩
  · intro hx
    apply (windowExpansion_mem_open_iff a b hab _).mp
    rw [windowExpansion_compression a b hab x (fun i => ⟨(hx i).1.le, (hx i).2.le⟩)]
    exact hx

/-- The original compression is an actual homeomorphism from the open
window onto the interior of the original cube. Its inverse is the
specified affine inclusion. -/
theorem exists_windowCompression_interior_homeomorph :
    ∃ e : {x : N → I | ∀ i, a i < x i ∧ x i < b i} ≃ₜ
        ((_root_.Cube.boundary N)ᶜ : Set (N → I)),
      (∀ x, (e x).val = windowCompression a b x.val) ∧
      (∀ u, (e.symm u).val = windowExpansion a b u.val) := by
  refine ⟨{
    toFun := fun x => ⟨windowCompression a b x.val,
      (windowCompression_mem_interior_iff a b hab x.val).mpr x.property⟩
    invFun := fun u => ⟨windowExpansion a b u.val,
      (windowExpansion_mem_open_iff a b hab u.val).mpr u.property⟩
    left_inv := fun x => Subtype.ext (windowExpansion_compression a b hab x.val
      (fun i => ⟨(x.property i).1.le, (x.property i).2.le⟩))
    right_inv := fun u => Subtype.ext (windowCompression_expansion a b hab u.val)
    continuous_toFun := ((windowCompression a b).continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := ((windowExpansion a b).continuous.comp continuous_subtype_val).subtype_mk _ },
    fun _ => rfl, fun _ => rfl⟩

end KIP126.Topology.Cube
