module

public import KIP126.Def.Topology.Cube.Rotation.Data
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace KIP126.Topology.Cube

open scoped unitInterval Topology

theorem quarterLinear_eq_zero_iff (s : ℝ) (v : ℝ × ℝ) :
    quarterLinear s v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change (1 - s) * v.1 + s * v.2 = 0 at h₁
    change (1 - s) * v.2 - s * v.1 = 0 at h₂
    have hd : (1 - s) ^ 2 + s ^ 2 ≠ 0 := by nlinarith [sq_nonneg (2*s-1)]
    have hx : ((1 - s) ^ 2 + s ^ 2) * v.1 = 0 := by
      linear_combination (1-s) * h₁ - s * h₂
    have hy : ((1 - s) ^ 2 + s ^ 2) * v.2 = 0 := by
      linear_combination s * h₁ + (1-s) * h₂
    exact Prod.ext ((mul_eq_zero.mp hx).resolve_left hd) ((mul_eq_zero.mp hy).resolve_left hd)
  · rintro rfl
    simp [quarterLinear]

@[simp] theorem norm_quarterRadial (s : ℝ) (v : ℝ × ℝ) :
    ‖quarterRadial s v‖ = ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv, quarterRadial, quarterLinear]
  · have hn : ‖quarterLinear s v‖ ≠ 0 := norm_ne_zero_iff.mpr
      (mt (quarterLinear_eq_zero_iff s v).mp hv)
    rw [quarterRadial, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)), div_mul_cancel₀ _ hn]

theorem continuous_quarterLinear : Continuous (fun z : ℝ × (ℝ × ℝ) => quarterLinear z.1 z.2) := by
  unfold quarterLinear
  fun_prop

theorem continuous_quarterRadial : Continuous (fun z : ℝ × (ℝ × ℝ) => quarterRadial z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hv : z.2 = 0
  · have hzero : quarterRadial z.1 z.2 = 0 := by simp [hv, quarterRadial, quarterLinear]
    rw [ContinuousAt, hzero, tendsto_zero_iff_norm_tendsto_zero]
    simpa only [norm_quarterRadial, hv, norm_zero] using
      (continuous_snd : Continuous (fun z : ℝ × (ℝ × ℝ) => z.2)).norm.continuousAt (x := z) |>.tendsto
  · exact ((continuous_snd.norm.continuousAt.div continuous_quarterLinear.norm.continuousAt
      (norm_ne_zero_iff.mpr (mt (quarterLinear_eq_zero_iff z.1 z.2).mp hv))).smul
        continuous_quarterLinear.continuousAt)

@[simp] theorem quarterRadial_zero (v : ℝ × ℝ) : quarterRadial 0 v = v := by
  have hl : quarterLinear 0 v = v := by ext <;> simp [quarterLinear]
  by_cases hv : v = 0
  · simp [hv, quarterRadial]
  · simp [quarterRadial, hl, norm_ne_zero_iff.mpr hv]

@[simp] theorem quarterRadial_one (v : ℝ × ℝ) : quarterRadial 1 v = (v.2, -v.1) := by
  have hl : quarterLinear 1 v = (v.2, -v.1) := by ext <;> simp [quarterLinear]
  have hn : ‖quarterLinear 1 v‖ = ‖v‖ := by
    rw [hl, Prod.norm_def, Prod.norm_def, norm_neg, max_comm]
  by_cases hv : v = 0
  · subst v
    ext <;> simp [quarterRadial, quarterLinear]
  · rw [quarterRadial, hn, div_self (norm_ne_zero_iff.mpr hv), one_smul, hl]

theorem continuous_squareCenter : Continuous squareCenter := by
  unfold squareCenter
  fun_prop

theorem continuous_squareRotation : Continuous (fun z : I × (I × I) => squareRotation z.1 z.2) := by
  have hc : Continuous (fun z : I × (I × I) => quarterRadial z.1 (squareCenter z.2)) :=
    continuous_quarterRadial.comp (continuous_fst.subtype_val.prodMk
      (continuous_squareCenter.comp continuous_snd))
  exact (continuous_projIcc.comp (hc.fst.div_const 2 |>.add continuous_const)).prodMk
    (continuous_projIcc.comp (hc.snd.div_const 2 |>.add continuous_const))

theorem norm_squareCenter_le (p : I × I) : ‖squareCenter p‖ ≤ 1 := by
  rw [Prod.norm_def]
  apply max_le
  · rw [Real.norm_eq_abs, abs_le]
    constructor <;> dsimp [squareCenter] <;> nlinarith [p.1.property.1, p.1.property.2]
  · rw [Real.norm_eq_abs, abs_le]
    constructor <;> dsimp [squareCenter] <;> nlinarith [p.2.property.1, p.2.property.2]

theorem squareCenter_rotation (s : I) (p : I × I) :
    squareCenter (squareRotation s p) = quarterRadial s (squareCenter p) := by
  have hn : ‖quarterRadial s (squareCenter p)‖ ≤ 1 := by
    rw [norm_quarterRadial]
    exact norm_squareCenter_le p
  have h₁ : |(quarterRadial s (squareCenter p)).1| ≤ 1 :=
    (le_max_left _ _).trans hn
  have h₂ : |(quarterRadial s (squareCenter p)).2| ≤ 1 :=
    (le_max_right _ _).trans hn
  obtain ⟨ha, hb⟩ := abs_le.mp h₁
  obtain ⟨hc, hd⟩ := abs_le.mp h₂
  have hp₁ : (quarterRadial s (squareCenter p)).1 / 2 + 1 / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  have hp₂ : (quarterRadial s (squareCenter p)).2 / 2 + 1 / 2 ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith
  change (2 * (Set.projIcc (0 : ℝ) 1 zero_le_one
      ((quarterRadial s (squareCenter p)).1 / 2 + 1 / 2) : ℝ) - 1,
    2 * (Set.projIcc (0 : ℝ) 1 zero_le_one
      ((quarterRadial s (squareCenter p)).2 / 2 + 1 / 2) : ℝ) - 1) = _
  rw [Set.projIcc_of_mem _ hp₁, Set.projIcc_of_mem _ hp₂]
  ext <;> dsimp only <;> ring

theorem squareCenter_injective : Function.Injective squareCenter := by
  intro p q h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  apply Prod.ext <;> apply Subtype.ext
  · dsimp [squareCenter] at h₁
    linarith
  · dsimp [squareCenter] at h₂
    linarith

@[simp] theorem squareRotation_zero (p : I × I) : squareRotation 0 p = p := by
  apply squareCenter_injective
  rw [squareCenter_rotation]
  exact quarterRadial_zero _

@[simp] theorem squareRotation_one (p : I × I) : squareRotation 1 p = (p.2, σ p.1) := by
  apply squareCenter_injective
  rw [squareCenter_rotation]
  change quarterRadial 1 (squareCenter p) = _
  rw [quarterRadial_one]
  ext <;> simp only [squareCenter, unitInterval.coe_symm_eq] <;> ring

theorem square_boundary_iff_norm (p : I × I) :
    (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) ↔ ‖squareCenter p‖ = 1 := by
  have hn := norm_squareCenter_le p
  constructor
  · intro h
    apply le_antisymm hn
    rcases h with h | h | h | h
    · have : ‖(squareCenter p).1‖ = 1 := by norm_num [squareCenter, h]
      rw [Prod.norm_def, this]
      exact le_max_left _ _
    · have : ‖(squareCenter p).1‖ = 1 := by norm_num [squareCenter, h]
      rw [Prod.norm_def, this]
      exact le_max_left _ _
    · have : ‖(squareCenter p).2‖ = 1 := by norm_num [squareCenter, h]
      rw [Prod.norm_def, this]
      exact le_max_right _ _
    · have : ‖(squareCenter p).2‖ = 1 := by norm_num [squareCenter, h]
      rw [Prod.norm_def, this]
      exact le_max_right _ _
  · intro h
    rw [Prod.norm_def] at h
    have hab := max_cases ‖(squareCenter p).1‖ ‖(squareCenter p).2‖
    rcases hab with ⟨heq, _⟩ | ⟨heq, _⟩
    · rw [heq, Real.norm_eq_abs, abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at h
      rcases h with h | h
      · exact Or.inr (Or.inl (Subtype.ext (by change (p.1 : ℝ) = 1; dsimp [squareCenter] at h; linarith)))
      · exact Or.inl (Subtype.ext (by change (p.1 : ℝ) = 0; dsimp [squareCenter] at h; linarith))
    · rw [heq, Real.norm_eq_abs, abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at h
      rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext (by change (p.2 : ℝ) = 1; dsimp [squareCenter] at h; linarith))))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext (by change (p.2 : ℝ) = 0; dsimp [squareCenter] at h; linarith))))

theorem squareRotation_preserves_boundary (s : I) (p : I × I)
    (hp : p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) :
    (squareRotation s p).1 = 0 ∨ (squareRotation s p).1 = 1 ∨
      (squareRotation s p).2 = 0 ∨ (squareRotation s p).2 = 1 := by
  apply (square_boundary_iff_norm _).mpr
  rw [squareCenter_rotation, norm_quarterRadial]
  exact (square_boundary_iff_norm p).mp hp

/-- A boundary-preserving homotopy from the identity of the square to
clockwise quarter rotation. Boundary points may move along the boundary. -/
theorem exists_square_quarter_rotation :
    ∃ R : C(I × (I × I), I × I),
      (∀ p, R (0, p) = p) ∧ (∀ p, R (1, p) = (p.2, σ p.1)) ∧
      (∀ s p, (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) →
        (R (s, p)).1 = 0 ∨ (R (s, p)).1 = 1 ∨ (R (s, p)).2 = 0 ∨ (R (s, p)).2 = 1) :=
  ⟨⟨fun z => squareRotation z.1 z.2, continuous_squareRotation⟩,
    squareRotation_zero, squareRotation_one, squareRotation_preserves_boundary⟩

end KIP126.Topology.Cube
