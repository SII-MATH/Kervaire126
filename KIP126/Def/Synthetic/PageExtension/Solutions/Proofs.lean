import KIP126.Def.Synthetic.PageExtension.Solutions.Data
import Mathlib.Algebra.Category.ModuleCat.Projective
import KIP126.Def.Synthetic.PageExtension.Predicates
import KIP126.Def.Synthetic.ExtensionSS.Solutions.Proofs

namespace KIP126.Synthetic.PageExtension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.Core.SpectralSequence
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

set_option backward.isDefEq.respectTransparency false

theorem finiteRelation_iff_solutions (P : NormalizedPageFamily H N F f)
    (q : ℕ) (hq : 0 < q) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n) (hkq : P.lambdaExponent n < q)
    (x : PageRepresentatives.cycles H X q (s, t))
    (y : PageRepresentatives.cycles H Y (q - P.lambdaExponent n : ℕ) (s + n, t + n)) :
    DifferentialRelation ((P.finite q hq).ess (P.degree s t)) n (s, 1)
      (elementMap (P.finiteSourceMap q hq s t x))
      (elementMap (P.finiteTargetMap q hq n s t hn hkq y)) ↔
        Nonempty (P.FiniteSolutions q hq n s t hn hkq x y) := by
  have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg _) hn
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
  simpa only [NormalizedPageFamily.FiniteSolutions, NormalizedPageFamily.finiteTargetClass,
    SyntheticExtensionData.targetClass, eqToHom_refl, Category.comp_id, id_eq] using
    (P.finite q hq).differentialRelation_iff_solutions (P.degree s t) n s
      (elementMap (P.finiteSourceMap q hq s t x))
      (P.finiteTargetClass q hq n s t hn hkq y)

theorem infiniteRelation_iff_solutions (P : NormalizedPageFamily H N F f)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : PageRepresentatives.permanentCycles H X (s, t))
    (y : PageRepresentatives.permanentCycles H Y (s + n, t + n)) :
    DifferentialRelation (P.infinite.ess (P.degree s t)) n (s, 1)
      (elementMap (P.infiniteSourceMap s t x)) (elementMap (P.infiniteTargetMap n s t hn y)) ↔
        Nonempty (P.InfiniteSolutions n s t hn x y) := by
  have hn0 : 0 ≤ n := le_trans (Int.natCast_nonneg _) hn
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
  simpa only [NormalizedPageFamily.InfiniteSolutions, NormalizedPageFamily.infiniteTargetClass,
    SyntheticExtensionData.targetClass, eqToHom_refl, Category.comp_id, id_eq] using
    P.infinite.differentialRelation_iff_solutions (P.degree s t) n s
      (elementMap (P.infiniteSourceMap s t x)) (P.infiniteTargetClass n s t hn y)

/-- Concrete finite representative fibers exactly express the existing
page-extension relation, including its higher-filtration indeterminacy. -/
theorem finitePageExtension_iff_solutions (P : NormalizedPageFamily H N F f)
    (r : ℕ) (hr : 2 ≤ r) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n) (hk : P.lambdaExponent n < r - 1)
    (x : PageRepresentatives.cycles H X (r - 1 : ℕ) (s, t))
    (y : PageRepresentatives.cycles H Y (r - 1 - P.lambdaExponent n : ℕ) (s + n, t + n)) :
    FinitePageExtension P r n s t x.val y.val ↔
      Nonempty (P.FiniteSolutions (r - 1) (by omega) n s t hn hk x y) := by
  rw [← finiteRelation_iff_solutions]
  constructor
  · rintro ⟨W⟩
    have hx : W.sourceCycle = x := Subtype.ext W.source_eq
    have hy : W.targetCycle = y := Subtype.ext W.target_eq
    simpa only [hx, hy] using W.relation
  · intro h
    exact ⟨{
      page_ge_two := hr
      exponent_le_length := hn
      exponent_lt_quotient := hk
      sourceCycle := x
      targetCycle := y
      source_eq := rfl
      target_eq := rfl
      relation := h }⟩

theorem infinitePageExtension_iff_solutions (P : NormalizedPageFamily H N F f)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : PageRepresentatives.permanentCycles H X (s, t))
    (y : PageRepresentatives.permanentCycles H Y (s + n, t + n)) :
    InfinitePageExtension P n s t x.val y.val ↔
      Nonempty (P.InfiniteSolutions n s t hn x y) := by
  rw [← infiniteRelation_iff_solutions]
  constructor
  · rintro ⟨W⟩
    have hx : W.sourceCycle = x := Subtype.ext W.source_eq
    have hy : W.targetCycle = y := Subtype.ext W.target_eq
    simpa only [hx, hy] using W.relation
  · intro h
    exact ⟨{
      exponent_le_length := hn
      sourceCycle := x
      targetCycle := y
      source_eq := rfl
      target_eq := rfl
      relation := h }⟩

end KIP126.Synthetic.PageExtension
