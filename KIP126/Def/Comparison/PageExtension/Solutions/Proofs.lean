import KIP126.Def.Comparison.PageExtension.Solutions.Data
import KIP126.Def.Synthetic.PageExtension.Solutions.Proofs

/-! am6/am7：从实际代表元方程推出 page extension 的解语义与有限商限制。
使用同一经典标签和实际 ρ 方块；不假设限制的满射性。 -/

namespace KIP126.Def.Comparison.StageInterfaces

set_option backward.isDefEq.respectTransparency false

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Synthetic.PageExtension KIP126.Classical.Adams.PageRepresentatives KIP126.Challenge2

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

theorem finitePageExtension_iff_solutions (P : NormalizedPageFamily H N F f)
    (r : ℕ) (hr : 2 ≤ r) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n) (hk : P.lambdaExponent n < r - 1)
    (x : cycles H X (r - 1 : ℕ) (s, t))
    (y : cycles H Y (r - 1 - P.lambdaExponent n : ℕ) (s + n, t + n)) :
    FinitePageExtension P r n s t x.val y.val ↔
      Nonempty (P.FiniteSolutions (r - 1) (by omega) n s t hn hk x y) := by
  exact KIP126.Synthetic.PageExtension.finitePageExtension_iff_solutions P r hr n s t hn hk x y

theorem infinitePageExtension_iff_solutions (P : NormalizedPageFamily H N F f)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : permanentCycles H X (s, t))
    (y : permanentCycles H Y (s + n, t + n)) :
    InfinitePageExtension P n s t x.val y.val ↔
      Nonempty (P.InfiniteSolutions n s t hn x y) := by
  exact KIP126.Synthetic.PageExtension.infinitePageExtension_iff_solutions P n s t hn x y

theorem finitePageExtension_restrict (P : NormalizedPageFamily H N F f)
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (i j : ℕ) (hi : 0 < i) (hj : 0 < j) (hij : i ≤ j) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n)
    (hki : P.lambdaExponent n < i) (hkj : P.lambdaExponent n < j)
    (xi : cycles H X i (s, t)) (xj : cycles H X j (s, t)) (hx : xi.val = xj.val)
    (yi : cycles H Y (i - P.lambdaExponent n : ℕ) (s + n, t + n))
    (yj : cycles H Y (j - P.lambdaExponent n : ℕ) (s + n, t + n)) (hy : yi.val = yj.val)
    (h : FinitePageExtension P (j + 1) n s t xj.val yj.val) :
    FinitePageExtension P (i + 1) n s t xi.val yi.val := by
  obtain ⟨a⟩ := (finitePageExtension_iff_solutions P (j + 1) (by omega)
    n s t hn hkj xj yj).mp h
  apply (finitePageExtension_iff_solutions P (i + 1) (by omega)
    n s t hn hki xi yi).mpr
  exact ⟨restrictFiniteSolution I J i j hi hj hij n s t hn hki hkj xi xj hx yi yj hy a⟩

end KIP126.Def.Comparison.StageInterfaces
