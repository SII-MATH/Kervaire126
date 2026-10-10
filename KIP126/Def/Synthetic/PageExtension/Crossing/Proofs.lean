import KIP126.Def.Synthetic.PageExtension.Crossing.Predicates

/-! Degree and length consequences of the actual crossing predicates. -/

namespace KIP126.Synthetic.PageExtension

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams

universe u v u' v'
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}
  (P : NormalizedPageFamily H N F f)

/-- The shorter witness lands at the paper's stated target bidegree. -/
theorem crossing_target_degree (n s t : ℤ) (a b : ℕ) :
    (s + a + (n - a - b), t + a + (n - a - b)) =
      (s + n - b, t + n - b) := by
  ext <;> omega

/-- Positive filtration displacement leaves strictly less extension length. -/
theorem crossing_length_lt (n : ℤ) (a b : ℕ) (ha : 0 < a) :
    n - a - b < n := by omega

/-- The boundary exclusion always lies in the valid paper range; it never
uses the truncated extension of `boundaries` to levels below one. -/
theorem crossing_boundaryLevel_ge_two (n : ℤ) (a b : ℕ) (ha : 0 < a)
    (hb : (b : ℤ) ≤ n - a - normalizedExponent H f) :
    2 ≤ 1 + n - b - normalizedExponent H f := by omega

theorem FinitePageExtension.length_ge_of_hasCrossing {r : ℕ} {n s t : ℤ}
    (h : FinitePageExtension.HasCrossing P r n s t) :
    (normalizedExponent H f : ℤ) + 1 ≤ n := by
  rcases h with ⟨a, b, ha, _, hb, _⟩
  omega

/-- E₂ has no room for the required positive page displacement. -/
theorem FinitePageExtension.noCrossing_page_two (n s t : ℤ) :
    FinitePageExtension.NoCrossing P 2 n s t := by
  rintro ⟨a, b, ha, har, _⟩
  omega

theorem FinitePageExtension.noCrossing_of_length_le_exponent (r : ℕ) (n s t : ℤ)
    (hn : n ≤ normalizedExponent H f) :
    FinitePageExtension.NoCrossing P r n s t := by
  intro h
  have := FinitePageExtension.length_ge_of_hasCrossing P h
  omega

theorem InfinitePageExtension.length_ge_of_hasCrossing {n s t : ℤ}
    (h : InfinitePageExtension.HasCrossing P n s t) :
    (normalizedExponent H f : ℤ) + 1 ≤ n := by
  rcases h with ⟨a, b, ha, han, _⟩
  omega

theorem InfinitePageExtension.noCrossing_of_length_le_exponent (n s t : ℤ)
    (hn : n ≤ normalizedExponent H f) :
    InfinitePageExtension.NoCrossing P n s t := by
  intro h
  have := InfinitePageExtension.length_ge_of_hasCrossing P h
  omega

variable {P}

theorem FiniteExtensionWitness.noCrossing_page_two {n s t : ℤ}
    {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (W : FiniteExtensionWitness P 2 n s t x y) : W.NoCrossing :=
  FinitePageExtension.noCrossing_page_two P n s t

/-- The minimal allowed finite extension length is e(f). -/
theorem FiniteExtensionWitness.noCrossing_of_minimal_length {r : ℕ} {n s t : ℤ}
    {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (W : FiniteExtensionWitness P r n s t x y)
    (hn : n = normalizedExponent H f) : W.NoCrossing :=
  FinitePageExtension.noCrossing_of_length_le_exponent P r n s t hn.le

/-- The same minimal-length obstruction applies to an actual untruncated
extension, without reducing it to finite crossing candidates. -/
theorem InfiniteExtensionWitness.noCrossing_of_minimal_length {n s t : ℤ}
    {x : PageRepresentatives.Ambient H X (s, t)}
    {y : PageRepresentatives.Ambient H Y (s + n, t + n)}
    (W : InfiniteExtensionWitness P n s t x y)
    (hn : n = normalizedExponent H f) : W.NoCrossing :=
  InfinitePageExtension.noCrossing_of_length_le_exponent P n s t hn.le

end KIP126.Synthetic.PageExtension
