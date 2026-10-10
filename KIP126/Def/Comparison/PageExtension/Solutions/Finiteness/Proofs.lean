import KIP126.Def.Comparison.PageExtension.Solutions.Data
import KIP126.Def.Comparison.ClassicalSynthetic.FiniteBockstein.Data
import KIP126.Def.Algebra.InverseSequence.Finite.Proofs
import KIP126.Def.Synthetic.PageExtension.Solutions.Finiteness.Proofs
import KIP126.Def.Synthetic.QuotientTower.Finiteness.Proofs

/-! A compatible tower from finite nonempty actual solution fibers.
Finiteness is required for the strict representative fibers themselves.
No initial solution is prescribed, and no untruncated recovery is asserted. -/

namespace KIP126.Def.Comparison.StageInterfaces

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

/-- Finite nonempty permanent-label solution fibers admit some coherent
choice under the actual adjacent restrictions. -/
theorem nonempty_coherentPageExtensionSolutions_of_finite
    (P : NormalizedPageFamily H N F f)
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : permanentCycles H X (s, t)) (y : permanentCycles H Y (s + n, t + n))
    (hfinite : ∀ (q : ℕ) (hkq : P.lambdaExponent n < q),
      Finite (P.PermanentFiniteSolutions q n s t hn hkq x y))
    (hne : ∀ (q : ℕ) (hkq : P.lambdaExponent n < q),
      Nonempty (P.PermanentFiniteSolutions q n s t hn hkq x y)) :
    Nonempty (CoherentPageExtensionSolutions P I J n s t hn x y) := by
  obtain ⟨a, ha⟩ := KIP126.Core.InverseSequence.exists_compatible_of_finite
    (P.lambdaExponent n + 1)
    (fun q hq => P.PermanentFiniteSolutions q n s t hn (Nat.lt_of_succ_le hq) x y)
    (fun q hq => restrictPermanentFiniteSolution I J q (q + 1) (Nat.le_succ q)
      n s t hn (Nat.lt_of_succ_le hq)
      (lt_trans (Nat.lt_of_succ_le hq) (Nat.lt_succ_self q)) x y)
    (fun q hq => hfinite q (Nat.lt_of_succ_le hq))
    (fun q hq => hne q (Nat.lt_of_succ_le hq))
  refine ⟨{
    solution := fun q hkq => a q (Nat.succ_le_of_lt hkq)
    compatible := ?_ }⟩
  intro q hkq
  exact ha q (Nat.succ_le_of_lt hkq)

/-- Finiteness of the actual source homotopy groups suffices for finiteness
of strict solution fibers; the target groups need not be finite. -/
theorem nonempty_coherentPageExtensionSolutions_of_finite_source
    (P : NormalizedPageFamily H N F f)
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : permanentCycles H X (s, t)) (y : permanentCycles H Y (s + n, t + n))
    (hfinite : ∀ (q : ℕ), P.lambdaExponent n < q →
      Finite (syntheticHomotopy (XModLambdaN (normalizedSource H N f) q) (P.degree s t)))
    (hne : ∀ (q : ℕ) (hkq : P.lambdaExponent n < q),
      Nonempty (P.PermanentFiniteSolutions q n s t hn hkq x y)) :
    Nonempty (CoherentPageExtensionSolutions P I J n s t hn x y) := by
  apply nonempty_coherentPageExtensionSolutions_of_finite P I J n s t hn x y ?_ hne
  intro q hkq
  haveI := hfinite q hkq
  exact P.finite_permanentFiniteSolutions_of_finite_source q n s t hn hkq x y

/-- The actual λ quotient has finite homotopy when the relevant finite
segment of the classical E₂ diagonal is finite and the specified first-quotient
comparison is supplied. This does not prove that comparison or finite type. -/
theorem finite_normalizedSourceHomotopy_of_firstQuotientComparison
    (P : NormalizedPageFamily H N F f) (Q : FirstQuotientHomotopyComparison H N X)
    (q : ℕ) (hq : 0 < q) (s t : ℤ)
    (hfinite : ∀ j : ℕ, j < q → Finite (Ambient H X (s + j, t + j))) :
    Finite (syntheticHomotopy (XModLambdaN (normalizedSource H N f) q) (P.degree s t)) := by
  apply P.sourceTower.finite_biHom q hq (t - s) (t + normalizedExponent H f)
  intro j hj
  haveI := hfinite j hj
  have hm : t + (j : ℤ) - (s + j) = t - s := by omega
  have hw : t + (j : ℤ) + normalizedExponent H f =
      t + normalizedExponent H f + j := by omega
  simpa only [hm, hw, normalizedSource] using
    (Finite.of_equiv (Ambient H X (s + j, t + j))
      (Q (normalizedExponent H f) (s + j) (t + j)).toEquiv.symm)

/-- A first-quotient comparison, finite classical E₂ diagonal, and nonempty
actual solution fibers suffice for some coherent tower. No recovery of an
untruncated solution is asserted. -/
theorem nonempty_coherentPageExtensionSolutions_of_finite_e2
    (P : NormalizedPageFamily H N F f)
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (Q : FirstQuotientHomotopyComparison H N X)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : permanentCycles H X (s, t)) (y : permanentCycles H Y (s + n, t + n))
    (hfinite : ∀ j : ℕ, Finite (Ambient H X (s + j, t + j)))
    (hne : ∀ (q : ℕ) (hkq : P.lambdaExponent n < q),
      Nonempty (P.PermanentFiniteSolutions q n s t hn hkq x y)) :
    Nonempty (CoherentPageExtensionSolutions P I J n s t hn x y) := by
  apply nonempty_coherentPageExtensionSolutions_of_finite_source P I J n s t hn x y ?_ hne
  intro q hkq
  exact finite_normalizedSourceHomotopy_of_firstQuotientComparison P Q q (by omega)
    s t (fun j _ => hfinite j)

end KIP126.Def.Comparison.StageInterfaces
