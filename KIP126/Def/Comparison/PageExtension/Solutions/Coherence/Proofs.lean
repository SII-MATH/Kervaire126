import KIP126.Def.Comparison.PageExtension.Solutions.Data
import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.AffineRestriction.Proofs
import KIP126.Def.Algebra.InverseSequence.Proofs

/-! Compatible finite solution towers from an initial solution and actual
surjective restrictions. This makes no untruncated ESS recovery claim. -/

namespace KIP126.Def.Comparison.StageInterfaces

open KIP126.Core.SpectralSequence
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

/-- For the actual permanent-label restriction, lifting every strict
solution is equivalent to lifting every homogeneous displacement, provided
one later solution is specified. The two label diagrams are retained. -/
theorem restrictPermanentFiniteSolution_surjective_iff_differences_surjective
    (P : NormalizedPageFamily H N F f)
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (i j : ℕ) (hij : i ≤ j) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n)
    (hki : P.lambdaExponent n < i) (hkj : P.lambdaExponent n < j)
    (x : permanentCycles H X (s, t)) (y : permanentCycles H Y (s + n, t + n))
    (a : P.PermanentFiniteSolutions j n s t hn hkj x y) :
    Function.Surjective (restrictPermanentFiniteSolution I J i j hij n s t hn hki hkj x y) ↔
      Function.Surjective (FilteredComplex.Solutions.restrictDifferences
        (I.complexMap i j (lt_of_le_of_lt (Nat.zero_le _) hki)
          (lt_of_le_of_lt (Nat.zero_le _) hkj) hij (P.degree s t))
        (ModuleCat.of ℤ (ULift.{v} ℤ)) n s 1) := by
  have transport {FC GD : FilteredComplex (ModuleCat.{v} ℤ)}
      (g : FilteredComplex.Morphism FC GD)
      {xx : ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ FC.assocGraded s 1}
      {yy : ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ FC.assocGraded (s + n) 0}
      (b : FilteredComplex.Solutions.Fiber FC n s 1 xx yy)
      (xi : ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ GD.assocGraded s 1)
      (yi : ModuleCat.of ℤ (ULift.{v} ℤ) ⟶ GD.assocGraded (s + n) 0)
      (hx : xx ≫ g.associatedGradedMap s 1 = xi)
      (hy : yy ≫ g.associatedGradedMap (s + n) 0 = yi) :
      Function.Surjective (fun c : FilteredComplex.Solutions.Fiber FC n s 1 xx yy =>
        show FilteredComplex.Solutions.Fiber GD n s 1 xi yi from by
          have d := FilteredComplex.Solutions.restrict g c
          erw [hx] at d
          erw [hy] at d
          exact d) ↔ Function.Surjective
            (FilteredComplex.Solutions.restrictDifferences g (ModuleCat.of ℤ (ULift.{v} ℤ)) n s 1) := by
    cases hx
    cases hy
    exact FilteredComplex.Solutions.restrict_surjective_iff_differences_surjective g b
  exact transport
    (I.complexMap i j (lt_of_le_of_lt (Nat.zero_le _) hki)
      (lt_of_le_of_lt (Nat.zero_le _) hkj) hij (P.degree s t)) a _ _
    (J.source i j _ _ hij s t
      (Submodule.inclusion (permanentCycles_le_cycles H X (s, t) i) x)
      (Submodule.inclusion (permanentCycles_le_cycles H X (s, t) j) x) rfl)
    (J.target i j _ _ hij n s t hn hki hkj
      (Submodule.inclusion (permanentCycles_le_cycles H Y (s + n, t + n)
        (i - P.lambdaExponent n : ℕ)) y)
      (Submodule.inclusion (permanentCycles_le_cycles H Y (s + n, t + n)
        (j - P.lambdaExponent n : ℕ)) y) rfl)

/-- The coherent tower can be chosen to extend the given solution at the
first admissible quotient length `q = lambdaExponent n + 1`. -/
theorem exists_coherentPageExtensionSolutions_of_surjective
    (P : NormalizedPageFamily H N F f)
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : permanentCycles H X (s, t)) (y : permanentCycles H Y (s + n, t + n))
    (a₀ : P.PermanentFiniteSolutions (P.lambdaExponent n + 1) n s t hn
      (Nat.lt_succ_self _) x y)
    (hsurj : ∀ (q : ℕ) (hkq : P.lambdaExponent n < q),
      Function.Surjective (restrictPermanentFiniteSolution I J q (q + 1) (Nat.le_succ q)
        n s t hn hkq (lt_trans hkq (Nat.lt_succ_self q)) x y)) :
    ∃ a : CoherentPageExtensionSolutions P I J n s t hn x y,
      a.solution (P.lambdaExponent n + 1) (Nat.lt_succ_self _) = a₀ := by
  obtain ⟨a, ha₀, ha⟩ := KIP126.Core.InverseSequence.exists_compatible_of_surjective
    (P.lambdaExponent n + 1)
    (fun q hq => P.PermanentFiniteSolutions q n s t hn (Nat.lt_of_succ_le hq) x y)
    (fun q hq => restrictPermanentFiniteSolution I J q (q + 1) (Nat.le_succ q)
      n s t hn (Nat.lt_of_succ_le hq)
      (lt_trans (Nat.lt_of_succ_le hq) (Nat.lt_succ_self q)) x y)
    (fun q hq => hsurj q (Nat.lt_of_succ_le hq)) a₀
  refine ⟨{
    solution := fun q hkq => a q (Nat.succ_le_of_lt hkq)
    compatible := ?_ }, ha₀⟩
  intro q hkq
  exact ha q (Nat.succ_le_of_lt hkq)

theorem nonempty_coherentPageExtensionSolutions_of_surjective
    (P : NormalizedPageFamily H N F f)
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : permanentCycles H X (s, t)) (y : permanentCycles H Y (s + n, t + n))
    (a₀ : P.PermanentFiniteSolutions (P.lambdaExponent n + 1) n s t hn
      (Nat.lt_succ_self _) x y)
    (hsurj : ∀ (q : ℕ) (hkq : P.lambdaExponent n < q),
      Function.Surjective (restrictPermanentFiniteSolution I J q (q + 1) (Nat.le_succ q)
        n s t hn hkq (lt_trans hkq (Nat.lt_succ_self q)) x y)) :
    Nonempty (CoherentPageExtensionSolutions P I J n s t hn x y) := by
  obtain ⟨a, _⟩ := exists_coherentPageExtensionSolutions_of_surjective P I J n s t hn x y a₀ hsurj
  exact ⟨a⟩

/-- Nonempty finite fibers and surjective actual homogeneous restrictions
produce a coherent tower extending the specified initial solution. -/
theorem exists_coherentPageExtensionSolutions_of_differences_surjective
    (P : NormalizedPageFamily H N F f)
    (I : PageExtensionRestrictionFiltration P) (J : PageExtensionRestrictionLabels P I)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (x : permanentCycles H X (s, t)) (y : permanentCycles H Y (s + n, t + n))
    (a₀ : P.PermanentFiniteSolutions (P.lambdaExponent n + 1) n s t hn
      (Nat.lt_succ_self _) x y)
    (hne : ∀ (q : ℕ) (hkq : P.lambdaExponent n < q),
      Nonempty (P.PermanentFiniteSolutions q n s t hn hkq x y))
    (hsurj : ∀ (q : ℕ) (hkq : P.lambdaExponent n < q),
      Function.Surjective (FilteredComplex.Solutions.restrictDifferences
        (I.complexMap q (q + 1) (lt_of_le_of_lt (Nat.zero_le _) hkq)
          (lt_of_le_of_lt (Nat.zero_le _) (lt_trans hkq (Nat.lt_succ_self q)))
          (Nat.le_succ q) (P.degree s t))
        (ModuleCat.of ℤ (ULift.{v} ℤ)) n s 1)) :
    ∃ a : CoherentPageExtensionSolutions P I J n s t hn x y,
      a.solution (P.lambdaExponent n + 1) (Nat.lt_succ_self _) = a₀ := by
  apply exists_coherentPageExtensionSolutions_of_surjective P I J n s t hn x y a₀
  intro q hkq
  obtain ⟨a⟩ := hne (q + 1) (lt_trans hkq (Nat.lt_succ_self q))
  exact (restrictPermanentFiniteSolution_surjective_iff_differences_surjective
    P I J q (q + 1) (Nat.le_succ q) n s t hn hkq
    (lt_trans hkq (Nat.lt_succ_self q)) x y a).mpr (hsurj q hkq)

end KIP126.Def.Comparison.StageInterfaces
