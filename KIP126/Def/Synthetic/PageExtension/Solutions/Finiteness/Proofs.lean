import KIP126.Def.Synthetic.PageExtension.Solutions.Permanent.Data
import KIP126.Def.Synthetic.ExtensionSS.Solutions.Finiteness.Proofs

namespace KIP126.Synthetic.PageExtension.NormalizedPageFamily

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Classical.Adams KIP126.Classical.Adams.PageRepresentatives
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

theorem finite_finiteSolutions_of_finite_source (P : NormalizedPageFamily H N F f)
    (q : ℕ) (hq : 0 < q) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n) (hkq : P.lambdaExponent n < q)
    (x : cycles H X q (s, t))
    (y : cycles H Y (q - P.lambdaExponent n : ℕ) (s + n, t + n))
    [Finite (syntheticHomotopy (XModLambdaN (normalizedSource H N f) q) (P.degree s t))] :
    Finite (P.FiniteSolutions q hq n s t hn hkq x y) := by
  haveI : Finite (syntheticHomotopy
      (XModLambdaN ((SyntheticCategory.biShift (0, (normalizedExponent H f : ℤ))).obj
        (N.functor.obj X)) q) (P.degree s t)) :=
    inferInstanceAs (Finite
      (syntheticHomotopy (XModLambdaN (normalizedSource H N f) q) (P.degree s t)))
  exact (P.finite q hq).finite_solutions_of_finite_source (P.degree s t) n s _ _

theorem finite_permanentFiniteSolutions_of_finite_source
    (P : NormalizedPageFamily H N F f)
    (q : ℕ) (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (hkq : P.lambdaExponent n < q)
    (x : permanentCycles H X (s, t)) (y : permanentCycles H Y (s + n, t + n))
    [Finite (syntheticHomotopy (XModLambdaN (normalizedSource H N f) q) (P.degree s t))] :
    Finite (P.PermanentFiniteSolutions q n s t hn hkq x y) :=
  P.finite_finiteSolutions_of_finite_source q (by omega) n s t hn hkq _ _

end KIP126.Synthetic.PageExtension.NormalizedPageFamily
