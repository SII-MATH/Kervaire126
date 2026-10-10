import KIP126.Def.Synthetic.PageExtension.Family.Data

namespace KIP126.Synthetic.PageExtension

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence KIP126.Classical.Adams

universe u v u' v'
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type u'} [SyntheticCategory.{u', v'} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}

private theorem iso_hom_eq_zero_iff {A B : ModuleCat.{v'} ℤ} (e : A ≅ B) (x : A) :
    e.hom.hom x = 0 ↔ x = 0 := e.toLinearEquiv.map_eq_zero_iff

private theorem iso_inv_eq_zero_iff {A B : ModuleCat.{v'} ℤ} (e : A ≅ B) (x : B) :
    e.inv.hom x = 0 ↔ x = 0 := iso_hom_eq_zero_iff e.symm x

private theorem eqToHom_eq_zero_iff {A B : ModuleCat.{v'} ℤ} (h : A = B) (x : A) :
    (eqToHom h : A ⟶ B).hom x = 0 ↔ x = 0 := iso_hom_eq_zero_iff (eqToIso h) x

/-- ESS ambient identifications and degree transports are isomorphisms.
Thus they do not alter the kernel of the actual finite λ-scaled E∞ map. -/
theorem NormalizedPageFamily.finiteTargetMap_eq_zero_iff (P : NormalizedPageFamily H N F f)
    (q : ℕ) (hq : 0 < q) (n s t : ℤ)
    (hn : (normalizedExponent H f : ℤ) ≤ n) (hkq : P.lambdaExponent n < q)
    (z : PageRepresentatives.cycles H Y (q - P.lambdaExponent n : ℕ) (s + n, t + n)) :
    P.finiteTargetMap q hq n s t hn hkq z = 0 ↔
      ((F.functor.map (P.targetTower.lambdaInclusion (P.lambdaExponent n) q hkq)).eInftyMap
        (s + n, t + n, t + n - P.lambdaExponent n)).hom
          (P.finiteTarget q (P.lambdaExponent n) hkq (s + n) (t + n) z) = 0 := by
  unfold NormalizedPageFamily.finiteTargetMap
  simp only [LinearMap.comp_apply, eqToHom_eq_zero_iff, iso_inv_eq_zero_iff]
  rfl

/-- The untruncated ESS identifications likewise preserve the λ-map kernel. -/
theorem NormalizedPageFamily.infiniteTargetMap_eq_zero_iff (P : NormalizedPageFamily H N F f)
    (n s t : ℤ) (hn : (normalizedExponent H f : ℤ) ≤ n)
    (z : PageRepresentatives.permanentCycles H Y (s + n, t + n)) :
    P.infiniteTargetMap n s t hn z = 0 ↔
      ((F.functor.map (lambdaPow (P.lambdaExponent n) (N.functor.obj Y))).eInftyMap
        (s + n, t + n, t + n - P.lambdaExponent n)).hom
          (P.infiniteTarget (P.lambdaExponent n) (s + n) (t + n) z) = 0 := by
  unfold NormalizedPageFamily.infiniteTargetMap
  simp only [LinearMap.comp_apply, eqToHom_eq_zero_iff, iso_inv_eq_zero_iff]
  rfl

end KIP126.Synthetic.PageExtension
