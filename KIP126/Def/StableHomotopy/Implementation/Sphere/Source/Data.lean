module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Equivalence

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
set_option backward.isDefEq.respectTransparency false

/-- Every nonnegative specified source sphere is strictly isomorphic to the corresponding iterated actual levelwise suspension of the point-set sphere. -/
noncomputable def sourceSpherePrespectrum_positiveIso : ∀ n : ℕ,
    sourceSpherePrespectrum (n : ℤ) ≅ (suspension^[n]) sphere
  | 0 => eqToIso sourceSpherePrespectrum_zero
  | n+1 => suspensionSpectrumSuspensionIso (sphereLevel n) ≪≫
      suspensionFunctor.mapIso (sourceSpherePrespectrum_positiveIso n) ≪≫
        eqToIso (Function.iterate_succ_apply' suspension n sphere).symm

/-- The source representing sphere agrees with the actual suspension/desuspension construction in every integer degree. -/
noncomputable def sourceSphere_actualShiftIso (d : ℤ) :
    sourceSphere d ≅ sourceLocalization.obj
      (if 0 ≤ d then (suspension^[d.toNat]) sphere else (desuspension^[(-d).toNat]) sphere) := by
  cases d with
  | ofNat n =>
    have hn : 0 ≤ (Int.ofNat n : ℤ) := Int.natCast_nonneg n
    rw [if_pos hn]
    exact sourceLocalization.mapIso (sourceSpherePrespectrum_positiveIso n)
  | negSucc n =>
    have hn : ¬ 0 ≤ Int.negSucc n := by omega
    rw [if_neg hn]
    apply sourceLocalization.mapIso
    apply eqToIso
    change (desuspension^[n+1]) (suspensionSpectrum BasedSpace.zeroSphere) = _
    rw [suspensionSpectrum_zeroSphere]
    rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
