module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Source.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.SourceShift.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The specified degree-n source sphere has no actual stable homotopy
below n, including negative sphere degrees. -/
theorem sourceSphere_homotopy_subsingleton (n d : ℤ) (hd : d < n) :
    Subsingleton ((sourceStableHomotopyAddFunctor d).obj (sourceSphere n)) := by
  have e := sourceSphere_actualShiftIso n
  by_cases hn : 0 ≤ n
  · simp only [if_pos hn] at e
    have he : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    letI := sphere_stableHomotopy_subsingleton_of_neg (d - n.toNat) (by omega)
    exact ((stableHomotopyEquivOfSourceIso e d).trans
      (stableHomotopyIterateSuspensionEquiv sphere n.toNat d)).injective.subsingleton
  · simp only [if_neg hn] at e
    have he : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
    letI := sphere_stableHomotopy_subsingleton_of_neg (d + (-n).toNat) (by omega)
    exact ((stableHomotopyEquivOfSourceIso e d).trans
      (stableHomotopyIterateDesuspensionEquiv sphere (-n).toNat d)).injective.subsingleton

end KIP126.StableHomotopy.Implementation.Prespectrum
