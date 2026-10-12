module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.HomotopyExtension.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Comparison.Stability.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Universal.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual quotient of a cubical cofibration is cofibrant. The
relative lift vanishes exactly on the attached source before descending. -/
theorem IsCubicalCofibration.pointSetCofiber {X Y : Prespectrum.{u}}
    {f : X ⟶ Y} (hf : IsCubicalCofibration f) :
    IsCubicallyCofibrant (pointSetCofiber f) := by
  intro E B p hp
  constructor
  intro t b sq
  letI := hf p hp
  let s : CommSq (zeroMap X E) f p (cofiberProjection f ≫ b) := ⟨by
    rw [← Category.assoc,cofiberProjection_comp]
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact (p.point n).trans (b.point n).symm⟩
  refine CommSq.HasLift.mk' {
    l := cofiberDesc f s.lift s.fac_left
    fac_left := zeroPrespectrum_isZero.eq_of_src _ _
    fac_right := ?_ }
  apply cofiberHom_ext f
  rw [← Category.assoc,cofiberProjection_desc]
  exact s.fac_right

/-- The actual cone-to-quotient map is a stable equivalence for every
actual cubical cofibration with cofibrant source. -/
theorem IsCubicalCofibration.coneToCofiber_stableEquivalence
    {X Y : Prespectrum.{u}} {f : X ⟶ Y} (hf : IsCubicalCofibration f)
    (hX : IsCubicallyCofibrant X) : stableEquivalences (coneToCofiber f) :=
  Prespectrum.coneToCofiber_stableEquivalence f (hf.level_hasHomotopyExtension hX)

end KIP126.StableHomotopy.Implementation.Prespectrum
