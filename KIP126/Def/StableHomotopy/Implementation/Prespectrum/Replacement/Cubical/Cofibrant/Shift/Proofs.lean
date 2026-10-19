module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Tail.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
universe u
set_option backward.isDefEq.respectTransparency false

/-- Padded desuspension preserves the actual cubical left lifting
property, since the relevant right lifting conditions simply shift levels. -/
theorem IsCubicallyCofibrant.desuspension {X : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) : IsCubicallyCofibrant X.desuspension := by
  intro E B p hp
  constructor
  intro t b sq
  obtain ⟨l, hl⟩ := hX.lift (levelTailMap p) (fun n => hp (n+1)) (levelTailMap b)
  refine CommSq.HasLift.mk' {
    l := desuspensionMap l ≫ paddedTailInclusion E
    fac_left := zeroPrespectrum_isZero.eq_of_src _ _
    fac_right := ?_ }
  apply Hom.ext
  funext n
  cases n with
  | zero =>
    apply ContinuousMap.ext
    intro x
    exact (p.point 0).trans (b.point 0).symm
  | succ n =>
    exact congrArg (fun k : X ⟶ levelTail B => k.level n) hl

end KIP126.StableHomotopy.Implementation.Prespectrum
