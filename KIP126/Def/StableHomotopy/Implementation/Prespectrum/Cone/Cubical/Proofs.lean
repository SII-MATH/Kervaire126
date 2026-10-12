module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibrant.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Universal.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Zero.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology.HomotopyLifting
universe u
set_option backward.isDefEq.respectTransparency false

/-- Literal mapping cones of spectra with the actual cubical left
lifting property retain that property: lift the bottom, then lift its
retained nullhomotopy with both endpoints fixed, and use the actual quotient. -/
theorem IsCubicallyCofibrant.cone {X Y : Prespectrum.{u}}
    (hX : IsCubicallyCofibrant X) (hY : IsCubicallyCofibrant Y) (f : X ⟶ Y) :
    IsCubicallyCofibrant (cone f) := by
  intro E B p hp
  constructor
  intro t b sq
  obtain ⟨a,ha⟩ := hY.lift p hp (coneInclusion f ≫ b)
  let H : StrictHomotopy ((f ≫ a) ≫ p) ((zeroMap X E) ≫ p) := {
    hom := coneNullPath f ≫ pathMap b
    zero := by rw [Category.assoc,pathMap_evaluation,← Category.assoc,coneNullPath_zero,
      Category.assoc,← ha,Category.assoc]
    one := by
      rw [Category.assoc,pathMap_evaluation,← Category.assoc,coneNullPath_one]
      apply Hom.ext
      funext n
      apply ContinuousMap.ext
      intro x
      exact (b.point n).trans (p.point n).symm }
  obtain ⟨G,hG⟩ := hX.lift_strictHomotopy p hp H
  let l : Prespectrum.cone f ⟶ E := coneLift f a G.hom G.zero G.one
  have hl : l ≫ p = b := by
    apply coneHom_ext f
    · rw [← Category.assoc,coneInclusion_lift]
      exact ha
    · rw [pathMap_comp,← Category.assoc,coneNullPath_lift]
      exact hG
  exact CommSq.HasLift.mk' { l := l, fac_left := zeroPrespectrum_isZero.eq_of_src _ _, fac_right := hl }

/-- In particular, the literal cone of a map between the actual free-cell
replacements is itself an actual retract of a free-cell replacement. -/
theorem cone_cubicalReplacementComparison_hasSection (X Y : Prespectrum.{u})
    (f : cubicalReplacementFunctor.obj X ⟶ cubicalReplacementFunctor.obj Y) :
    ∃ s : cone f ⟶ cubicalReplacementFunctor.obj (cone f),
      s ≫ cubicalReplacementComparison.app (cone f) = 𝟙 (cone f) :=
  IsCubicallyCofibrant.replacement_hasSection
    (IsCubicallyCofibrant.cone (cubicalReplacement_isCubicallyCofibrant X)
      (cubicalReplacement_isCubicallyCofibrant Y) f)

end KIP126.StableHomotopy.Implementation.Prespectrum
