module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Identity.Square
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal identity mapping cone is strictly contractible, with a
continuous contraction commuting with every spectrum bond. -/
def coneIdentityContraction (X : Prespectrum.{u}) :
    StrictHomotopy (𝟙 (cone (𝟙 X))) (zeroMap (cone (𝟙 X)) (cone (𝟙 X))) := by
  let H := coneLift (𝟙 X) (coneNullPath (𝟙 X)) (coneIdentitySquare X)
    (by simpa only [Category.id_comp] using coneIdentitySquare_zero X) (coneIdentitySquare_one X)
  refine { hom := H, zero := ?_, one := ?_ }
  · apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro (x | ⟨x,s⟩)
    · exact Quot.sound (ConeRelation.start x)
    · change Quot.mk (ConeRelation (𝟙 X) n)
        (.inr (x,unitInterval.symm (unitInterval.symm s * unitInterval.symm 0))) =
        Quot.mk (ConeRelation (𝟙 X) n) (.inr (x,s))
      simp
  · apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    refine Quot.inductionOn z ?_
    rintro (x | ⟨x,s⟩)
    · exact Quot.sound (ConeRelation.finish x)
    · change Quot.mk (ConeRelation (𝟙 X) n)
        (.inr (x,unitInterval.symm (unitInterval.symm s * unitInterval.symm 1))) =
        (coneLevel (𝟙 X) n).point
      simp only [unitInterval.symm_one,mul_zero,unitInterval.symm_zero]
      exact Quot.sound (ConeRelation.finish x)
end KIP126.StableHomotopy.Implementation.Prespectrum
