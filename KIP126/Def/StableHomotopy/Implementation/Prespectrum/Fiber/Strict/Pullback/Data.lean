module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Strict.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
universe u

/-- Forget the forced basepoint coordinate of the strict fiber of a pullback projection. -/
def strictFiberPullbackTo {A B Z : Prespectrum.{u}} (p : A ⟶ B) (g : Z ⟶ B) :
    strictFiber (pullbackSnd p g) ⟶ strictFiber p where
  level n :=
    { toFun z := ⟨(z.val.1.val.1,z.val.2),by
        change p.level n z.val.1.val.1 = (B.level n).point
        exact z.val.1.property.trans
          ((congrArg (g.level n) z.property).trans (g.point n))⟩
      continuous_toFun := (continuous_subtype_val.fst.subtype_val.fst.prodMk
        continuous_subtype_val.snd).subtype_mk _ }
  point _ := rfl
  bond _ _ _ := rfl

/-- Insert the basepoint in the pulled-back object's coordinate. -/
def strictFiberPullbackFrom {A B Z : Prespectrum.{u}} (p : A ⟶ B) (g : Z ⟶ B) :
    strictFiber p ⟶ strictFiber (pullbackSnd p g) where
  level n :=
    { toFun z := ⟨(⟨(z.val.1,(Z.level n).point),z.property.trans (g.point n).symm⟩,z.val.2),rfl⟩
      continuous_toFun := (((continuous_subtype_val.fst.prodMk continuous_const).subtype_mk _).prodMk
        continuous_subtype_val.snd).subtype_mk _ }
  point _ := rfl
  bond n z t := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext rfl (Z.bond_point n t).symm
    · rfl

/-- Strict kernels are preserved by the actual strict pullback, through an
explicit strict isomorphism before localization. -/
def strictFiberPullbackIso {A B Z : Prespectrum.{u}} (p : A ⟶ B) (g : Z ⟶ B) :
    strictFiber (pullbackSnd p g) ≅ strictFiber p where
  hom := strictFiberPullbackTo p g
  inv := strictFiberPullbackFrom p g
  hom_inv_id := by
    apply Hom.ext
    funext n
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext rfl z.property.symm
    · rfl
  inv_hom_id := rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
