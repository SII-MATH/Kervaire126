module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Pushout.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Map.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits

universe u

/-- The specified actual pushout-cofiber isomorphisms commute with strict
maps of the original squares, retaining their original quotient maps. -/
@[reassoc] theorem cofiberPushoutIso_natural
    {A B C D A' B' C' D' : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ D'} {j' : C' ⟶ D'}
    (h : IsPushout f g i j) (h' : IsPushout f' g' i' j')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (hf : f ≫ b = a ≫ f') (hi : i ≫ d = b ≫ i') (hj : j ≫ d = c ≫ j') :
    (cofiberPushoutIso h).hom ≫ cofiberMap c d hj =
      cofiberMap a b hf ≫ (cofiberPushoutIso h').hom := by
  apply cofiberHom_ext f
  rw [cofiberPushoutIso_projection_assoc,cofiberProjection_map,
    cofiberProjection_map_assoc,cofiberPushoutIso_projection,← Category.assoc,hi,Category.assoc]

end KIP126.StableHomotopy.Implementation.Prespectrum
