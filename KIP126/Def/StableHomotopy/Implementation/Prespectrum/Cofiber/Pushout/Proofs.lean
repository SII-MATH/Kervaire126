module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Pushout.Data

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
@[reassoc] theorem cofiberPushoutIso_projection {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) :
    cofiberProjection f ≫ (cofiberPushoutIso h).hom = i ≫ cofiberProjection j :=
  (cofiberPushoutIso_exists h).choose_spec
end KIP126.StableHomotopy.Implementation.Prespectrum
