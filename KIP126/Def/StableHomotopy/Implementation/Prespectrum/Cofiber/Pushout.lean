module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Pushout.Existence.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
/-- The actual quotient comparison induced by the displayed pushout. -/
noncomputable def cofiberPushoutIso {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) : pointSetCofiber f ≅ pointSetCofiber j :=
  (cofiberPushoutIso_exists h).choose
end KIP126.StableHomotopy.Implementation.Prespectrum

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
@[reassoc] theorem cofiberPushoutIso_projection {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) :
    cofiberProjection f ≫ (cofiberPushoutIso h).hom = i ≫ cofiberProjection j :=
  (cofiberPushoutIso_exists h).choose_spec
end KIP126.StableHomotopy.Implementation.Prespectrum

end
