module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cofiber.Pushout.Existence.Proofs

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u
/-- The actual quotient comparison induced by the displayed pushout. -/
noncomputable def cofiberPushoutIso {A B C D : Prespectrum.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout f g i j) : pointSetCofiber f ≅ pointSetCofiber j :=
  (cofiberPushoutIso_exists h).choose
end KIP126.StableHomotopy.Implementation.Prespectrum
