module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Replacement.Cubical.Cofibration.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Cone.Pushout.Excision.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
universe u

/-- Actual cubical attachment supplies cofibrancy of both new objects;
only the original two sources need their actual lifting property checked.
The levelwise homotopy-extension hypothesis remains explicit. -/
theorem isPushout_stableEquivalence_of_cubicalCofibration
    {A B C D : Prespectrum.{u}}
    (hA : IsCubicallyCofibrant A) (hC : IsCubicallyCofibrant C)
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hf : IsCubicalCofibration f) (h : IsPushout f g i j)
    (hE : ∀ n, KIP126.Topology.HomotopyExtension.HasHomotopyExtension
      (TopCat.ofHom (f.level n))) (hg : stableEquivalences g) :
    stableEquivalences i :=
  isPushout_stableEquivalence_of_isCubicallyCofibrant
    hA (hA.of_cubicalCofibration hf) hC (hC.pushout hf h) h hE hg

end KIP126.StableHomotopy.Implementation.Prespectrum
