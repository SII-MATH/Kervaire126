module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Normalization.Proofs
public import Mathlib.CategoryTheory.Yoneda

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- Based homotopy and stabilization descend actual cubical representatives to localized sphere morphisms. -/
noncomputable def stableHomotopySourceMap (X : Prespectrum) (d : ℤ) :
    StableHomotopy X d → (sourceSphere d ⟶ sourceLocalization.obj X) :=
  Quot.lift Representative.sourceMap Representative.sourceMap_relation

/-- The cubical-to-morphism construction is natural for every localized morphism, including inverses of actual stable equivalences. The universe lift only matches the localization morphism universe. -/
noncomputable def sourceStableHomotopyToHom (d : ℤ) :
    (sourceStableHomotopyFunctor.{0} d ⋙ uliftFunctor.{1,0}) ⟶ coyoneda.obj (Opposite.op (sourceSphere d)) :=
  Localization.Construction.natTransExtension {
    app X := TypeCat.ofHom (fun x => stableHomotopySourceMap X d x.down)
    naturality := by
      intro X Y f
      ext x
      change stableHomotopySourceMap Y d
        (((sourceStableHomotopyFunctor d).map (sourceLocalization.map f)) x.down) =
        stableHomotopySourceMap X d x.down ≫ sourceLocalization.map f
      rw [sourceStableHomotopyFunctor_map]
      exact Quot.inductionOn x.down (fun a => a.sourceMap_natural f) }

end KIP126.StableHomotopy.Implementation.Prespectrum
