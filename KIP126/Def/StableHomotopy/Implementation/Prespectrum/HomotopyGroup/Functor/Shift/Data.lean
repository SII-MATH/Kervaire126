module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.Source.Shift.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyGroup.Functor.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- Integer suspension on the original stable groups, through their actual
representing spheres and the fixed coherent shift. -/
noncomputable def sourceStableHomotopyShiftEquiv (X : SourceCategory.{0}) (d k : ℤ) :
    (sourceStableHomotopyAddFunctor (d-k)).obj X ≃
      (sourceStableHomotopyAddFunctor d).obj (X⟦k⟧) :=
  (Prespectrum.sourceStableHomotopyEquiv X.as.obj (d-k)).trans
    ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor SourceCategory k)).homEquiv.trans
      ((Iso.homCongr
        (Prespectrum.sourceSphere_addShiftIso (d-k) k ≪≫
          eqToIso (congrArg Prespectrum.sourceSphere (sub_add_cancel d k)))
        (Iso.refl (X⟦k⟧))).trans
        (Prespectrum.sourceStableHomotopyEquiv (X⟦k⟧).as.obj d).symm))

end KIP126.StableHomotopy.Implementation
