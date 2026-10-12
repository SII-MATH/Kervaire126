module

public import KIP126.Def.StableHomotopy.Implementation.Singular.Evaluation.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation
open CategoryTheory
universe u

/-- Realization of the actual singular map induced by a based continuous map. -/
noncomputable def singularRealizationMap {A B : BasedSpace.{u}} (f : A ⟶ B) :
    C(singularRealization A,singularRealization B) :=
  (SSet.toTop.map (TopCat.toSSet.map (TopCat.ofHom (X := A.space) (Y := B.space) f.map))).hom

end KIP126.StableHomotopy.Implementation
