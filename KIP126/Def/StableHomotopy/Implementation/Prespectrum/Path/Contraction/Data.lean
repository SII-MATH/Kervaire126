module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory Topology
open scoped unitInterval

universe u

/-- Simultaneously shorten every actual path, compatibly with all bonds. -/
def pathContraction (X : Prespectrum.{u}) :
    pathPrespectrum X ⟶ pathPrespectrum (pathPrespectrum X) where
  level n :=
    (⟨fun z => z.1.1 (z.1.2 * z.2),
      continuous_fst.fst.eval
        ((continuous_fst.snd.subtype_val.mul continuous_snd.subtype_val).subtype_mk _)⟩ :
      C((C(I,X.level n) × I) × I,X.level n)).curry.curry
  point n := by
    apply ContinuousMap.ext; intro s
    apply ContinuousMap.ext; intro t
    rfl
  bond n x t := by
    apply ContinuousMap.ext; intro s
    apply ContinuousMap.ext; intro r
    rfl

end KIP126.StableHomotopy.Implementation.Prespectrum
