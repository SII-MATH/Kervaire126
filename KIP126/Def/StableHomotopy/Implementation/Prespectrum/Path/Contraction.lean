module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Homotopy.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.HomotopyCategory.Quotient

@[expose] public section

section

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

end

section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory
open scoped unitInterval

universe u

@[simp] theorem pathContraction_zero (X : Prespectrum.{u}) :
    pathContraction X ≫ pathEvaluation (pathPrespectrum X) 0 =
      pathEvaluation X 0 ≫ pathConstant X := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro x
  apply ContinuousMap.ext; intro t
  change (show C(I,X.level n) from x) (0 * t) = (show C(I,X.level n) from x) 0
  rw [zero_mul]

@[simp] theorem pathContraction_one (X : Prespectrum.{u}) :
    pathContraction X ≫ pathEvaluation (pathPrespectrum X) 1 =
      𝟙 (pathPrespectrum X) := by
  apply Hom.ext; funext n
  apply ContinuousMap.ext; intro x
  apply ContinuousMap.ext; intro t
  change (show C(I,X.level n) from x) (1 * t) = (show C(I,X.level n) from x) t
  rw [one_mul]

/-- Actual constant paths are already invertible in the strict homotopy
category, before stable localization. -/
instance homotopyQuotient_pathConstant_isIso (X : Prespectrum.{u}) :
    IsIso (homotopyQuotient.map (pathConstant X)) := by
  refine ⟨homotopyQuotient.map (pathEvaluation X 0), ?_, ?_⟩
  · rw [← Functor.map_comp, pathConstant_comp_evaluation, homotopyQuotient.map_id]
  · rw [← Functor.map_comp, ← homotopyQuotient.map_id]
    exact (homotopyQuotient_map_eq_iff _ _).mpr
      ⟨⟨pathContraction X, pathContraction_zero X, pathContraction_one X⟩⟩

end KIP126.StableHomotopy.Implementation.Prespectrum

end
