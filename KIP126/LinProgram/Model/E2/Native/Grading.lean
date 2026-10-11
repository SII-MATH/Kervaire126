import KIP126.LinProgram.Model.E2.Native.Compatibility
import KIP126.Def.Algebra.GradedQuotient.Data
import KIP126.LinProgram.Certificates.RelationCatalogue.Homogeneity
import Mathlib.RingTheory.GradedAlgebra.AlgHom

/-! The fixed native quotient is genuinely bigraded. The comparison with the
historical cutoff is proved on every component of internal degree at most 261. -/
namespace KIP126.LinE2
open KIP126.Core.Algebra MvPolynomial
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

local instance : GradedAlgebra (weightedHomogeneousSubmodule F2 generatorDegree) :=
  weightedGradedAlgebra F2 generatorDegree

/-- Homogeneity uses all original relations, certified against the original archive. -/
theorem nativeIdeal_isHomogeneous :
    nativeIdeal.IsHomogeneous (weightedHomogeneousSubmodule F2 generatorDegree) := by
  apply Ideal.homogeneous_span
  rintro p ⟨code, hc, rfl⟩
  exact csv_relation_isWeightedHomogeneous code hc

/-- Every native class has a unique finite homogeneous decomposition. -/
instance nativeGradedAlgebra : GradedAlgebra
    (fun d : ℕ × ℕ => nativeHomogeneousPart d.1 d.2) :=
  KIP126.Algebra.GradedQuotient.gradedAlgebra
    (weightedHomogeneousSubmodule F2 generatorDegree) nativeIdeal nativeIdeal_isHomogeneous

/-- The polynomial projection preserves the full bigrading, with no degree cutoff. -/
def nativeProjectionGraded :
    GradedAlgHom F2 (weightedHomogeneousSubmodule F2 generatorDegree)
      (fun d : ℕ × ℕ => nativeHomogeneousPart d.1 d.2) where
  toAlgHom := nativeProjection
  map_mem := by
    intro d p hp
    exact ⟨p, hp, rfl⟩

/-- Removing the artificial high-degree zeros changes no component through degree 261. -/
def truncateAtEquiv (s t : ℕ) (ht : t ≤ 261) : NativeAt s t ≃ₗ[F2] E2At s t :=
  LinearEquiv.ofBijective (truncateAt s t)
    ⟨truncateAt_injective_of_homogeneous nativeIdeal_isHomogeneous s t ht,
      truncateAt_surjective s t⟩

@[simp] theorem truncateAtEquiv_apply_val (s t : ℕ) (ht : t ≤ 261) (x : NativeAt s t) :
    (truncateAtEquiv s t ht x).val = truncate x.val := rfl

@[simp] theorem truncateAtEquiv_symm_apply (s t : ℕ) (ht : t ≤ 261) (x : E2At s t) :
    truncate ((truncateAtEquiv s t ht).symm x).val = x.val := by
  exact congrArg Subtype.val ((truncateAtEquiv s t ht).apply_symm_apply x)

/-- The low-degree inverse identifies products whenever the product degree is covered. -/
theorem truncateAtEquiv_mul {s t s' t' : ℕ} (ht : t+t' ≤ 261)
    (x : NativeAt s t) (y : NativeAt s' t') :
    (truncateAtEquiv (s+s') (t+t') ht (nativeMultiply x y)).val =
      (truncateAtEquiv s t (by omega) x).val *
        (truncateAtEquiv s' t' (by omega) y).val := map_mul truncate x.val y.val

end
end KIP126.LinE2
