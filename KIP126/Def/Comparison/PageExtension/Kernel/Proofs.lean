import KIP126.Def.Comparison.PageExtension.Targets.Data
import KIP126.Def.Comparison.PageExtension.Ambiguity.Predicates
import KIP126.Def.ClassicalAdams.PageRepresentatives.Quotient.Top.Proofs
import KIP126.Def.Synthetic.PageExtension.Target.Proofs

namespace KIP126.Def.Comparison.StageInterfaces

set_option backward.isDefEq.respectTransparency false

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Synthetic.Context KIP126.Synthetic.SpectralSequence
open KIP126.Synthetic.PageExtension KIP126.Classical.Adams.PageRepresentatives KIP126.Challenge2

universe u v w
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w, v} Syn]
  [HasFunctorialCofiber (C := Syn)]
  {H : Mod2EilenbergMacLane (C := C)} {N : NuFunctorData C Syn}
  {F : SyntheticAdamsFamily Syn} {X Y : C} {f : X ⟶ Y}
  (P : NormalizedPageFamily H N F f)
  (R : KIP126.Challenge2.SyntheticEInftyPresentation H N F) (S : EInftyWeightShift F)
  (T : ∀ X : C, FiniteLambdaQuotientTower (N.functor.obj X))
  (K : KIP126.Challenge2.SyntheticEInftyMapCompatibility H N F R S T)
  (J : PageExtensionTargetComparison P R S T)

include K J

/-- The kernel of the actual λ-scaled finite target follows from the two
comparison diagrams and the classical subquotient, without a kernel input. -/
theorem finiteLambdaTarget_eq_zero_iff (q k : ℕ) (hkq : k < q) (s t : ℤ)
    (z : cycles H Y (q - k : ℕ) (s, t)) :
    ((F.functor.map (P.targetTower.lambdaInclusion k q hkq)).eInftyMap
      (s, t, t - k)).hom (P.finiteTarget q k hkq s t z) = 0 ↔
        z.val ∈ boundaries H Y (1 + k) (s, t) := by
  let a := S.lowerIso (XModLambdaN (N.functor.obj Y) (q - k)) k (s, t) t
    (P.finiteTarget q k hkq s t z)
  have he := K.lambda_finite Y q k hkq (s, t) t
    (by constructor <;> simp <;> omega) a
  erw [show R.finiteWindow Y (q - k) (by omega) (s, t) t
      (by constructor <;> simp <;> omega) a = finiteTopClass H Y (q - k) (s, t) z
        from J.finite q k hkq s t z] at he
  change R.finiteWindow Y q (by omega) (s, t) (t - k)
      (by constructor <;> simp <;> omega)
      (((F.functor.map ((T Y).lambdaInclusion k q hkq)).eInftyMap (s, t, t - k)).hom
        ((S.lowerIso (XModLambdaN (N.functor.obj Y) (q - k)) k (s, t) t).symm
          ((S.lowerIso (XModLambdaN (N.functor.obj Y) (q - k)) k (s, t) t)
            (P.finiteTarget q k hkq s t z)))) = _ at he
  erw [LinearEquiv.symm_apply_apply] at he
  rw [← J.target_tower] at he
  calc
    _ ↔ R.finiteWindow Y q (by omega) (s, t) (t - k)
        (by constructor <;> simp <;> omega)
        (((F.functor.map (P.targetTower.lambdaInclusion k q hkq)).eInftyMap
          (s, t, t - k)).hom (P.finiteTarget q k hkq s t z)) = 0 :=
      (LinearEquiv.map_eq_zero_iff _).symm
    _ ↔ _ := by rw [he]; exact quotientMap_finiteTopClass_eq_zero H Y q k hkq (s, t) z

/-- The untruncated target kernel is the same boundary-cutoff calculation. -/
theorem infiniteLambdaTarget_eq_zero_iff (k : ℕ) (s t : ℤ)
    (z : permanentCycles H Y (s, t)) :
    ((F.functor.map (lambdaPow k (N.functor.obj Y))).eInftyMap
      (s, t, t - k)).hom (P.infiniteTarget k s t z) = 0 ↔
        z.val ∈ boundaries H Y (1 + k) (s, t) := by
  let a := S.lowerIso (N.functor.obj Y) k (s, t) t (P.infiniteTarget k s t z)
  have he := K.lambda_nu Y k (s, t) t le_rfl a
  erw [show R.nuWindow Y (s, t) t le_rfl a = permanentTopClass H Y (s, t) z
    from J.infinite k s t z] at he
  change R.nuWindow Y (s, t) (t - k) (by omega)
      (((F.functor.map (lambdaPow k (N.functor.obj Y))).eInftyMap (s, t, t - k)).hom
        ((S.lowerIso (N.functor.obj Y) k (s, t) t).symm
          ((S.lowerIso (N.functor.obj Y) k (s, t) t) (P.infiniteTarget k s t z)))) = _ at he
  erw [LinearEquiv.symm_apply_apply] at he
  calc
    _ ↔ R.nuWindow Y (s, t) (t - k) (by omega)
        (((F.functor.map (lambdaPow k (N.functor.obj Y))).eInftyMap
          (s, t, t - k)).hom (P.infiniteTarget k s t z)) = 0 :=
      (LinearEquiv.map_eq_zero_iff _).symm
    _ ↔ _ := by rw [he]; exact permanentQuotientMap_topClass_eq_zero H Y k (s, t) z

/-- The finite boundary-kernel field is now a consequence of representative
compatibility and the actual λ E∞ formula. -/
theorem finitePageExtensionBoundaryKernel {r : ℕ} {n s t : ℤ}
    {x : Ambient H X (s, t)} {y : Ambient H Y (s + n, t + n)}
    (W : FiniteExtensionWitness P r n s t x y) : W.ClassicalBoundaryKernel := by
  unfold FiniteExtensionWitness.ClassicalBoundaryKernel
  ext z
  change P.finiteTargetMap (r - 1) _ n s t _ _ z = 0 ↔
    z.val ∈ boundaries H Y (1 + n - normalizedExponent H f) (s + n, t + n)
  rw [P.finiteTargetMap_eq_zero_iff,
    finiteLambdaTarget_eq_zero_iff P R S T K J]
  have hk : (P.lambdaExponent n : ℤ) = n - normalizedExponent H f :=
    Int.toNat_of_nonneg (sub_nonneg.mpr W.exponent_le_length)
  rw [show 1 + (P.lambdaExponent n : ℤ) = 1 + n - normalizedExponent H f by omega]

theorem infinitePageExtensionBoundaryKernel {n s t : ℤ}
    {x : Ambient H X (s, t)} {y : Ambient H Y (s + n, t + n)}
    (W : InfiniteExtensionWitness P n s t x y) : W.ClassicalBoundaryKernel := by
  unfold InfiniteExtensionWitness.ClassicalBoundaryKernel
  ext z
  change P.infiniteTargetMap n s t _ z = 0 ↔
    z.val ∈ boundaries H Y (1 + n - normalizedExponent H f) (s + n, t + n)
  rw [P.infiniteTargetMap_eq_zero_iff,
    infiniteLambdaTarget_eq_zero_iff P R S T K J]
  have hk : (P.lambdaExponent n : ℤ) = n - normalizedExponent H f :=
    Int.toNat_of_nonneg (sub_nonneg.mpr W.exponent_le_length)
  rw [show 1 + (P.lambdaExponent n : ℤ) = 1 + n - normalizedExponent H f by omega]

end KIP126.Def.Comparison.StageInterfaces
