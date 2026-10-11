module

public import KIP126.Def.StageInput.StandardSphere.Algebra.Components.Proofs

@[expose] public section


/-! The global direct-sum algebra of the fixed actual sphere E₂ page.
Its ring structure uses the explicitly named structural obligations in
`Components.Proofs`; it has no native presentation parameter or cutoff. -/

namespace KIP126.Classical.Adams.Sphere.Internal

open KIP126.Core.Algebra
noncomputable section

attribute [local irreducible] ActualE2At actualE2AtModule actualE2Product

instance actualE2GradedCommRing : DirectSum.GCommRing ActualE2At where
  mul := fun {p q} x y => actualE2Product p q x y
  one := actualE2Unit
  mul_zero := fun x => map_zero (actualE2Product _ _ x)
  zero_mul := fun x => by simp
  mul_add := fun x y z => map_add (actualE2Product _ _ x) y z
  add_mul := fun x y z => by simp
  one_mul := actualE2_one_mul
  mul_one := actualE2_mul_one
  mul_assoc := actualE2_mul_assoc
  mul_comm := actualE2_mul_comm
  natCast n := n • actualE2Unit
  natCast_zero := zero_nsmul _
  natCast_succ n := by simp [add_nsmul]
  intCast n := n • actualE2Unit
  intCast_ofNat n := by simp
  intCast_negSucc_ofNat n := negSucc_zsmul actualE2Unit n

instance actualE2GradedAlgebra : DirectSum.GAlgebra F2 ActualE2At where
  toFun :=
    { toFun := fun r => r • actualE2Unit
      map_zero' := zero_smul _ _
      map_add' := fun r s => add_smul r s _ }
  map_one := one_smul _ _
  map_mul r s := by
    change (r * s) • (1 : GradedMonoid ActualE2At) =
      (r • (1 : GradedMonoid ActualE2At)) * (s • (1 : GradedMonoid ActualE2At))
    rw [actualE2_smul_mul, actualE2_one_mul, mul_smul]
  commutes r a := actualE2_mul_comm _ a
  smul_def r a := by
    change r • a = (r • (1 : GradedMonoid ActualE2At)) * a
    rw [actualE2_smul_mul, actualE2_one_mul]

/-- All nonnegative homogeneous pieces of the fixed actual sphere E₂,
with finite support and the fixed multiplication. No product is truncated. -/
abbrev ActualE2Total := DirectSum (ℕ × ℕ) ActualE2At

/-- The canonical linear inclusion of one actual page component. -/
def embed (p : ℕ × ℕ) : ActualE2At p →ₗ[F2] ActualE2Total :=
  DirectSum.lof F2 (ℕ × ℕ) ActualE2At p

end
end KIP126.Classical.Adams.Sphere.Internal
