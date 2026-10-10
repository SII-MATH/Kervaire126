import KIP126.Def.Synthetic.Completion.Data
import KIP126.Def.Synthetic.Sphere.Data
import KIP126.Def.StableHomotopy.TowerSpectralSequence.Sequence.Data

/-!
# The actual residual λ tower and its represented spectral sequences

The tower is extended constantly at all nonpositive indices from its actual
zeroth object `biShift (0,0) A`.  Its negative tail is not replaced by positive
weight shifts of `A`.  At each fixed weight the first page and differential
come from the specified cofiber layers of that tower.
-/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory
open KIP126.StableHomotopy KIP126.Synthetic.Context

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

/-- The actual residual λ sequence, extended constantly through stage zero. -/
noncomputable def lambdaTower (A : Syn) : DescendingTower Syn :=
  (lambdaResidualSequence A).toDescendingTower

/-- The specified comparison from a shifted weight sphere to the bigraded
sphere.  In particular the representing objects are compared by this actual
isomorphism, rather than identified by definitional equality. -/
noncomputable def representedSphereIso (n w : ℤ) :
    (Smn (Syn := Syn) 0 w)⟦n⟧ ≅ Smn n w :=
  (SyntheticCategory.biShift_compat n).symm.app (Smn 0 w) ≪≫
    (SyntheticCategory.biShift_comp (0, w) (n, 0)).app S_0_0 ≪≫
      eqToIso (by simp only [Smn, Prod.mk_add_mk, zero_add, add_zero])

/-- The induced additive comparison with actual bigraded homotopy groups. -/
noncomputable def representedHomEquiv (n w : ℤ) (Y : Syn) :
    ShiftedHom (Smn 0 w) n Y ≃+ BiHom n w Y where
  toFun f := (representedSphereIso n w).inv ≫ f
  invFun f := (representedSphereIso n w).hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp only [Preadditive.comp_add]

variable [HasFunctorialCofiber (C := Syn)]

/-- The intrinsic `E₁`-based sequence at one fixed weight.  Its bidegree is
`(tower index, represented stem)` and its differential has degree `(q,-1)`
on raw page `q`.  No convergence or completeness hypothesis is needed. -/
noncomputable def weightwiseSequence (A : Syn) (w : ℤ) :
    KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) (ℤ × ℤ) :=
  TowerSpectralSequence.sequence (lambdaTower A) (Smn 0 w)

end KIP126.Synthetic.Bockstein
