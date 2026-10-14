module

public import KIP126.Def.Algebra.SimplicialModule.Principal.Realization.Proofs
public import KIP126.Def.Topology.SimplicialRealization.Pullback.StandardSimplex.Naturality

@[expose] public section

namespace KIP126.Core.SimplicialModule
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open KIP126.Topology.SimplicialRealization
open scoped MonoidalCategory
universe u
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false

/-- Restricting an actual lift gives a lift of the restricted simplex. -/
theorem principalSimplex_restrict_lift
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) (b : B.obj (op ⦋n⦌)) (z : A.obj (op ⦋n⦌))
    (hz : (p.app (op ⦋n⦌)).hom z = b) :
    (p.app (op ⦋m⦌)).hom ((A.map φ.op).hom z) = (B.map φ.op).hom b :=
  (ConcreteCategory.congr_hom (p.naturality φ.op) z).trans (congrArg (B.map φ.op).hom hz)

/-- The actual continuous simplex trivializations commute with every
simplicial restriction, using the restricted lift and the same fiber coordinate. -/
theorem principalRealizationHomeomorph_natural_simplex
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) (b : B.obj (op ⦋n⦌)) (z : A.obj (op ⦋n⦌))
    (hz : (p.app (op ⦋n⦌)).hom z = b)
    (x : |kernel p ⋙ forget (ModuleCat R)|) (t : |(Δ[m] : SSet.{u})|) :
    (principalRealizationHomeomorph p b z hz (x,SSet.toTop.map (SSet.stdSimplex.map φ) t)).val.1 =
      (principalRealizationHomeomorph p ((B.map φ.op).hom b) ((A.map φ.op).hom z)
        (principalSimplex_restrict_lift p φ b z hz) (x,t)).val.1 := by
  rw [principalRealizationHomeomorph_fst,principalRealizationHomeomorph_fst,
    realizationStandardSimplexProductHomeomorph_symm_natural]
  have h := congrArg SSet.toTop.map (principalSimplexMap_natural_simplex p φ z)
  rw [Functor.map_comp] at h
  exact ConcreteCategory.congr_hom h _


end KIP126.Core.SimplicialModule
