module

public import KIP126.Def.Topology.SimplicialRealization.Pullback.StandardSimplex.Proofs

@[expose] public section

namespace KIP126.Topology.SimplicialRealization
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false

/-- The actual product homeomorphisms commute strictly with simplex operators. -/
theorem realizationStandardSimplexProductHomeomorph_natural (X : SSet.{u})
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) (x : |X ⊗ Δ[m]|) :
    realizationStandardSimplexProductHomeomorph X n
      (SSet.toTop.map (𝟙 X ⊗ₘ SSet.stdSimplex.map φ) x) =
      ((realizationStandardSimplexProductHomeomorph X m x).1,
        SSet.toTop.map (SSet.stdSimplex.map φ) (realizationStandardSimplexProductHomeomorph X m x).2) := by
  apply Prod.ext
  · change SSet.toTop.map (CartesianMonoidalCategory.fst X Δ[n])
      (SSet.toTop.map (𝟙 X ⊗ₘ SSet.stdSimplex.map φ) x) =
        SSet.toTop.map (CartesianMonoidalCategory.fst X Δ[m]) x
    have h : (𝟙 X ⊗ₘ SSet.stdSimplex.map φ) ≫ CartesianMonoidalCategory.fst X Δ[n] =
        CartesianMonoidalCategory.fst X Δ[m] := by simp
    have h' := congrArg SSet.toTop.map h
    rw [Functor.map_comp] at h'
    exact ConcreteCategory.congr_hom h' x
  · change SSet.toTop.map (CartesianMonoidalCategory.snd X Δ[n])
      (SSet.toTop.map (𝟙 X ⊗ₘ SSet.stdSimplex.map φ) x) =
        SSet.toTop.map (SSet.stdSimplex.map φ) (SSet.toTop.map (CartesianMonoidalCategory.snd X Δ[m]) x)
    have h : (𝟙 X ⊗ₘ SSet.stdSimplex.map φ) ≫ CartesianMonoidalCategory.snd X Δ[n] =
        CartesianMonoidalCategory.snd X Δ[m] ≫ SSet.stdSimplex.map φ := by simp
    have h' := congrArg SSet.toTop.map h
    simp only [Functor.map_comp] at h'
    exact ConcreteCategory.congr_hom h' x

/-- Strict naturality also holds for the inverses of the actual product homeomorphisms. -/
theorem realizationStandardSimplexProductHomeomorph_symm_natural (X : SSet.{u})
    {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) (x : |X|) (t : |(Δ[m] : SSet.{u})|) :
    (realizationStandardSimplexProductHomeomorph X n).symm
      (x,SSet.toTop.map (SSet.stdSimplex.map φ) t) =
      SSet.toTop.map (𝟙 X ⊗ₘ SSet.stdSimplex.map φ)
        ((realizationStandardSimplexProductHomeomorph X m).symm (x,t)) := by
  apply (realizationStandardSimplexProductHomeomorph X n).injective
  rw [Homeomorph.apply_symm_apply,realizationStandardSimplexProductHomeomorph_natural,
    Homeomorph.apply_symm_apply]


end KIP126.Topology.SimplicialRealization
