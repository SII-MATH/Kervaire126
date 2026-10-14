module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.Map.Proofs
public import Mathlib.Algebra.FiveLemma

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory
universe u

/-- A strict commuting square whose two vertical maps are actual stable
equivalences induces an actual stable equivalence on path homotopy fibers. -/
theorem fiberMap_stableEquivalence {X Y X' Y' : Prespectrum.{u}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ g) (ha : stableEquivalences a) (hb : stableEquivalences b) :
    stableEquivalences (fiberMap f g a b h) := by
  intro d
  have hc (e : ℤ) :
      (stableHomotopyAddHom g e).comp (stableHomotopyAddHom a e) =
        (stableHomotopyAddHom b e).comp (stableHomotopyAddHom f e) := by
    ext x
    change (stableHomotopyFunctor e).map g ((stableHomotopyFunctor e).map a x) =
      (stableHomotopyFunctor e).map b ((stableHomotopyFunctor e).map f x)
    rw [← Functor.map_comp_apply,← Functor.map_comp_apply,← h]
  have hp :
      (stableHomotopyAddHom (fiberProjection g) d).comp
          (stableHomotopyAddHom (fiberMap f g a b h) d) =
        (stableHomotopyAddHom a d).comp (stableHomotopyAddHom (fiberProjection f) d) := by
    ext x
    change (stableHomotopyFunctor d).map (fiberProjection g)
      ((stableHomotopyFunctor d).map (fiberMap f g a b h) x) =
        (stableHomotopyFunctor d).map a ((stableHomotopyFunctor d).map (fiberProjection f) x)
    rw [← Functor.map_comp_apply,← Functor.map_comp_apply,fiberMap_projection]
  exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (stableHomotopyAddHom f (d+1)) (fiberBoundary f d)
    (stableHomotopyAddHom (fiberProjection f) d) (stableHomotopyAddHom f d)
    (stableHomotopyAddHom g (d+1)) (fiberBoundary g d)
    (stableHomotopyAddHom (fiberProjection g) d) (stableHomotopyAddHom g d)
    (stableHomotopyAddHom a (d+1)) (stableHomotopyAddHom b (d+1))
    (stableHomotopyAddHom (fiberMap f g a b h) d)
    (stableHomotopyAddHom a d) (stableHomotopyAddHom b d)
    (hc (d+1)) (by ext y; exact (fiberBoundary_natural f g a b h d y).symm)
    hp (hc d)
    (fiberBoundary_exact f d) (fiberBoundary_projection_exact f d) (fiberProjection_map_exact f d)
    (fiberBoundary_exact g d) (fiberBoundary_projection_exact g d) (fiberProjection_map_exact g d)
    (ha (d+1)).2 (hb (d+1)) (ha d) (hb d).1

end KIP126.StableHomotopy.Implementation.Prespectrum
