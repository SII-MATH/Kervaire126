import KIPBase.Synthetic.GeometricAdamsCofiber

/-!
# Object-level realization data for a synthetic Adams tower

`SynAdamsConvergenceData` identifies the abstract Adams abutment with actual
represented homotopy groups, but it does not construct objects representing
the stages of an Adams resolution.  This file records the additional,
model-dependent object-level realization needed by the geometric boundary
argument.

The interface is an explicit parameter: no global instance or axiom asserts
that an arbitrary `GeometricAdams.Input` is an Adams resolution.
-/

namespace KIPBase.Synthetic.GeometricAdams.Input

open CategoryTheory CategoryTheory.Limits

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]
    {X : Syn}

/-- Object-level geometric realization of the synthetic Adams resolution.

The field is the model-specific realization statement not contained in the
abstract spectral-sequence convergence package: a divided adjacent-layer
target detected by a geometric page differential is represented at the
corresponding stage, compatibly with one relative representative.  The
free-layer datum is kept as a parameter so different chosen identifications
of the associated graded are not silently conflated.

Constructing this structure for a concrete synthetic Adams tower is the only
remaining model-dependent input; all cofiber and capping consequences are
proved from it downstream. -/
structure SyntheticAdamsGeometricRealization
    (G : GeometricAdams.Input X) (R : G.FreeLayers) : Prop where
  dividedBoundary
      (s r : ℕ) (hr : 2 ≤ r) (m : ℤ)
      (x : G.PageGroup (Smn m (m + s)) s r (by omega))
      (y : Smn m (m + s) ⟶ (shiftFunctor Syn (1 : ℤ)).obj
        ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).obj
          (G.layer (s + r))))
      (hxy : G.pageObstruction (Smn m (m + s)) s r (by omega) x =
        QuotientAddGroup.mk
          (y ≫ (shiftFunctor Syn (1 : ℤ)).map
            (lambdaPow (r - 1) (G.layer (s + r))))) :
    ∃ (z : G.Representative (Smn m (m + s)) s r)
      (y' : Smn m (m + s) ⟶ (G.boundaryTarget (r - 1)).stage (s + r)),
      QuotientAddGroup.mk
        (⟨G.source (Smn m (m + s)) s r (by omega) z,
          ⟨z, rfl⟩⟩ : G.sourceCycles (Smn m (m + s)) s r (by omega)) = x ∧
      y' ≫ (shiftFunctor Syn (1 : ℤ)).map
          ((SyntheticCategory.biShift (0, -((r - 1 : ℕ) : ℤ))).map
            (syn_functorial_cofiber.cofibι
              (G.transition (s + r) (s + r + 1) (Nat.le_succ _)))) = y ∧
      z ≫ G.boundary s (s + r) (Nat.le_add_right s r) =
        y' ≫ (shiftFunctor Syn (1 : ℤ)).map
          (lambdaPow (r - 1) (G.stage (s + r)))

end KIPBase.Synthetic.GeometricAdams.Input
