module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Map.Equivalence.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- Iterating the actual truncation functors with a smaller second cutoff
is naturally isomorphic to that smaller truncation. Its inverse is the
smaller truncation of the original larger-cutoff unit. -/
noncomputable def sourcePostnikovIterationIso (m n : ℤ) (h : n ≤ m) :
    sourcePostnikovFunctor m ⋙ sourcePostnikovFunctor n ≅ sourcePostnikovFunctor n := by
  exact (NatIso.ofComponents
    (fun (X : SourceCategory.{0}) => by
      letI := sourcePostnikovMap_unit_isIso X m n h
      exact asIso (sourcePostnikovMap n (sourcePostnikovUnit X m)))
    (fun f => by
      change sourcePostnikovMap n f ≫ sourcePostnikovMap n (sourcePostnikovUnit _ m) =
        sourcePostnikovMap n (sourcePostnikovUnit _ m) ≫
          sourcePostnikovMap n (sourcePostnikovMap m f)
      rw [← sourcePostnikovMap_comp, ← sourcePostnikovMap_comp,
        sourcePostnikovUnit_naturality])).symm

end KIP126.StableHomotopy.Implementation

end

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

/-- The inverse comparison is precisely the image of the original unit. -/
@[simp] theorem sourcePostnikovIterationIso_inv_app (X : SourceCategory.{0})
    (m n : ℤ) (h : n ≤ m) :
    (sourcePostnikovIterationIso m n h).inv.app X =
      sourcePostnikovMap n (sourcePostnikovUnit X m) := rfl

/-- The iteration comparison carries the original unit of the iterated
object to the previously constructed cutoff restriction. -/
@[reassoc (attr := simp)]
theorem sourcePostnikovUnit_iterationIso_hom (X : SourceCategory.{0})
    (m n : ℤ) (h : n ≤ m) :
    sourcePostnikovUnit (sourcePostnikovTruncation X m) n ≫
      (sourcePostnikovIterationIso m n h).hom.app X =
        sourcePostnikovRestriction X m n h := by
  apply (sourcePostnikovUnit_precomp_bijective X m (sourcePostnikovTruncation X n)
    (fun d hd => sourcePostnikovTruncation_homotopy_subsingleton X n d (h.trans hd))).injective
  dsimp only
  rw [← Category.assoc, ← sourcePostnikovUnit_naturality n (sourcePostnikovUnit X m), Category.assoc,
    sourcePostnikovUnit_restriction]
  change sourcePostnikovUnit X n ≫ (sourcePostnikovIterationIso m n h).inv.app X ≫
    (sourcePostnikovIterationIso m n h).hom.app X = sourcePostnikovUnit X n
  rw [Iso.inv_hom_id_app]
  exact Category.comp_id (sourcePostnikovUnit X n)

/-- At equal cutoffs, the natural iteration comparison is the inverse
of the same actual unit on the already truncated object. -/
@[reassoc (attr := simp)]
theorem sourcePostnikovUnit_idempotence (X : SourceCategory.{0}) (n : ℤ) :
    sourcePostnikovUnit (sourcePostnikovTruncation X n) n ≫
      (sourcePostnikovIterationIso n n le_rfl).hom.app X = 𝟙 _ := by
  rw [sourcePostnikovUnit_iterationIso_hom, sourcePostnikovRestriction_refl]

end KIP126.StableHomotopy.Implementation

end
