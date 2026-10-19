module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Restriction.Data
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Map

@[expose] public section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- Every restriction preserves the original truncation units exactly. -/
@[reassoc (attr := simp)]
theorem sourcePostnikovUnit_restriction (X : SourceCategory.{0}) (m n : ℤ) (h : n ≤ m) :
    sourcePostnikovUnit X m ≫ sourcePostnikovRestriction X m n h = sourcePostnikovUnit X n :=
  ((sourcePostnikovUnit_precomp_bijective X m (sourcePostnikovTruncation X n)
    (fun d hd => sourcePostnikovTruncation_homotopy_subsingleton X n d (h.trans hd))).surjective
      (sourcePostnikovUnit X n)).choose_spec

/-- Equal cutoffs give the actual identity restriction. -/
@[simp] theorem sourcePostnikovRestriction_refl (X : SourceCategory.{0}) (n : ℤ) :
    sourcePostnikovRestriction X n n le_rfl = 𝟙 _ := by
  apply (sourcePostnikovUnit_precomp_bijective X n (sourcePostnikovTruncation X n)
    (sourcePostnikovTruncation_homotopy_subsingleton X n)).injective
  dsimp only
  rw [sourcePostnikovUnit_restriction, Category.comp_id]

/-- Restriction between integer cutoffs composes coherently. -/
@[reassoc (attr := simp)]
theorem sourcePostnikovRestriction_trans (X : SourceCategory.{0}) (l m n : ℤ)
    (hml : m ≤ l) (hnm : n ≤ m) :
    sourcePostnikovRestriction X l m hml ≫ sourcePostnikovRestriction X m n hnm =
      sourcePostnikovRestriction X l n (hnm.trans hml) := by
  apply (sourcePostnikovUnit_precomp_bijective X l (sourcePostnikovTruncation X n)
    (fun d hd => sourcePostnikovTruncation_homotopy_subsingleton X n d
      ((hnm.trans hml).trans hd))).injective
  dsimp only
  rw [← Category.assoc, sourcePostnikovUnit_restriction,
    sourcePostnikovUnit_restriction, sourcePostnikovUnit_restriction]

/-- The integer-cutoff restrictions are natural in the original source object. -/
@[reassoc]
theorem sourcePostnikovRestriction_naturality {X Y : SourceCategory.{0}} (f : X ⟶ Y)
    (m n : ℤ) (h : n ≤ m) :
    sourcePostnikovMap m f ≫ sourcePostnikovRestriction Y m n h =
      sourcePostnikovRestriction X m n h ≫ sourcePostnikovMap n f := by
  apply (sourcePostnikovUnit_precomp_bijective X m (sourcePostnikovTruncation Y n)
    (fun d hd => sourcePostnikovTruncation_homotopy_subsingleton Y n d (h.trans hd))).injective
  dsimp only
  rw [← Category.assoc, sourcePostnikovUnit_naturality, Category.assoc,
    sourcePostnikovUnit_restriction, ← Category.assoc, sourcePostnikovUnit_restriction,
    sourcePostnikovUnit_naturality]

end KIP126.StableHomotopy.Implementation
