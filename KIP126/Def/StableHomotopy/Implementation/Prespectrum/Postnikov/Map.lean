module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Postnikov.Universal.Proofs

@[expose] public section

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

/-- The unique induced map between the same constructed truncation objects,
chosen from their proved universal property. -/
noncomputable def sourcePostnikovMap (n : ℤ) {X Y : SourceCategory.{0}} (f : X ⟶ Y) :
    sourcePostnikovTruncation X n ⟶ sourcePostnikovTruncation Y n :=
  ((sourcePostnikovUnit_precomp_bijective X n (sourcePostnikovTruncation Y n)
    (sourcePostnikovTruncation_homotopy_subsingleton Y n)).surjective
      (f ≫ sourcePostnikovUnit Y n)).choose

end KIP126.StableHomotopy.Implementation

end

section

namespace KIP126.StableHomotopy.Implementation

open CategoryTheory

set_option backward.isDefEq.respectTransparency false

/-- The induced truncation map preserves the original specified units. -/
@[reassoc (attr := simp)]
theorem sourcePostnikovUnit_naturality (n : ℤ) {X Y : SourceCategory.{0}} (f : X ⟶ Y) :
    sourcePostnikovUnit X n ≫ sourcePostnikovMap n f = f ≫ sourcePostnikovUnit Y n :=
  ((sourcePostnikovUnit_precomp_bijective X n (sourcePostnikovTruncation Y n)
    (sourcePostnikovTruncation_homotopy_subsingleton Y n)).surjective
      (f ≫ sourcePostnikovUnit Y n)).choose_spec

/-- Uniqueness gives the identity law on the same truncation objects. -/
@[simp] theorem sourcePostnikovMap_id (n : ℤ) (X : SourceCategory.{0}) :
    sourcePostnikovMap n (𝟙 X) = 𝟙 (sourcePostnikovTruncation X n) := by
  apply (sourcePostnikovUnit_precomp_bijective X n (sourcePostnikovTruncation X n)
    (sourcePostnikovTruncation_homotopy_subsingleton X n)).injective
  dsimp only
  rw [sourcePostnikovUnit_naturality, Category.id_comp, Category.comp_id]

/-- Uniqueness gives genuine functorial composition, independently of the
nonfunctorial choices of the intermediate cofiber triangles. -/
@[simp] theorem sourcePostnikovMap_comp (n : ℤ) {X Y Z : SourceCategory.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    sourcePostnikovMap n (f ≫ g) = sourcePostnikovMap n f ≫ sourcePostnikovMap n g := by
  apply (sourcePostnikovUnit_precomp_bijective X n (sourcePostnikovTruncation Z n)
    (sourcePostnikovTruncation_homotopy_subsingleton Z n)).injective
  dsimp only
  simp only [sourcePostnikovUnit_naturality, sourcePostnikovUnit_naturality_assoc,
    Category.assoc]

/-- The actual induced truncation maps preserve the original addition. -/
theorem sourcePostnikovMap_add (n : ℤ) {X Y : SourceCategory.{0}} (f g : X ⟶ Y) :
    sourcePostnikovMap n (f+g) = sourcePostnikovMap n f + sourcePostnikovMap n g := by
  apply (sourcePostnikovUnit_precomp_bijective X n (sourcePostnikovTruncation Y n)
    (sourcePostnikovTruncation_homotopy_subsingleton Y n)).injective
  dsimp only
  simp only [sourcePostnikovUnit_naturality, Preadditive.comp_add, Preadditive.add_comp]

end KIP126.StableHomotopy.Implementation

end
