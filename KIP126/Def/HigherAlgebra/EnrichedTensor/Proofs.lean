import KIP126.Def.HigherAlgebra.EnrichedTensor.Predicates

/-! Property statements for the actual enriched finite tensor operations.
The proofs remain separate from the data; they do not select a model. -/

namespace KIP126.HigherAlgebra.EnrichedTensor

open CategoryTheory MonoidalCategory Operad

universe u v

variable {M : Type u} [Category.{v} M]
  [EnrichedOrdinaryCategory TopCat.{v} M]

theorem arrow_point {X Y : M} (f : X ⟶ Y) : arrow (point f) = f := by
  sorry

theorem point_arrow {X Y : M} (f : MappingSpace X Y) : point (arrow f) = f := by
  sorry

variable [MonoidalCategory M]

/-- The coloured finite tensor equations imply every endomorphism operad law
for the operations computed from those tensors. -/
theorem endomorphismLaws (P : Presentation M) (hP : TensorLaws P) (X : M) :
    EndomorphismLaws P X := by
  sorry

/-- The point-set formula for substitution uses the same ordinary maps and
the same flattening isomorphism as the enriched continuous construction. -/
theorem compose_arrow (P : Presentation M) (X : M)
    (I : FintypeCat.{0}) (J : I → FintypeCat.{0})
    (f : P.Op X I) (g : (i : I) → P.Op X (J i)) :
    arrow (P.compose X I J (f, g)) =
      (P.flatten I J (fun _ _ => X)).hom ≫
        P.map I (fun i => arrow (g i)) ≫ arrow f := by
  sorry

end KIP126.HigherAlgebra.EnrichedTensor
