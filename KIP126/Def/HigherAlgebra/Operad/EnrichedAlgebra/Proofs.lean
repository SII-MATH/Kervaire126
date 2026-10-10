import KIP126.Def.HigherAlgebra.Operad.EnrichedAlgebra.Data

/-! Properties needed to form the category and its unit-forgetting functor.
Proofs may remain unfinished during the interface-definition milestone. -/

namespace KIP126.HigherAlgebra.Operad.EnrichedAlgebra

open CategoryTheory MonoidalCategory EnrichedTensor

universe u v w

variable {M : Type u} [Category.{v} M] [MonoidalCategory M]
  [EnrichedOrdinaryCategory TopCat.{v} M]
  {P : Presentation M} {hP : TensorLaws P} {O : TopologicalOperad.{w}}

theorem identity_commutes (A : EnrichedAlgebra P hP O)
    (I : FintypeCat.{0}) (x : O.Op I) :
    A.operation I x ≫ 𝟙 A.carrier =
      P.map I (fun _ => 𝟙 A.carrier) ≫ A.operation I x := by
  sorry

theorem composition_commutes {A B D : EnrichedAlgebra P hP O}
    (f : Hom A B) (g : Hom B D) (I : FintypeCat.{0}) (x : O.Op I) :
    A.operation I x ≫ (f.hom ≫ g.hom) =
      P.map I (fun _ => f.hom ≫ g.hom) ≫ D.operation I x := by
  sorry

/-- The nullary case of the algebra-morphism equation, transported through
the actual empty tensor comparison, fixes the same unit arrow. -/
theorem unit_naturality (o : O.Op empty) {A B : EnrichedAlgebra P hP O}
    (f : Hom A B) : unit o A ≫ f.hom = unit o B := by
  sorry

end KIP126.HigherAlgebra.Operad.EnrichedAlgebra
