import KIP126.Def.Synthetic.Bockstein.Maps.Data
import KIP126.Def.Synthetic.QuotientMap.Proofs

/-! Local triangle and naturality properties of the prescribed Bockstein
arrow. No page-differential or lift-independence claim is made here. -/

namespace KIP126.Synthetic.Bockstein

open CategoryTheory CategoryTheory.Limits KIP126.StableHomotopy Context

universe u v

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  [HasFunctorialCofiber (C := Syn)]

/-- Classes coming from the unquotiented object have zero Bockstein. -/
theorem incl_beta (A : Syn) (q : ℕ) :
    XModLambdaN.incl A q ≫ beta A q = 0 := by
  rw [beta, ← Category.assoc, XModLambdaN.incl_comp_proj, zero_comp]

/-- Naturality uses the actual cofiber maps of the same λ-power squares. -/
theorem beta_naturality {A B : Syn} (f : A ⟶ B) (q : ℕ) :
    XModLambdaN.map f q ≫ beta B q =
      beta A q ≫ (shiftFunctor Syn (1 : ℤ)).map
        ((SyntheticCategory.biShift (0, -(q : ℤ))).map (XModLambdaN.map f 1)) := by
  unfold beta
  rw [← Category.assoc, XModLambdaN.proj_naturality, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, XModLambdaN.incl_naturality,
    Functor.map_comp, Functor.map_comp, Category.assoc]

end KIP126.Synthetic.Bockstein
