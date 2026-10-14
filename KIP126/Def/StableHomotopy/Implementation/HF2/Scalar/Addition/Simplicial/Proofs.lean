module

public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Addition.Simplicial.Data
public import KIP126.Def.StableHomotopy.Implementation.HF2.Scalar.Product.Level.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.HF2Scalar
open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory Opposite Simplicial
open HF2Bond
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

theorem additionSet_cone (n : ℕ) :
    pairConeMap n ≫ Functor.whiskerLeft coneFunctor.op (additionSet (n+1)) =
      additionSet n ≫ coefficientToLoopSet n ≫ loopSetInclusion n := by
  ext a x
  exact (((coefficientToLoop n ≫ loopInclusion n).app a).hom.map_add x.1 x.2).symm

theorem diagonalSet_cone (n : ℕ) :
    (coefficientToLoopSet n ≫ loopSetInclusion n) ≫
        Functor.whiskerLeft coneFunctor.op (diagonalSet (n+1)) =
      diagonalSet n ≫ pairConeMap n := by
  ext a x
  rfl

theorem inlSet_cone (n : ℕ) :
    (coefficientToLoopSet n ≫ loopSetInclusion n) ≫
        Functor.whiskerLeft coneFunctor.op (inlSet (n+1)) =
      inlSet n ≫ pairConeMap n := by
  ext a x
  exact Prod.ext rfl (((coefficientToLoop n ≫ loopInclusion n).app a).hom.map_zero).symm

theorem inrSet_cone (n : ℕ) :
    (coefficientToLoopSet n ≫ loopSetInclusion n) ≫
        Functor.whiskerLeft coneFunctor.op (inrSet (n+1)) =
      inrSet n ≫ pairConeMap n := by
  ext a x
  exact Prod.ext (((coefficientToLoop n ≫ loopInclusion n).app a).hom.map_zero).symm rfl

/-- A commuting square of actual cone maps gives a strict square of
their continuous realized bonds. -/
theorem coneSquare_realize {A B C D : SSet.{0}}
    (a : A ⟶ decalage C) (b : B ⟶ decalage D) (f : A ⟶ B) (g : C ⟶ D)
    (h : a ≫ Functor.whiskerLeft coneFunctor.op g = f ≫ b)
    (x : |A|) (t : I) :
    SSet.toTop.map g (coneEvaluation C (SSet.toTop.map a x,t)) =
      coneEvaluation D (SSet.toTop.map b (SSet.toTop.map f x),t) := by
  rw [coneEvaluation_natural]
  have hh := ConcreteCategory.congr_hom (congrArg SSet.toTop.map h) x
  simp only [Functor.map_comp,TopCat.comp_app] at hh
  exact congrArg (fun y => coneEvaluation D (y,t)) hh

@[simp] theorem inlSet_additionSet (n : ℕ) : inlSet n ≫ additionSet n = 𝟙 _ := by
  ext a x
  change (hf2SimplicialModule n).obj a at x
  exact add_zero (x : (hf2SimplicialModule n).obj a)

@[simp] theorem inrSet_additionSet (n : ℕ) : inrSet n ≫ additionSet n = 𝟙 _ := by
  ext a x
  change (hf2SimplicialModule n).obj a at x
  exact zero_add (x : (hf2SimplicialModule n).obj a)

/-- Characteristic two is a literal identity of the simplicial maps,
before passing to homotopy groups or localization. -/
theorem diagonalSet_additionSet (n : ℕ) : diagonalSet n ≫ additionSet n = zeroSet n := by
  ext a x
  change (hf2SimplicialModule n).obj a at x
  change (x : (hf2SimplicialModule n).obj a) + x = 0
  calc
    x+x = ((1 : ZMod 2)+1) • x := by rw [add_smul,one_smul]
    _ = 0 := by
      have hz : (1 : ZMod 2)+1 = 0 := by decide
      rw [hz,zero_smul]

theorem realization_zeroSet (n : ℕ) (x : |hf2SimplicialSet n|) :
    SSet.toTop.map (zeroSet n) x = (hf2RealizationLevel n).point := by
  have h : SSet.toTop.map (zeroSet n) = TopCat.const (hf2RealizationLevel n).point := by
    apply realization_hom_ext
    intro a z u
    rw [realizeSimplex_map]
    exact realizeSimplex_zero _ _ _
  exact ConcreteCategory.congr_hom h x

end KIP126.StableHomotopy.Implementation.HF2Scalar
