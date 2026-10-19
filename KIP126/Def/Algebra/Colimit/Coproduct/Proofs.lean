module

public import KIP126.Def.Algebra.Colimit.Coproduct.Data
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

@[expose] public section

namespace KIP126.Foundation

open CategoryTheory CategoryTheory.Limits
universe u v w
set_option backward.isDefEq.respectTransparency false

/-- The algebraic direct sum satisfies the actual coproduct universal property. -/
noncomputable def additiveDirectSumCofan_isColimit {J : Type u}
    (A : J → AddCommGrpCat.{u}) : IsColimit (additiveDirectSumCofan A) := by
  classical
  refine Cofan.IsColimit.mk _ (fun c => AddCommGrpCat.ofHom
    (DirectSum.toAddMonoid (γ := c.pt) (fun j => (c.inj j).hom))) ?_ ?_
  · intro c j
    apply AddCommGrpCat.ext
    intro x
    change DirectSum.toAddMonoid (γ := c.pt) (fun j => (c.inj j).hom)
      (DirectSum.of (fun j => A j) j x) = _
    rw [DirectSum.toAddMonoid_of]
  · intro c m hm
    apply AddCommGrpCat.ext
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of j x =>
      change m (DirectSum.of (fun j => A j) j x) =
        DirectSum.toAddMonoid (γ := c.pt) (fun j => (c.inj j).hom)
          (DirectSum.of (fun j => A j) j x)
      rw [DirectSum.toAddMonoid_of]
      exact ConcreteCategory.congr_hom (hm j) x
    | add x y hx hy => simp only [map_add, hx, hy]

/-- In a finite coproduct of abelian groups every element is the sum of
its actual components. -/
theorem finiteCofan_exists_sum {J : Type*} [Fintype J]
    {A : J → AddCommGrpCat.{u}} (c : Cofan A) (hc : IsColimit c) (a : c.pt) :
    ∃ x : ∀ j, A j, ∑ j, c.inj j (x j) = a := by
  let b := Bicone.ofColimitCocone hc
  refine ⟨fun j => b.π j a,?_⟩
  have h := IsBilimit.total (biconeIsBilimitOfColimitCoconeOfIsColimit hc)
  have hsum (s : Finset J) : (∑ j ∈ s, b.π j ≫ b.ι j) a =
      ∑ j ∈ s, c.inj j (b.π j a) := by
    classical
    induction s using Finset.induction with
    | empty => rfl
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj, AddCommGrpCat.hom_add_apply, ih]
      rfl
  have ha := ConcreteCategory.congr_hom h a
  change (∑ j, b.π j ≫ b.ι j) a = a at ha
  rw [hsum] at ha
  exact ha

/-- An additive functor to abelian groups preserves a given small coproduct
when every element of its image is supported on an actual finite subcoproduct. -/
theorem preservesCoproduct_of_finite_support
    {C : Type v} [Category.{w} C] [Preadditive C] [HasCoproducts.{u} C]
    (F : C ⥤ AddCommGrpCat.{u}) [F.Additive] {J : Type u} (X : J → C)
    (hfin : ∀ a : F.obj (∐ X), ∃ (s : Finset J)
      (b : F.obj (∐ fun j : (s : Set J) => X j.val)),
      F.map (Sigma.desc (fun j : (s : Set J) => Sigma.ι X j.val)) b = a) :
    PreservesColimit (Discrete.functor X) F := by
  classical
  let A (j : J) := F.obj (X j)
  let D := additiveDirectSumCofan A
  let σ : D.pt ⟶ F.obj (∐ X) := AddCommGrpCat.ofHom
    (DirectSum.toAddMonoid (fun j => (F.map (Sigma.ι X j)).hom))
  have hσ (j : J) (x : A j) : σ (DirectSum.of (fun j => A j) j x) = F.map (Sigma.ι X j) x :=
    DirectSum.toAddMonoid_of _ _ _
  let π (j : J) : ∐ X ⟶ X j :=
    Sigma.desc (fun k => if h : k = j then eqToHom (congrArg X h) else 0)
  have hπ (j : J) (x : DirectSum J (fun j => A j)) : F.map (π j) (σ x) = x j := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of k x =>
      rw [hσ]
      change (F.map (Sigma.ι X k) ≫ F.map (π j)) x = _
      rw [← F.map_comp]
      simp only [π, Sigma.ι_desc]
      by_cases h : k = j
      · subst k
        simp
      · simp [h, DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
    | add x y hx hy => simp only [map_add, hx, hy, DirectSum.add_apply]
  have hi : Function.Injective σ := by
    intro x y h
    apply DFinsupp.ext
    intro j
    rw [← hπ j x, ← hπ j y, h]
  have hs : Function.Surjective σ := by
    intro a
    obtain ⟨s,b,hb⟩ := hfin a
    let Y (j : (s : Set J)) := X j.val
    let c : Cofan (fun j : (s : Set J) => F.obj (Y j)) :=
      Cofan.mk (F.obj (∐ Y)) (fun j => F.map (Sigma.ι Y j))
    have hc : IsColimit c := isColimitOfHasCoproductOfPreservesColimit F Y
    obtain ⟨x,hx⟩ := finiteCofan_exists_sum c hc b
    refine ⟨∑ j : (s : Set J), DirectSum.of (fun j => A j) j.val (x j),?_⟩
    rw [map_sum]
    simp only [hσ]
    rw [← hb, ← hx, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change F.map (Sigma.ι X j.val) (x j) =
      (F.map (Sigma.ι Y j) ≫ F.map (Sigma.desc (fun j : (s : Set J) => Sigma.ι X j.val))) (x j)
    rw [← F.map_comp, Sigma.ι_desc]
  letI : IsIso σ := (ConcreteCategory.isIso_iff_bijective σ).mpr ⟨hi,hs⟩
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct X)
  refine (isColimitMapCoconeCofanMkEquiv F X (Sigma.ι X)).symm ?_
  apply IsColimit.ofIsoColimit (additiveDirectSumCofan_isColimit A)
  refine Cocone.ext (asIso σ) ?_
  rintro ⟨j⟩
  apply AddCommGrpCat.ext
  intro x
  exact hσ j x

end KIP126.Foundation
