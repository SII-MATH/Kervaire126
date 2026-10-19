module

public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.Homotopy.Basic

@[expose] public section

namespace KIP126.Topology

open CategoryTheory CategoryTheory.Limits
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false

/-- Homotopies on the two pieces of an actual topological coproduct
glue continuously, retaining their exact values on both pieces. -/
theorem exists_homotopy_of_topological_coproduct
    {A B P Y : TopCat.{u}} {a : A ⟶ P} {b : B ⟶ P}
    (h : IsColimit (BinaryCofan.mk a b)) (F G : C(P,Y))
    (HA : (F.comp a.hom).Homotopy (G.comp a.hom))
    (HB : (F.comp b.hom).Homotopy (G.comp b.hom)) :
    ∃ H : F.Homotopy G,
      (∀ (t : I) (x : A), H (t,a x) = HA (t,x)) ∧
      (∀ (t : I) (x : B), H (t,b x) = HB (t,x)) := by
  let cA : A ⟶ TopCat.of C(I,Y) :=
    TopCat.ofHom (HA.toContinuousMap.comp ContinuousMap.prodSwap).curry
  let cB : B ⟶ TopCat.of C(I,Y) :=
    TopCat.ofHom (HB.toContinuousMap.comp ContinuousMap.prodSwap).curry
  let d := BinaryCofan.IsColimit.desc h cA cB
  let E : C(P × I,Y) := d.hom.uncurry
  have hA (t : I) (x : A) : E (a x,t) = HA (t,x) :=
    congrArg (fun p : C(I,Y) => p t)
      (ConcreteCategory.congr_hom (BinaryCofan.IsColimit.inl_desc h cA cB) x)
  have hB (t : I) (x : B) : E (b x,t) = HB (t,x) :=
    congrArg (fun p : C(I,Y) => p t)
      (ConcreteCategory.congr_hom (BinaryCofan.IsColimit.inr_desc h cA cB) x)
  have h0 : TopCat.ofHom (Y := Y)
      (E.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 0))) =
      TopCat.ofHom (X := P) (Y := Y) F := by
    apply BinaryCofan.IsColimit.hom_ext h
    · ext x
      exact (hA 0 x).trans (HA.apply_zero x)
    · ext x
      exact (hB 0 x).trans (HB.apply_zero x)
  have h1 : TopCat.ofHom (Y := Y)
      (E.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ 1))) =
      TopCat.ofHom (X := P) (Y := Y) G := by
    apply BinaryCofan.IsColimit.hom_ext h
    · ext x
      exact (hA 1 x).trans (HA.apply_one x)
    · ext x
      exact (hB 1 x).trans (HB.apply_one x)
  exact ⟨{
    toFun := fun z => E (z.2,z.1)
    continuous_toFun := E.continuous.comp (continuous_snd.prodMk continuous_fst)
    map_zero_left := ConcreteCategory.congr_hom h0
    map_one_left := ConcreteCategory.congr_hom h1 },hA,hB⟩

end KIP126.Topology
