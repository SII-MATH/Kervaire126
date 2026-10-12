module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Coproduct.Subfamily.Data
public import KIP126.Def.Topology.Coproduct.Wedge.Subfamily.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace

open CategoryTheory CategoryTheory.Limits
universe u

@[simp] theorem wedgeι_subfamilyMap {J : Type u} (X : J → BasedSpace.{u})
    (s : Set J) (j : s) :
    wedgeι (fun j : s => X j.val) j ≫ wedgeSubfamilyMap X s = wedgeι X j.val := rfl

/-- The explicit finite-subfamily inclusion and the chosen coproduct
inclusion agree under the proved actual wedge comparison. -/
theorem wedgeCoproductIso_subfamily {J : Type u} (X : J → BasedSpace.{u}) (s : Set J) :
    (wedgeCoproductIso (fun j : s => X j.val)).hom ≫ coproductSubfamilyMap X s =
      wedgeSubfamilyMap X s ≫ (wedgeCoproductIso X).hom := by
  apply (wedgeCofan_isColimit (fun j : s => X j.val)).hom_ext
  intro j
  change wedgeι (fun j : s => X j.val) j.as ≫ _ = wedgeι (fun j : s => X j.val) j.as ≫ _
  rw [← Category.assoc, wedgeι_coproductIso_hom]
  change Sigma.ι (fun j : s => X j.val) j.as ≫
    Sigma.desc (fun j : s => Sigma.ι X j.val) = _
  rw [Sigma.ι_desc,← Category.assoc,wedgeι_subfamilyMap,wedgeι_coproductIso_hom]

/-- A continuous map from a compact space into the actual chosen based
coproduct factors through the coproduct of finitely many original summands. -/
theorem continuousMap_coproduct_factor_finite {J : Type u} (X : J → BasedSpace.{u})
    [∀ j, T1Space (X j)] {A : Type*} [TopologicalSpace A] [CompactSpace A]
    (f : C(A,(∐ X : BasedSpace.{u}))) :
    ∃ (s : Finset J) (g : C(A,(∐ fun j : (s : Set J) => X j.val : BasedSpace.{u}))),
      (coproductSubfamilyMap X (s : Set J)).map.comp g = f := by
  let f' : C(A,wedge X) := (wedgeCoproductIso X).inv.map.comp f
  obtain ⟨s,g,hg⟩ := KIP126.Topology.continuousMap_wedge_factor_finite f'
  let e := wedgeCoproductIso (fun j : (s : Set J) => X j.val)
  refine ⟨s,e.hom.map.comp g,?_⟩
  apply ContinuousMap.ext
  intro a
  have he := congrArg (fun k : wedge (fun j : (s : Set J) => X j.val) ⟶ ∐ X =>
    k.map (g a)) (wedgeCoproductIso_subfamily X (s : Set J))
  have hg' := congrArg (fun k => k a) hg
  change (KIP126.Topology.wedgeSubfamilyInclusion (fun j => X j)
    (fun j => (X j).point) (s : Set J)) (g a) = (wedgeCoproductIso X).inv.map (f a) at hg'
  calc
    _ = (wedgeCoproductIso X).hom.map ((wedgeSubfamilyMap X (s : Set J)).map (g a)) := he
    _ = (wedgeCoproductIso X).hom.map ((wedgeCoproductIso X).inv.map (f a)) :=
      congrArg (wedgeCoproductIso X).hom.map hg'
    _ = f a := congrArg (fun k : (∐ X) ⟶ ∐ X => k.map (f a)) (wedgeCoproductIso X).inv_hom_id

end KIP126.StableHomotopy.Implementation.BasedSpace
