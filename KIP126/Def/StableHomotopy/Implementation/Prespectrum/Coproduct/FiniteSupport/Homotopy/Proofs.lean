module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Coproduct.FiniteSupport.Proofs
public import KIP126.Def.Topology.Coproduct.Wedge.HomotopySupport.Homotopy.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory CategoryTheory.Limits
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- Every actual stable class of an arbitrary strict coproduct has
finite summand support after a genuine based homotopy of its original
cubical representative. No separation condition is imposed on the levels. -/
theorem stableHomotopy_coproduct_finite_support_general {J : Type u}
    (X : J → Prespectrum.{u}) (d : ℤ) (a : StableHomotopy (∐ X) d) :
    ∃ (s : Finset J) (b : StableHomotopy (∐ fun j : (s : Set J) => X j.val) d),
      stableHomotopyMap (coproductSubfamilyMap X (s : Set J)) d b = a := by
  induction a using Quot.inductionOn with
  | h a =>
      let F := fun j => (X j).level a.stage
      let e := coproductLevelIso X a.stage ≪≫ (BasedSpace.wedgeCoproductIso F).symm
      let p := e.hom.map.comp a.loop.val
      obtain ⟨s,⟨H⟩⟩ := KIP126.Topology.continuousMap_wedge_homotopy_finite_support p
      let S := (s : Set J)
      let F' := fun j : S => F j.val
      let e' := coproductLevelIso (fun j : S => X j.val) a.stage ≪≫
        (BasedSpace.wedgeCoproductIso F').symm
      let R := KIP126.Topology.wedgeSubfamilyRetraction (fun j => F j) (fun j => (F j).point) S
      let incl := BasedSpace.wedgeSubfamilyMap F S
      let q := coproductSubfamilyMap X S
      let g := e'.inv.map.comp (R.comp p)
      have hinc : (evaluationFunctor a.stage).map q ≫ e.hom = e'.hom ≫ incl := by
        have hw := congrArg (fun k => (BasedSpace.wedgeCoproductIso F').inv ≫ k ≫
          (BasedSpace.wedgeCoproductIso F).inv) (BasedSpace.wedgeCoproductIso_subfamily F S)
        dsimp only [F'] at hw
        simp only [Category.assoc,Iso.inv_hom_id_assoc,Iso.hom_inv_id,Category.comp_id] at hw
        change (evaluationFunctor a.stage).map q ≫
          ((coproductLevelIso X a.stage).hom ≫ (BasedSpace.wedgeCoproductIso F).inv) =
          ((coproductLevelIso (fun j : S => X j.val) a.stage).hom ≫
            (BasedSpace.wedgeCoproductIso F').inv) ≫ incl
        rw [← Category.assoc,coproductLevelIso_subfamily]
        simp only [Category.assoc]
        exact congrArg (fun k => (coproductLevelIso (fun j : S => X j.val) a.stage).hom ≫ k) hw
      have he (z : (∐ X : Prespectrum.{u}).level a.stage) : e.inv.map (e.hom.map z) = z :=
        congrArg (fun k => k.map z) e.hom_inv_id
      have he' (z : BasedSpace.wedge F') : e'.hom.map (e'.inv.map z) = z :=
        congrArg (fun k => k.map z) e'.inv_hom_id
      have hgp (z : Fin a.dimension → I) (hz : z ∈ Cube.boundary (Fin a.dimension)) :
          g z = ((∐ fun j : S => X j.val : Prespectrum.{u}).level a.stage).point := by
        change e'.inv.map (R (e.hom.map (a.loop z))) = _
        have haz : a.loop z = ((∐ X : Prespectrum.{u}).level a.stage).point :=
          a.loop.property z hz
        rw [haz,e.hom.point]
        change e'.inv.map (BasedSpace.wedge F').point = _
        exact e'.inv.point
      let b : Representative (∐ fun j : S => X j.val) d :=
        ⟨a.stage,a.dimension,a.degree,⟨g,hgp⟩⟩
      refine ⟨s,Quot.mk _ b,?_⟩
      have hp : e.inv.map.comp p = a.loop.val := by
        ext z
        exact he (a.loop z)
      have hg : e.inv.map.comp (incl.map.comp (R.comp p)) = (q.level a.stage).comp g := by
        ext z
        apply Function.LeftInverse.injective he
        change e.hom.map (e.inv.map (incl.map (R (p z)))) =
          e.hom.map (q.level a.stage (e'.inv.map (R (p z))))
        rw [show e.hom.map (e.inv.map (incl.map (R (p z)))) = incl.map (R (p z)) from
          congrArg (fun k => k.map (incl.map (R (p z)))) e.inv_hom_id]
        have hh := congrArg (fun k => k.map (e'.inv.map (R (p z)))) hinc
        change e.hom.map (q.level a.stage (e'.inv.map (R (p z)))) =
          incl.map (e'.hom.map (e'.inv.map (R (p z)))) at hh
        rw [he'] at hh
        exact hh.symm
      have H' := (H.compContinuousMap e.inv.map).cast hp hg
      have hab : GenLoop.Homotopic a.loop (b.map q).loop := by
        refine ⟨{ H'.toHomotopy with prop' := ?_ }⟩
        intro t z hz
        apply H'.eq_fst t
        change p z = incl.map (R (p z))
        change e.hom.map (a.loop z) = incl.map (R (e.hom.map (a.loop z)))
        have haz : a.loop z = ((∐ X : Prespectrum.{u}).level a.stage).point :=
          a.loop.property z hz
        rw [haz,e.hom.point]
        rfl
      change Quot.mk _ (b.map q) = Quot.mk _ a
      exact (Quot.sound (StableRelation.homotopy a (b.map q).loop hab)).symm

end KIP126.StableHomotopy.Implementation.Prespectrum
