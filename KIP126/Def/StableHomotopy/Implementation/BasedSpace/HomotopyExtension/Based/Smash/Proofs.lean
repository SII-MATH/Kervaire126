module

public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.HomotopyExtension.Based.Predicates
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Continuity.Proofs
public import KIP126.Def.StableHomotopy.Implementation.BasedSpace.Smash.Associativity.Proofs
public import KIP126.Def.Topology.HomotopyExtension.Retraction.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory Set _root_.Topology
open KIP126.Topology.HomotopyExtension
open scoped unitInterval
set_option backward.isDefEq.respectTransparency false

/-- The original quotient smash of a closed homotopy-extension map with
any based space has based homotopy extension. No condition on the second
factor is imposed: continuity is checked on compact Hausdorff tests of
the original k-product before descending its actual quotient. -/
theorem smashMap_hasBasedHomotopyExtension {A B : BasedSpace.{0}}
    (i : A ⟶ B) (hi : IsClosedEmbedding i.map)
    (hH : HasHomotopyExtension (TopCat.ofHom i.map)) (X : BasedSpace.{0}) :
    HasBasedHomotopyExtension (smashMap i (𝟙 X)) := by
  classical
  intro Z f p hp_point hp_zero
  obtain ⟨r, hr_zero, hr_side, hr_range⟩ := hH.exists_cylinder_retraction
  change ∀ a t, r (i.map a,t) = (i.map a,t) at hr_side
  change ∀ q, (r q).2 = 0 ∨ (r q).1 ∈ range i.map at hr_range
  let e := hi.isEmbedding.toHomeomorph
  let raw : (B × X) × I → Z := fun q =>
    if h : (r (q.1.1,q.2)).1 ∈ range i.map then
      p (smashPoint A X (e.symm ⟨(r (q.1.1,q.2)).1,h⟩) q.1.2,(r (q.1.1,q.2)).2)
    else f.map (smashPoint B X (r (q.1.1,q.2)).1 q.1.2)
  have raw_bottom (b : B) (x : X) (t : I) (ht : (r (b,t)).2 = 0) :
      raw ((b,x),t) = f.map (smashPoint B X (r (b,t)).1 x) := by
    dsimp only [raw]
    split_ifs with h
    · rw [ht,hp_zero,smashMap_apply]
      have he := congrArg Subtype.val (e.apply_symm_apply ⟨(r (b,t)).1,h⟩)
      change i.map (e.symm ⟨(r (b,t)).1,h⟩) = (r (b,t)).1 at he
      change f.map (smashPoint B X (i.map (e.symm ⟨(r (b,t)).1,h⟩)) x) = _
      rw [he]
    · rfl
  have raw_side (a : A) (x : X) (t : I) :
      raw ((i.map a,x),t) = p (smashPoint A X a x,t) := by
    have h : (r (i.map a,t)).1 ∈ range i.map := by
      rw [hr_side]
      exact ⟨a,rfl⟩
    dsimp only [raw]
    rw [dif_pos h]
    have he : e.symm ⟨(r (i.map a,t)).1,h⟩ = a := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Subtype.ext
      exact congrArg Prod.fst (hr_side a t)
    rw [he,hr_side]
  have raw_zero (b : B) (x : X) :
      raw ((b,x),0) = f.map (smashPoint B X b x) := by
    rw [raw_bottom b x 0 (congrArg Prod.snd (hr_zero b)),hr_zero]
  have raw_left (x : X) (t : I) : raw ((B.point,x),t) = Z.point := by
    rw [← i.point,raw_side,smashPoint_base_left,hp_point]
  have raw_right (b : B) (t : I) : raw ((b,X.point),t) = Z.point := by
    dsimp only [raw]
    split_ifs <;> simp only [smashPoint_base_right,hp_point,f.point]
  have raw_test (K : CompHaus.{0}) (b : C(K,B)) (x : C(K,X)) (t : C(K,I)) :
      Continuous (fun k => raw ((b k,x k),t k)) := by
    let R : C(K,B × I) := r.comp (b.prodMk t)
    let U : Set K := {k | (R k).2 = 0}
    let V : Set K := {k | (R k).1 ∈ range i.map}
    have hU : IsClosed U := isClosed_eq R.continuous.snd continuous_const
    have hV : IsClosed V := hi.isClosed_range.preimage R.continuous.fst
    have hUV : U ∪ V = univ := Set.eq_univ_of_forall (fun k => hr_range (b k,t k))
    letI : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
    let aV : C(V,A) :=
      ⟨fun k => e.symm ⟨(R k.val).1,k.property⟩,
        e.symm.continuous.comp ((R.continuous.fst.comp continuous_subtype_val).subtype_mk _)⟩
    let pV : C(V,Z) :=
      ⟨fun k => p (smashPoint A X (aV k) (x k.val),(R k.val).2),
        p.continuous.comp ((continuous_smashPoint A X aV
          (x.comp ⟨Subtype.val,continuous_subtype_val⟩)).prodMk
            (R.continuous.snd.comp continuous_subtype_val))⟩
    have hv : ContinuousOn (fun k => raw ((b k,x k),t k)) V := by
      apply continuousOn_iff_continuous_restrict.mpr
      apply pV.continuous.congr
      intro k
      change pV k = raw ((b k.val,x k.val),t k.val)
      dsimp only [raw]
      have hk : (r (b k.val,t k.val)).1 ∈ range i.map := k.property
      rw [dif_pos hk]
      rfl
    have hu : ContinuousOn (fun k => raw ((b k,x k),t k)) U :=
      (f.map.continuous.comp (continuous_smashPoint B X
        ⟨fun k => (R k).1,R.continuous.fst⟩ x)).continuousOn.congr
          (fun k hk => raw_bottom (b k) (x k) (t k) hk)
    exact continuousOn_univ.mp (hUV ▸ hu.union_of_isClosed hv hU hV)
  let family : B × X → C(I,Z) := fun bx =>
    ⟨fun t => raw (bx,t),raw_test (CompHaus.of I)
      (ContinuousMap.const _ bx.1) (ContinuousMap.const _ bx.2) (ContinuousMap.id _)⟩
  have hfamily : Continuous[TopologicalSpace.compactlyGenerated.{0} (B × X),inferInstance]
      family := by
    apply continuous_from_compactlyGenerated
    intro K g
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact raw_test (CompHaus.of (K × I))
      ⟨fun q => (g q.1).1,g.continuous.fst.comp continuous_fst⟩
      ⟨fun q => (g q.1).2,g.continuous.snd.comp continuous_fst⟩ ContinuousMap.snd
  have raw_collapsed (bx : B × X) (t : I)
      (h : bx.1 = B.point ∨ bx.2 = X.point) : raw (bx,t) = Z.point := by
    rcases h with h | h
    · rcases bx with ⟨b,x⟩
      dsimp only at h
      subst b
      exact raw_left x t
    · rcases bx with ⟨b,x⟩
      dsimp only at h
      subst x
      exact raw_right b t
  let H : C((B.smash X) × I,Z) :=
    ⟨fun q => Quot.lift (fun bx => raw (bx,q.2))
      (fun bx bx' h => (raw_collapsed bx q.2 h.1).trans
        (raw_collapsed bx' q.2 h.2).symm) q.1,by
      letI : TopologicalSpace (B × X) := TopologicalSpace.compactlyGenerated.{0} (B × X)
      apply isQuotientMap_quot_mk.continuous_lift_prod_left
      exact (⟨family,hfamily⟩ : C(B × X,C(I,Z))).uncurry.continuous⟩
  refine ⟨H,?_,?_,?_⟩
  · intro t
    exact raw_left X.point t
  · intro z
    refine Quot.inductionOn z ?_
    rintro ⟨b,x⟩
    exact raw_zero b x
  · intro z t
    refine Quot.inductionOn z ?_
    rintro ⟨a,x⟩
    change H ((smashMap i (𝟙 X)).map (smashPoint A X a x),t) = _
    rw [smashMap_apply]
    exact raw_side a x t

end KIP126.StableHomotopy.Implementation.BasedSpace
