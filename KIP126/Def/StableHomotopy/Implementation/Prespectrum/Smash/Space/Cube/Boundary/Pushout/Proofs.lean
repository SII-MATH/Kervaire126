module

public import KIP126.Def.Topology.HomotopyLifting.Cube.Boundary.Product.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Smash.Space.Interval.Boundary.Iso.Data
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum

open CategoryTheory CategoryTheory.Limits _root_.Topology
open KIP126.Topology.HomotopyLifting
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

/-- Actual smash representatives with a compact Hausdorff parameter are
continuous on the original product with a compactly generated based space. -/
theorem continuous_parameterSmashPoint (P : TopCat.{0}) [CompactSpace P] [T2Space P]
    (A : BasedSpace.{0}) [UCompactlyGeneratedSpace.{0} A] :
    Continuous (fun p : P × A =>
      BasedSpace.smashPoint (BasedSpace.adjoinPoint P) A (.inl p.1) p.2) := by
  letI : UCompactlyGeneratedSpace.{0} (A × P) :=
    BasedSpace.compactlyGenerated_prod_compHaus A (CompHaus.of P)
  have h : Continuous (fun p : A × P =>
      BasedSpace.smashPoint (BasedSpace.adjoinPoint P) A (.inl p.2) p.1) :=
    BasedSpace.continuous_smashPoint (BasedSpace.adjoinPoint P) A
      ⟨fun p : A × P => (Sum.inl p.2 : P ⊕ PUnit),continuous_inl.comp continuous_snd⟩ ContinuousMap.fst
  exact h.comp continuous_swap

/-- The two actual cube-boundary parameter pieces glue after smashing with
an original compactly generated based space. The construction uses the proper
quotient map of the parameter cover and the original smash quotient. -/
theorem exists_spaceSmashCubeBoundaryProduct_lift (n : ℕ) (A B : BasedSpace.{0})
    [UCompactlyGeneratedSpace.{0} A]
    (f : (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)).smash A ⟶ B)
    (g : (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)).smash A ⟶ B)
    (h : ∀ (z : cubeBoundaryProductCorner n) (x : A),
      f.map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) A
        (.inl (cubeBoundaryProductTop n z)) x) =
      g.map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) A
        (.inl (cubeBoundaryProductLeft n z)) x)) :
    ∃ d : (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))).smash A ⟶ B,
      (∀ (e : cubeBoundaryProductEnds n) (x : A),
        d.map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) A
          (.inl (cubeBoundaryProductEndInclusion n e)) x) =
        f.map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) A (.inl e) x)) ∧
      (∀ (s : cubeBoundaryProductSide n) (x : A),
        d.map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) A
          (.inl (cubeBoundaryProductSideInclusion n s)) x) =
        g.map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) A (.inl s) x)) := by
  classical
  letI : T2Space intervalBoundaryObject :=
    inferInstanceAs (T2Space {t : I // t = 0 ∨ t = 1})
  letI : CompactSpace (cubeBoundaryProductEnds n) :=
    inferInstanceAs (CompactSpace (intervalBoundaryObject × ULift (Fin n → I)))
  letI : T2Space (cubeBoundaryProductEnds n) :=
    inferInstanceAs (T2Space (intervalBoundaryObject × ULift (Fin n → I)))
  letI : CompactSpace (cubeBoundaryProductSide n) :=
    inferInstanceAs (CompactSpace (I × cubeBoundaryObject n))
  letI : T2Space (cubeBoundaryProductSide n) :=
    inferInstanceAs (T2Space (I × ULift (↥(_root_.Cube.boundary (Fin n)))))
  letI : T2Space (cubeBoundaryObject (n+1)) :=
    inferInstanceAs (T2Space (ULift (↥(_root_.Cube.boundary (Fin (n+1))))))
  let q : C(cubeBoundaryProductEnds n ⊕ cubeBoundaryProductSide n,cubeBoundaryObject (n+1)) :=
    ⟨Sum.elim (cubeBoundaryProductEndInclusion n) (cubeBoundaryProductSideInclusion n),
      (cubeBoundaryProductEndInclusion n).hom.continuous.sumElim
        (cubeBoundaryProductSideInclusion n).hom.continuous⟩
  have hqs : Function.Surjective q := by
    intro z
    rcases cubeBoundaryProduct_jointly_surjective n z with ⟨e,he⟩ | ⟨s,hs⟩
    · exact ⟨.inl e,he⟩
    · exact ⟨.inr s,hs⟩
  let Q : C((cubeBoundaryProductEnds n ⊕ cubeBoundaryProductSide n) × A,
      cubeBoundaryObject (n+1) × A) :=
    ⟨Prod.map q id,q.continuous.prodMap continuous_id⟩
  have hQ : IsQuotientMap Q :=
    (q.continuous.isProperMap.prodMap isProperMap_id).isClosedMap.isQuotientMap
      Q.continuous (by
        rintro ⟨z,x⟩
        obtain ⟨p,rfl⟩ := hqs z
        exact ⟨(p,x),rfl⟩)
  let v : C((cubeBoundaryProductEnds n ⊕ cubeBoundaryProductSide n) × A,B) := by
    let raw : (cubeBoundaryProductEnds n ⊕ cubeBoundaryProductSide n) × A → B := fun p =>
      match p.1 with
      | .inl e => f.map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) A (.inl e) p.2)
      | .inr s => g.map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) A (.inl s) p.2)
    have hc := (f.map.continuous.comp (continuous_parameterSmashPoint (cubeBoundaryProductEnds n) A)).sumElim
      (g.map.continuous.comp (continuous_parameterSmashPoint (cubeBoundaryProductSide n) A))
    refine ⟨raw,?_⟩
    convert hc.comp (Homeomorph.sumProdDistrib (X := cubeBoundaryProductEnds n)
      (Y := cubeBoundaryProductSide n) (Z := A)).continuous using 1
    all_goals first | rfl | (funext p; rcases p with ⟨e | s,x⟩ <;> rfl)
  have hv : Function.FactorsThrough v Q := by
    rintro ⟨p,x⟩ ⟨r,y⟩ he
    have hx : x = y := congrArg (fun p : cubeBoundaryObject (n+1) × A => p.2) he
    subst y
    have hp : q p = q r := congrArg (fun p : cubeBoundaryObject (n+1) × A => p.1) he
    rcases p with e | s <;> rcases r with e' | s'
    · have hh := cubeBoundaryProductEndInclusion_injective n hp
      subst e'
      rfl
    · obtain ⟨z,rfl,rfl⟩ := cubeBoundaryProduct_intersection n e s' hp
      exact h z x
    · obtain ⟨z,rfl,rfl⟩ := cubeBoundaryProduct_intersection n e' s hp.symm
      exact (h z x).symm
    · have hh := cubeBoundaryProductSideInclusion_injective n hp
      subst s'
      rfl
  let d₀ := hQ.lift v hv
  have hd₀e (e : cubeBoundaryProductEnds n) (x : A) :
      d₀ (cubeBoundaryProductEndInclusion n e,x) =
        f.map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) A (.inl e) x) :=
    DFunLike.congr_fun (hQ.lift_comp v hv) (Sum.inl e,x)
  have hd₀s (s : cubeBoundaryProductSide n) (x : A) :
      d₀ (cubeBoundaryProductSideInclusion n s,x) =
        g.map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) A (.inl s) x) :=
    DFunLike.congr_fun (hQ.lift_comp v hv) (Sum.inr s,x)
  have hd₀p (z : cubeBoundaryObject (n+1)) : d₀ (z,A.point) = B.point := by
    rcases cubeBoundaryProduct_jointly_surjective n z with ⟨e,rfl⟩ | ⟨s,rfl⟩
    · rw [hd₀e,BasedSpace.smashPoint_base_right]
      exact f.point
    · rw [hd₀s,BasedSpace.smashPoint_base_right]
      exact g.point
  let D := BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))
  let raw : D × A → B := fun p => match p.1 with
    | .inl z => d₀ (z,p.2)
    | .inr _ => B.point
  have hc : Continuous raw := by
    have hh := d₀.continuous.sumElim (show Continuous (fun _ : PUnit × A => B.point) from continuous_const)
    convert hh.comp (Homeomorph.sumProdDistrib (X := cubeBoundaryObject (n+1))
      (Y := PUnit) (Z := A)).continuous using 1
    all_goals first | rfl | (funext p; rcases p with ⟨z | z,x⟩ <;> rfl)
  have hp (p : D × A) (hp : p.1 = D.point ∨ p.2 = A.point) : raw p = B.point := by
    rcases hp with hp | hp
    · change p.1 = Sum.inr PUnit.unit at hp
      simp only [raw,hp]
    · rcases p with ⟨z | z,x⟩
      · exact (congrArg (fun x => d₀ (z,x)) hp).trans (hd₀p z)
      · rfl
  have hr : ∀ p r, BasedSpace.SmashRelation D A p r → raw p = raw r :=
    fun p r h => (hp p h.1).trans (hp r h.2).symm
  have hck : Continuous[TopologicalSpace.compactlyGenerated.{0} (D × A),inferInstance] raw :=
    continuous_from_compactlyGenerated raw (fun _ k => hc.comp k.continuous)
  letI : TopologicalSpace (D × A) := TopologicalSpace.compactlyGenerated.{0} (D × A)
  exact ⟨{ map := ⟨Quot.lift raw hr,continuous_quot_lift hr hck⟩,point := rfl },hd₀e,hd₀s⟩


/-- Maps out of the actual full boundary tensor are determined by their
restrictions to the two original boundary pieces. -/
theorem spaceSmashCubeBoundaryProduct_hom_ext (n : ℕ) (X Y : Prespectrum.{0})
    (f g : spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) X ⟶ Y)
    (he : spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductEndInclusion n)) (𝟙 X) ≫ f =
      spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductEndInclusion n)) (𝟙 X) ≫ g)
    (hs : spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductSideInclusion n)) (𝟙 X) ≫ f =
      spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductSideInclusion n)) (𝟙 X) ≫ g) :
    f = g := by
  apply Hom.ext
  funext k
  apply ContinuousMap.ext
  intro z
  refine Quot.inductionOn z ?_
  rintro ⟨a,x⟩
  cases a with
  | inl z =>
    rcases cubeBoundaryProduct_jointly_surjective n z with ⟨e,rfl⟩ | ⟨s,rfl⟩
    · have hh := DFunLike.congr_fun (congrArg (fun h => h.level k) he)
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) (X.level k) (.inl e) x)
      change f.level k ((spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductEndInclusion n)) (𝟙 X)).level k
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) (X.level k) (.inl e) x)) =
        g.level k ((spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductEndInclusion n)) (𝟙 X)).level k
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) (X.level k) (.inl e) x)) at hh
      rw [spaceSmashMap_apply] at hh
      exact hh
    · have hh := DFunLike.congr_fun (congrArg (fun h => h.level k) hs)
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) (X.level k) (.inl s) x)
      change f.level k ((spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductSideInclusion n)) (𝟙 X)).level k
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) (X.level k) (.inl s) x)) =
        g.level k ((spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductSideInclusion n)) (𝟙 X)).level k
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) (X.level k) (.inl s) x)) at hh
      rw [spaceSmashMap_apply] at hh
      exact hh
  | inr p =>
    cases p
    change f.level k (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) (X.level k)
      (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))).point x) =
      g.level k (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) (X.level k)
      (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))).point x)
    rw [BasedSpace.smashPoint_base_left]
    exact (f.point k).trans (g.point k).symm

/-- Tensoring the actual two-piece successor-boundary square with a spectrum
whose original levels are compactly generated gives an actual strict pushout. -/
theorem spaceSmashCubeBoundaryProduct_isPushout (n : ℕ) (X : Prespectrum.{0})
    [∀ k, UCompactlyGeneratedSpace.{0} (X.level k)] :
    IsPushout
      (spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductTop n)) (𝟙 X))
      (spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductLeft n)) (𝟙 X))
      (spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductEndInclusion n)) (𝟙 X))
      (spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductSideInclusion n)) (𝟙 X)) := by
  classical
  let T := spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductTop n)) (𝟙 X)
  let L := spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductLeft n)) (𝟙 X)
  let E := spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductEndInclusion n)) (𝟙 X)
  let S := spaceSmashMap (BasedSpace.adjoinPointMap (cubeBoundaryProductSideInclusion n)) (𝟙 X)
  have hc : T ≫ E = L ≫ S := by
    dsimp [T,E,L,S]
    rw [← spaceSmashMap_comp,← spaceSmashMap_comp]
    congr 1
    apply BasedSpace.Hom.ext
    apply ContinuousMap.ext
    intro a
    cases a <;> rfl
  have hlevel (s : PushoutCocone T L) (k : ℕ) :=
    exists_spaceSmashCubeBoundaryProduct_lift n (X.level k) (s.pt.level k)
      (⟨s.inl.level k,s.inl.point k⟩) (⟨s.inr.level k,s.inr.point k⟩) (by
        intro z x
        have hh := DFunLike.congr_fun (congrArg (fun f => f.level k) s.condition)
          (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductCorner n)) (X.level k) (.inl z) x)
        change s.inl.level k (T.level k
          (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductCorner n)) (X.level k) (.inl z) x)) =
          s.inr.level k (L.level k
          (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductCorner n)) (X.level k) (.inl z) x)) at hh
        dsimp [T,L] at hh
        rw [spaceSmashMap_apply,spaceSmashMap_apply] at hh
        exact hh)
  choose d hdE hdS using hlevel
  have hdesc (s : PushoutCocone T L) :
      ∃ m : spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) X ⟶ s.pt,
        E ≫ m = s.inl ∧ S ≫ m = s.inr := by
    let m : spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) X ⟶ s.pt := {
      level k := (d s k).map
      point k := (d s k).point
      bond k z t := by
        refine Quot.inductionOn z ?_
        rintro ⟨a,x⟩
        change (d s (k+1)).map ((spaceSmash (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) X).bond k
          (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) (X.level k) a x,t)) =
          s.pt.bond k ((d s k).map
            (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) (X.level k) a x),t)
        rw [spaceSmash_bond]
        cases a with
        | inl z =>
          rcases cubeBoundaryProduct_jointly_surjective n z with ⟨e,rfl⟩ | ⟨r,rfl⟩
          · rw [hdE,hdE]
            have hh := s.inl.bond k
              (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) (X.level k) (.inl e) x) t
            rw [spaceSmash_bond] at hh
            exact hh
          · rw [hdS,hdS]
            have hh := s.inr.bond k
              (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) (X.level k) (.inl r) x) t
            rw [spaceSmash_bond] at hh
            exact hh
        | inr p =>
          cases p
          change (d s (k+1)).map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) (X.level (k+1))
            (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))).point (X.bond k (x,t))) =
            s.pt.bond k ((d s k).map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) (X.level k)
              (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))).point x),t)
          rw [BasedSpace.smashPoint_base_left,BasedSpace.smashPoint_base_left,(d s (k+1)).point,(d s k).point,s.pt.bond_point] }
    refine ⟨m,?_,?_⟩
    · apply Hom.ext
      funext k
      apply ContinuousMap.ext
      intro z
      refine Quot.inductionOn z ?_
      rintro ⟨a,x⟩
      change (d s k).map (E.level k
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) (X.level k) a x)) =
        s.inl.level k (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) (X.level k) a x)
      dsimp [E]
      rw [spaceSmashMap_apply]
      cases a with
      | inl e => exact hdE s k e x
      | inr p =>
        cases p
        change (d s k).map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) (X.level k)
          (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))).point x) =
          s.inl.level k (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)) (X.level k)
            (BasedSpace.adjoinPoint (cubeBoundaryProductEnds n)).point x)
        rw [BasedSpace.smashPoint_base_left,BasedSpace.smashPoint_base_left,(d s k).point]
        exact (s.inl.point k).symm
    · apply Hom.ext
      funext k
      apply ContinuousMap.ext
      intro z
      refine Quot.inductionOn z ?_
      rintro ⟨a,x⟩
      change (d s k).map (S.level k
        (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) (X.level k) a x)) =
        s.inr.level k (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) (X.level k) a x)
      dsimp [S]
      rw [spaceSmashMap_apply]
      cases a with
      | inl r => exact hdS s k r x
      | inr p =>
        cases p
        change (d s k).map (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))) (X.level k)
          (BasedSpace.adjoinPoint (cubeBoundaryObject (n+1))).point x) =
          s.inr.level k (BasedSpace.smashPoint (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)) (X.level k)
            (BasedSpace.adjoinPoint (cubeBoundaryProductSide n)).point x)
        rw [BasedSpace.smashPoint_base_left,BasedSpace.smashPoint_base_left,(d s k).point]
        exact (s.inr.point k).symm
  apply IsPushout.of_isColimit (c := PushoutCocone.mk E S hc)
  refine PushoutCocone.IsColimit.mk _ (fun s => (hdesc s).choose)
    (fun s => (hdesc s).choose_spec.1) (fun s => (hdesc s).choose_spec.2) ?_
  intro s m hmE hmS
  exact spaceSmashCubeBoundaryProduct_hom_ext n X s.pt m (hdesc s).choose
    (hmE.trans (hdesc s).choose_spec.1.symm) (hmS.trans (hdesc s).choose_spec.2.symm)

end KIP126.StableHomotopy.Implementation.Prespectrum
