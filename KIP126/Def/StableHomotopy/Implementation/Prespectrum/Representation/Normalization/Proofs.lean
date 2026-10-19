module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Normalization.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval

set_option backward.isDefEq.respectTransparency false

theorem genLoopFreeSphereMap_cube (X : Prespectrum) (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) (t : Fin r → I) :
    (genLoopFreeSphereMap X n r p).level n (freeSphereLoop n r t) = p t :=
  (genLoop_freeSphere_map_exists_unique X n r p).choose_spec.1 t

theorem genLoopFreeSphereMap_stabilization (X : Prespectrum) (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    genLoopFreeSphereMap X (n+1) (r+1) (stabilizeLoop X n r p) =
      freeStabilization n (sphereLevel r) ≫ genLoopFreeSphereMap X n r p := by
  apply ((genLoop_freeSphere_map_exists_unique X (n+1) (r+1)
    (stabilizeLoop X n r p)).choose_spec.2 _ _).symm
  intro t
  change (genLoopFreeSphereMap X n r p).level (n+1)
    ((freeStabilization n (sphereLevel r)).level (n+1) (freeSphereLoop (n+1) (r+1) t)) = _
  rw [freeStabilization_freeSphereLoop]
  change (genLoopFreeSphereMap X n r p).level (n+1)
    ((free n (sphereLevel r)).bond n (freeSphereLoop n r (fun i => t i.succ),t 0)) = _
  rw [(genLoopFreeSphereMap X n r p).bond,genLoopFreeSphereMap_cube]
  rfl

theorem sourceFreeSphereDegreeIso_succ (d : ℤ) (n r : ℕ) (h : (r : ℤ) = d+n)
    (h' : ((r+1 : ℕ) : ℤ) = d+(n+1 : ℕ)) :
    sourceFreeSphereDegreeIso d (n+1) (r+1) h' =
      sourceFreeStabilizationIso n r ≪≫ sourceFreeSphereDegreeIso d n r h := by
  change (sourceFreeStabilizationIso n r ≪≫ sourceFreeSphereNormalizeIso n r ≪≫ eqToIso _) ≪≫ eqToIso _ =
    sourceFreeStabilizationIso n r ≪≫ (sourceFreeSphereNormalizeIso n r ≪≫ eqToIso _)
  simp only [Iso.trans_assoc,eqToIso_trans]

theorem Representative.sourceMap_stabilization {X : Prespectrum} {d : ℤ}
    (a : Representative X d) : a.sourceMap = a.next.sourceMap := by
  unfold Representative.sourceMap
  change _ = (sourceFreeSphereDegreeIso d (a.stage+1) (a.dimension+1) _).inv ≫
    sourceLocalization.map (genLoopFreeSphereMap X (a.stage+1) (a.dimension+1)
      (stabilizeLoop X a.stage a.dimension a.loop))
  rw [sourceFreeSphereDegreeIso_succ d a.stage a.dimension a.degree,
    genLoopFreeSphereMap_stabilization,Functor.map_comp]
  simp only [Iso.trans_inv,Category.assoc]
  change _ = _ ≫ (sourceFreeStabilizationIso a.stage a.dimension).inv ≫
    (sourceFreeStabilizationIso a.stage a.dimension).hom ≫ _
  rw [Iso.inv_hom_id_assoc]

theorem Representative.sourceMap_relation {X : Prespectrum} {d : ℤ}
    (a b : Representative X d) (h : StableRelation X d a b) : a.sourceMap = b.sourceMap := by
  cases h with
  | homotopy p hp =>
    unfold Representative.sourceMap
    congr 1
    exact source_freeSphere_maps_eq_of_genLoop_homotopy a.stage a.dimension X a.loop p _ _
      (genLoopFreeSphereMap_cube X a.stage a.dimension a.loop)
      (genLoopFreeSphereMap_cube X a.stage a.dimension p) hp
  | stabilization => exact a.sourceMap_stabilization

theorem genLoopFreeSphereMap_natural {X Y : Prespectrum} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) (X.level n) (X.level n).point) :
    genLoopFreeSphereMap Y n r
      ⟨(f.level n).comp p.val,fun t ht => (congrArg (f.level n) (p.property t ht)).trans (f.point n)⟩ =
      genLoopFreeSphereMap X n r p ≫ f := by
  apply ((genLoop_freeSphere_map_exists_unique Y n r _).choose_spec.2 _ _).symm
  intro t
  change f.level n ((genLoopFreeSphereMap X n r p).level n (freeSphereLoop n r t)) = f.level n (p t)
  rw [genLoopFreeSphereMap_cube]

theorem genLoopFreeSphereMap_id (n r : ℕ) :
    genLoopFreeSphereMap (free n (sphereLevel r)) n r (freeSphereLoop n r) = 𝟙 _ := by
  exact ((genLoop_freeSphere_map_exists_unique (free n (sphereLevel r)) n r _).choose_spec.2
    (𝟙 _) (fun _ => rfl)).symm

theorem freeStabilization_generator (d : ℤ) (n r : ℕ) (h : (r : ℤ) = d+n)
    (h' : ((r+1 : ℕ) : ℤ) = d+(n+1 : ℕ)) :
    stableHomotopyMap (freeStabilization n (sphereLevel r)) d
      (freeSphereGenerator d (n+1) (r+1) h') = freeSphereGenerator d n r h := by
  let a : Representative (free n (sphereLevel r)) d := ⟨n,r,h,freeSphereLoop n r⟩
  change Quot.mk _ ((⟨n+1,r+1,h',freeSphereLoop (n+1) (r+1)⟩ :
    Representative (free (n+1) (sphereLevel (r+1))) d).map (freeStabilization n (sphereLevel r))) =
      Quot.mk _ a
  have he : (⟨n+1,r+1,h',freeSphereLoop (n+1) (r+1)⟩ :
      Representative (free (n+1) (sphereLevel (r+1))) d).map (freeStabilization n (sphereLevel r)) =
        a.next := by
    dsimp [Representative.map,Representative.next,a]
    congr 1
    exact GenLoop.ext _ _ (freeStabilization_freeSphereLoop n r)
  rw [he]
  exact (Quot.sound (StableRelation.stabilization a)).symm

/-- The actual normalization isomorphism preserves the specified stable sphere generator. -/
theorem sourceFreeSphereDegreeIso_generator (d : ℤ) (n r : ℕ) (h : (r : ℤ) = d+n) :
    (sourceStableHomotopyFunctor d).map (sourceFreeSphereDegreeIso d n r h).hom
      (freeSphereGenerator d n r h) = sourceSphereGenerator d := by
  induction n generalizing r with
  | zero =>
    have hd : d = r := by omega
    subst d
    simp [sourceFreeSphereDegreeIso,sourceFreeSphereNormalizeIso,sourceSphereGenerator,sourceSphere,sourceSpherePrespectrum]
  | succ n ih =>
    cases r with
    | zero =>
      have hd : d = -(n+1 : ℕ) := by omega
      subst d
      change (sourceStableHomotopyFunctor (Int.negSucc n)).map
        (sourceFreeSphereDegreeIso (Int.negSucc n) (n+1) 0 h).hom
          (freeSphereGenerator (Int.negSucc n) (n+1) 0 h) = sourceSphereGenerator (Int.negSucc n)
      simp [sourceFreeSphereDegreeIso,sourceFreeSphereNormalizeIso,sourceSphereGenerator,sourceSphere,sourceSpherePrespectrum]
    | succ r =>
      have hp : (r : ℤ) = d+n := by omega
      rw [sourceFreeSphereDegreeIso_succ d n r hp]
      change (sourceStableHomotopyFunctor d).map
        ((sourceFreeStabilizationIso n r).hom ≫ (sourceFreeSphereDegreeIso d n r hp).hom)
          (freeSphereGenerator d (n+1) (r+1) h) = _
      rw [CategoryTheory.Functor.map_comp]
      change (sourceStableHomotopyFunctor d).map (sourceFreeSphereDegreeIso d n r hp).hom
        ((sourceStableHomotopyFunctor d).map (sourceLocalization.map (freeStabilization n (sphereLevel r)))
          (freeSphereGenerator d (n+1) (r+1) h)) = _
      rw [sourceStableHomotopyFunctor_map]
      change (sourceStableHomotopyFunctor d).map (sourceFreeSphereDegreeIso d n r hp).hom
        (stableHomotopyMap (freeStabilization n (sphereLevel r)) d (freeSphereGenerator d (n+1) (r+1) h)) = _
      rw [freeStabilization_generator d n r hp h]
      exact ih r hp

theorem Representative.sourceMap_generator {X : Prespectrum} {d : ℤ}
    (a : Representative X d) :
    (sourceStableHomotopyFunctor d).map a.sourceMap (sourceSphereGenerator d) =
      Quot.mk (StableRelation X d) a := by
  have hinv : (sourceStableHomotopyFunctor d).map
      (sourceFreeSphereDegreeIso d a.stage a.dimension a.degree).inv (sourceSphereGenerator d) =
        freeSphereGenerator d a.stage a.dimension a.degree := by
    rw [← sourceFreeSphereDegreeIso_generator d a.stage a.dimension a.degree]
    exact congrArg (fun f => f (freeSphereGenerator d a.stage a.dimension a.degree))
      ((sourceStableHomotopyFunctor d).mapIso
        (sourceFreeSphereDegreeIso d a.stage a.dimension a.degree)).hom_inv_id
  unfold Representative.sourceMap
  rw [CategoryTheory.Functor.map_comp]
  change (sourceStableHomotopyFunctor d).map
    (sourceLocalization.map (genLoopFreeSphereMap X a.stage a.dimension a.loop))
    ((sourceStableHomotopyFunctor d).map
      (sourceFreeSphereDegreeIso d a.stage a.dimension a.degree).inv (sourceSphereGenerator d)) = _
  rw [hinv,sourceStableHomotopyFunctor_map]
  change Quot.mk _ ((⟨a.stage,a.dimension,a.degree,freeSphereLoop a.stage a.dimension⟩ :
    Representative (free a.stage (sphereLevel a.dimension)) d).map
      (genLoopFreeSphereMap X a.stage a.dimension a.loop)) = Quot.mk _ a
  congr 1
  cases a with
  | mk n r h p =>
    dsimp [Representative.map]
    congr 1
    exact GenLoop.ext _ _ (genLoopFreeSphereMap_cube X n r p)

/-- The localized morphism of a representative is natural under actual prespectrum maps. -/
theorem Representative.sourceMap_natural {X Y : Prespectrum} (f : X ⟶ Y) {d : ℤ}
    (a : Representative X d) : (a.map f).sourceMap = a.sourceMap ≫ sourceLocalization.map f := by
  dsimp [Representative.sourceMap,Representative.map]
  rw [genLoopFreeSphereMap_natural,Functor.map_comp,Category.assoc]

end KIP126.StableHomotopy.Implementation.Prespectrum
