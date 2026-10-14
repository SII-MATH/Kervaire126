module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Representation.Equivalence

@[expose] public section
namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory _root_.Topology
set_option backward.isDefEq.respectTransparency false

/-- Every localized sphere morphism into a prespectrum whose levels have based CW type factors through a free prespectrum on an actual finite CW subcomplex. -/
theorem sourceSphere_hom_factor_finite_CW_model (X : Prespectrum)
    (hX : ∀ n, (X.level n).HasCWType) (d : ℤ) (f : sourceSphere d ⟶ sourceLocalization.obj X) :
    ∃ (n r : ℕ) (h : (r : ℤ) = d+n)
      (Y : BasedSpace) (hY : T2Space Y) (cY : CWComplex (Set.univ : Set Y)),
      letI := hY
      letI := cY
      ∃ E : CWComplex.Subcomplex (Set.univ : Set Y),
        CWComplex.Finite (E : Set Y) ∧ ∃ hp : Y.point ∈ E,
          ∃ (a : sphereLevel r ⟶ Y.subspace E hp)
            (b : free n (Y.subspace E hp) ⟶ X),
            (sourceFreeSphereDegreeIso d n r h).inv ≫ sourceLocalization.map (freeMap n a) ≫
              sourceLocalization.map b = f := by
  let x := (sourceStableHomotopyEquiv X d).symm f
  obtain ⟨n,r,h,Y,hY,cY,E,hE,hp,a,b,hrep⟩ :=
    stableHomotopy_represented_by_finite_CW_model X hX d x
  letI := hY
  letI := cY
  refine ⟨n,r,h,Y,hY,cY,E,hE,hp,a,b,?_⟩
  have hn : sourceStableHomotopyEquiv X d
      (stableHomotopyMap (freeMap n a ≫ b) d (freeSphereGenerator d n r h)) =
      sourceStableHomotopyEquiv (free n (sphereLevel r)) d (freeSphereGenerator d n r h) ≫
        sourceLocalization.map (freeMap n a ≫ b) :=
    stableHomotopySourceMap_natural (freeMap n a ≫ b) d (freeSphereGenerator d n r h)
  rw [sourceStableHomotopyEquiv_freeSphereGenerator,Functor.map_comp] at hn
  rw [← hn,hrep]
  exact (sourceStableHomotopyEquiv X d).apply_symm_apply f

end KIP126.StableHomotopy.Implementation.Prespectrum
