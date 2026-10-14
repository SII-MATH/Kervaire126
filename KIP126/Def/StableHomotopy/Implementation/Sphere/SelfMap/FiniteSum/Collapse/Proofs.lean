module

public import KIP126.Def.StableHomotopy.Implementation.Sphere.SelfMap.FiniteSum.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.SelfMap.Proofs
public import KIP126.Def.StableHomotopy.Implementation.Sphere.OrderModel.Collapse.Proofs

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory KIP126.Topology
open scoped unitInterval OnePoint
set_option backward.isDefEq.respectTransparency false

/-- Every original positive-dimensional sphere self-map has a finite
additive decomposition in the original stable quotient. The terms are
the actual branches of its actual complement-collapse map, retaining the
original window, quotient homeomorphism and pointed sheet homeomorphism.
No covering or local-degree hypothesis is supplied. -/
theorem exists_sphereSelfMapClass_finite_collapse_sum (n : ℕ) (hn : 0 < n)
    (f : sphereLevel n ⟶ sphereLevel n) :
    ∃ (m : ℕ) (u : sphereLevel n ⟶ sphereLevel n) (a b : Fin n → I),
    ∃ _hab : ∀ i, a i < b i,
      Nonempty (ContinuousMap.HomotopyRel u.map f.map {(sphereLevel n).point}) ∧
      ∃ e : Quot (fun x z : sphereLevel n =>
          u.map x ∉ sphereWindow n a b ∧ u.map z ∉ sphereWindow n a b) ≃ₜ
          Wedge (fun _ : Fin m => OnePoint (sphereWindow n a b)) (fun _ => ∞),
      ∃ he : e (Quot.mk _ (sphereLevel n).point) = wedgePoint _ _,
      ∃ r : OnePoint (sphereWindow n a b) ≃ₜ sphereLevel n,
      ∃ hr : r ∞ = (sphereLevel n).point,
        let Y : Fin m → BasedSpace := fun _ => ⟨TopCat.of (OnePoint (sphereWindow n a b)),∞⟩
        let p : sphereLevel n ⟶ BasedSpace.wedge Y :=
          ⟨⟨fun x => e (Quot.mk _ x),e.continuous.comp continuous_quot_mk⟩,he⟩
        sphereSelfMapClass n f = ∑ j : Fin m, sphereSelfMapClass n
          (p ≫ sphereWedgeProjection Y j ≫ (⟨⟨r,r.continuous⟩,hr⟩ : Y j ⟶ sphereLevel n)) := by
  obtain ⟨m,u,g,a,b,hab,hu,hg,_,e,he,r,hr,hformula⟩ :=
    exists_sphere_map_finite_collapse_decomposition n hn f
  refine ⟨m,u,a,b,hab,hu,e,he,r,hr,?_⟩
  let Y : Fin m → BasedSpace := fun _ => ⟨TopCat.of (OnePoint (sphereWindow n a b)),∞⟩
  let p : sphereLevel n ⟶ BasedSpace.wedge Y :=
    ⟨⟨fun x => e (Quot.mk _ x),e.continuous.comp continuous_quot_mk⟩,he⟩
  let s : ∀ j : Fin m, Y j ⟶ sphereLevel n := fun _ => ⟨⟨r,r.continuous⟩,hr⟩
  change sphereSelfMapClass n f = ∑ j, sphereSelfMapClass n (p ≫ sphereWedgeProjection Y j ≫ s j)
  have hfactor : g = p ≫ BasedSpace.wedgeDesc s := by
    apply BasedSpace.Hom.ext
    apply ContinuousMap.ext
    exact hformula
  calc
    sphereSelfMapClass n f = sphereSelfMapClass n g :=
      (sphereSelfMapClass_homotopic n g f hg).symm
    _ = ∑ j, sphereSelfMapClass n (p ≫ sphereWedgeProjection Y j ≫ s j) := by
      rw [hfactor]
      exact sphereSelfMapClass_wedgeDesc_eq_sum n Y p s

end KIP126.StableHomotopy.Implementation.Prespectrum
