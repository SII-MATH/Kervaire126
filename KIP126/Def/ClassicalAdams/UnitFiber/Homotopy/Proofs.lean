import KIP126.Def.ClassicalAdams.TowerLayer.Mapping.Proofs
import KIP126.Def.StableHomotopy.Cohomology.Sphere.Proofs

namespace KIP126.Classical.Adams

open CategoryTheory MonoidalCategory KIP126.StableHomotopy
  KIP126.StableHomotopy.Cohomology

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  (H : Mod2EilenbergMacLane (C := C))

/-- The specified unit onto HF2 is surjective on every represented homotopy
group. At degree zero it hits 1, and all other target groups vanish. -/
theorem mod2Unit_homotopy_surjective (n : ℤ) :
    Function.Surjective (inducedMap H.unit n) := by
  intro x
  obtain ⟨y, hy⟩ := mod2SphereHomology_unit_surjective H n (x ≫ (ρ_ H.HF2).inv)
  refine ⟨y, ?_⟩
  change y ≫ H.unit = x
  have h := congrArg (fun z => z ≫ (ρ_ H.HF2).hom) hy
  change (y ≫ adamsUnit H.unit SphereSpectrum) ≫ (ρ_ H.HF2).hom =
    (x ≫ (ρ_ H.HF2).inv) ≫ (ρ_ H.HF2).hom at h
  simpa only [Category.assoc, adamsUnit_sphere_unitor,
    Iso.inv_hom_id, Category.comp_id] using h

variable [HasFunctorialCofiber (C := C)]

/-- The inclusion of the actual unit fiber is injective on all sphere
homotopy groups. This is weaker than being a categorical monomorphism. -/
theorem mod2UnitFiber_homotopy_injective (n : ℤ) :
    Function.Injective (inducedMap (fiberι H.unit) n) := by
  have h := fiberι_homotopy_injective_of_surjective H.unit (n + 1)
    (mod2Unit_homotopy_surjective H (n + 1))
  have hindex : n + 1 - 1 = n := by omega
  rw [hindex] at h
  exact h

/-- Any vanishing degree of the sphere is also a vanishing degree of its
HF2-unit fiber. No t-structure, ring multiplication or tensor exactness is used. -/
theorem mod2UnitFiber_homotopy_subsingleton (n : ℤ)
    (hsphere : Subsingleton (HomotopyGroup n (SphereSpectrum : C))) :
    Subsingleton (HomotopyGroup n (fiber H.unit)) := by
  letI := hsphere
  exact (mod2UnitFiber_homotopy_injective H n).subsingleton

end KIP126.Classical.Adams
