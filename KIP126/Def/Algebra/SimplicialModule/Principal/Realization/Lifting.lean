module

public import KIP126.Def.Algebra.SimplicialModule.Principal.Realization.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Proofs
public import KIP126.Def.Topology.HomotopyLifting.Cube.Faces.Horn.Proofs

@[expose] public section

namespace KIP126.Core.SimplicialModule
open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open KIP126.Topology.HomotopyLifting
open scoped unitInterval
universe u v
variable {R : Type u} [Ring R]
set_option backward.isDefEq.respectTransparency false

/-- The realized module projection lifts an actual homotopy factoring through
a fixed target simplex, with every prescribed point of a retractile horn retained. -/
theorem principalRealization_exists_relativeLift
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : ℕ} (b : B.obj (op ⦋n⦌)) (z : A.obj (op ⦋n⦌))
    (hz : (p.app (op ⦋n⦌)).hom z = b)
    {T : Type v} [TopologicalSpace T] (S : Set T)
    (r : C(I × T,CylinderHorn T S)) (hr : ∀ w : CylinderHorn T S, r w.val = w)
    (g : C(CylinderHorn T S, |A ⋙ forget (ModuleCat R)|))
    (H : C(I × T, |(Δ[n] : SSet.{u})|))
    (hcomm : ∀ w, SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R))) (g w) =
      SSet.toTop.map ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b) (H w.val)) :
    ∃ L : C(I × T, |A ⋙ forget (ModuleCat R)|),
      (∀ w, SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R))) (L w) =
        SSet.toTop.map ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b) (H w)) ∧
      (∀ w : CylinderHorn T S, L w.val = g w) := by
  let e := principalRealizationHomeomorph p b z hz
  let gF : C(CylinderHorn T S, |kernel p ⋙ forget (ModuleCat R)|) :=
    ⟨fun w => (e.symm ⟨(g w,H w.val),hcomm w⟩).1,
      continuous_fst.comp (e.symm.continuous.comp
        ((g.continuous.prodMk (H.continuous.comp continuous_subtype_val)).subtype_mk hcomm))⟩
  let L : C(I × T, |A ⋙ forget (ModuleCat R)|) :=
    ⟨fun w => (e (gF (r w),H w)).val.1,
      continuous_fst.comp (continuous_subtype_val.comp
        (e.continuous.comp ((gF.continuous.comp r.continuous).prodMk H.continuous)))⟩
  refine ⟨L,?_,?_⟩
  · intro w
    exact (e (gF (r w),H w)).property.trans
      (congrArg (SSet.toTop.map ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b))
        (principalRealizationHomeomorph_snd p b z hz (gF (r w),H w)))
  · intro w
    change (e (gF (r w.val),H w.val)).val.1 = g w
    rw [hr]
    have he : (gF w,H w.val) = e.symm ⟨(g w,H w.val),hcomm w⟩ := by
      apply Prod.ext
      · rfl
      · exact (principalRealizationHomeomorph_symm_snd p b z hz ⟨(g w,H w.val),hcomm w⟩).symm
    rw [he,Homeomorph.apply_symm_apply]

/-- Every cube homotopy inside an actual target simplex lifts through the
realized projection and preserves the given bottom and all boundary sides. -/
theorem principalRealization_exists_cubeLift
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : ℕ} (b : B.obj (op ⦋n⦌)) (z : A.obj (op ⦋n⦌))
    (hz : (p.app (op ⦋n⦌)).hom z = b) (d : ℕ)
    (g : C(CylinderHorn (Fin d → I) (_root_.Cube.boundary (Fin d)), |A ⋙ forget (ModuleCat R)|))
    (H : C(I × (Fin d → I), |(Δ[n] : SSet.{u})|))
    (hcomm : ∀ w, SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R))) (g w) =
      SSet.toTop.map ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b) (H w.val)) :
    ∃ L : C(I × (Fin d → I), |A ⋙ forget (ModuleCat R)|),
      (∀ w, SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R))) (L w) =
        SSet.toTop.map ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b) (H w)) ∧
      (∀ w : CylinderHorn (Fin d → I) (_root_.Cube.boundary (Fin d)), L w.val = g w) :=
  principalRealization_exists_relativeLift p b z hz (_root_.Cube.boundary (Fin d))
    (cubeHornRetraction d) (cubeHornRetraction_restrict d) g H hcomm

/-- A simplex-factored homotopy also lifts relative to any selected set of
cube sides, which is the overlap condition needed for finite-grid gluing. -/
theorem principalRealization_exists_cubeFacesLift
    {A B : SimplicialObject (ModuleCat.{u} R)} (p : A ⟶ B)
    {n : ℕ} (b : B.obj (op ⦋n⦌)) (z : A.obj (op ⦋n⦌))
    (hz : (p.app (op ⦋n⦌)).hom z = b) (d : ℕ) (faces : Set (Fin d × Bool))
    (g : C(CylinderHorn (Fin d → I) (cubeFacesBoundary d faces), |A ⋙ forget (ModuleCat R)|))
    (H : C(I × (Fin d → I), |(Δ[n] : SSet.{u})|))
    (hcomm : ∀ w, SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R))) (g w) =
      SSet.toTop.map ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b) (H w.val)) :
    ∃ L : C(I × (Fin d → I), |A ⋙ forget (ModuleCat R)|),
      (∀ w, SSet.toTop.map (Functor.whiskerRight p (forget (ModuleCat R))) (L w) =
        SSet.toTop.map ((SSet.yonedaEquiv (X := B ⋙ forget (ModuleCat R))).symm b) (H w)) ∧
      (∀ w : CylinderHorn (Fin d → I) (cubeFacesBoundary d faces), L w.val = g w) :=
  principalRealization_exists_relativeLift p b z hz (cubeFacesBoundary d faces)
    (cubeFacesHornRetraction faces) (cubeFacesHornRetraction_restrict faces) g H hcomm


end KIP126.Core.SimplicialModule
