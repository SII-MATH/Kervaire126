module

public import KIP126.Def.StableHomotopy.Implementation.Prespectrum.Fiber.LoopKernel.Data

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.Prespectrum
open CategoryTheory Topology
open scoped unitInterval
universe u
set_option backward.isDefEq.respectTransparency false

/-- The retained square identifies the target loop with the image of the
actual source-coordinate loop of a fiber-nullhomotopy. -/
theorem fiberConnectingKernelLoop_image {X Y : Prespectrum.{u}} (f : X ⟶ Y) (n r : ℕ)
    (p : GenLoop (Fin r) ((Prespectrum.loop Y).level n) ((Prespectrum.loop Y).level n).point)
    (H : ContinuousMap.HomotopyRel ((fiberConnecting f).levelLoop n r p).val
      (ContinuousMap.const _ ((fiber f).level n).point) (Cube.boundary (Fin r))) :
    GenLoop.Homotopic ((loopMap f).levelLoop n r (fiberConnectingKernelLoop f n r p H)) p := by
  let q := fiberConnectingKernelLoop f n r p H
  let F : C((I × I) × (Fin r → I),Y.level n) :=
    ⟨fun z => (H (unitInterval.symm z.1.1,z.2)).val.2 (unitInterval.symm z.1.2),
      (continuous_subtype_val.snd.comp (H.continuous.comp
        ((unitInterval.continuous_symm.comp continuous_fst.fst).prodMk continuous_snd))).eval
          (unitInterval.continuous_symm.comp continuous_fst.snd)⟩
  let rev : C((Prespectrum.loop Y).level n,(Prespectrum.loop Y).level n) :=
    ⟨Path.symm,Path.continuous_symm⟩
  have hh := KIP126.Topology.Cube.square_edges_homotopicRel F
    (rev.comp ((loopMap f).levelLoop n r q).val) (rev.comp p.val) (Cube.boundary (Fin r))
    (by
      intro t x
      change (H (unitInterval.symm 0,x)).val.2 (unitInterval.symm t) = _
      simp only [unitInterval.symm_zero]
      exact congrArg (fun z : fiberLevel f n => z.val.2 (unitInterval.symm t)) (H.apply_one x))
    (by
      intro t x
      change (H (unitInterval.symm t,x)).val.2 (unitInterval.symm 0) = _
      simp only [unitInterval.symm_zero]
      exact (H (unitInterval.symm t,x)).property.2)
    (by
      intro t x
      change (H (unitInterval.symm t,x)).val.2 (unitInterval.symm 1) =
        f.level n (H (unitInterval.symm t,x)).val.1
      simp only [unitInterval.symm_one]
      exact (H (unitInterval.symm t,x)).property.1)
    (by
      intro t x
      change (H (unitInterval.symm 1,x)).val.2 (unitInterval.symm t) = p x (unitInterval.symm t)
      simp only [unitInterval.symm_one]
      exact congrArg (fun z : fiberLevel f n => z.val.2 (unitInterval.symm t)) (H.apply_zero x))
    (by
      intro s t x hx
      change (H (unitInterval.symm s,x)).val.2 (unitInterval.symm t) = _
      have hs := congrArg (fun z : fiberLevel f n => z.val.2 (unitInterval.symm t))
        (H.eq_fst (unitInterval.symm s) hx)
      exact hs.trans (congrArg (fun a : Path (Y.level n).point (Y.level n).point =>
        a (unitInterval.symm t)) (p.property x hx)))
  have hrev (a : C((Fin r → I),(Prespectrum.loop Y).level n)) : rev.comp (rev.comp a) = a := by
    apply ContinuousMap.ext
    intro x
    exact (a x).symm_symm
  change ((loopMap f).levelLoop n r q).val.HomotopicRel p.val (Cube.boundary (Fin r))
  simpa only [hrev] using hh.comp_continuousMap rev

/-- Exactness at the actual target loop space, before passing to stable classes. -/
theorem loopMap_fiberConnecting_levelLoop_exact {X Y : Prespectrum.{u}} (f : X ⟶ Y)
    (n r : ℕ) (p : GenLoop (Fin r) ((Prespectrum.loop Y).level n) ((Prespectrum.loop Y).level n).point) :
    GenLoop.Homotopic ((fiberConnecting f).levelLoop n r p) GenLoop.const ↔
      ∃ q, GenLoop.Homotopic ((loopMap f).levelLoop n r q) p := by
  constructor
  · rintro ⟨H⟩
    exact ⟨fiberConnectingKernelLoop f n r p H,fiberConnectingKernelLoop_image f n r p H⟩
  · rintro ⟨q,hq⟩
    exact (hq.comp_continuousMap ((fiberConnecting f).level n)).symm.trans
      ⟨fiberLoopMapNullhomotopy f n r q⟩

end KIP126.StableHomotopy.Implementation.Prespectrum
