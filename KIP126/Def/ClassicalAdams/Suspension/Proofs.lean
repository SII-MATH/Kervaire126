module

public import KIP126.Def.ClassicalAdams.Suspension.Data
public import KIP126.Def.StableHomotopy.Context.Suspension.Proofs
public import KIP126.Def.StableHomotopy.Context.Connecting.Desuspension.Proofs

@[expose] public section


/-!
# Desuspension of the actual Adams exact couple

These formulas follow from the tower and layer squares in `TowerComparison`.
All integer tower stages and homotopy degrees are retained. In particular,
the connecting map anticommutes with one desuspension.
-/

namespace KIP126.Classical.Adams.Suspension

open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology

universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {X : C}
  (S : TowerComparison H X)

/-- Every tower transition commutes with the specified desuspension. -/
theorem TowerComparison.desuspend_adamsI (n s t : ℤ) (hst : s ≤ t)
    (a : HomotopyGroup n (adamsTowerAt H.unit (X⟦(1 : ℤ)⟧) t)) :
    S.desuspendTower n s (adamsI H.unit (X⟦(1 : ℤ)⟧) n s t hst a) =
      adamsI H.unit X (n - 1) s t hst (S.desuspendTower n t a) := by
  change homotopyDesuspend (adamsTowerAt H.unit X s) n
      ((a ≫ adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s t hst) ≫ (S.tower s).hom) =
    homotopyDesuspend (adamsTowerAt H.unit X t) n (a ≫ (S.tower t).hom) ≫
      adamsTowerMapAt H.unit X s t hst
  rw [Category.assoc, ← S.tower_comm, ← Category.assoc,
    homotopyDesuspend_postcompose]

/-- The actual cofiber inclusion commutes with desuspension, including the
displayed reindexing of its domain sphere. -/
theorem TowerComparison.desuspend_adamsJ (s t : ℤ)
    (a : HomotopyGroup (t - s) (adamsTowerAt H.unit (X⟦(1 : ℤ)⟧) s)) :
    S.desuspendFirstPage s t (adamsJ H.unit (X⟦(1 : ℤ)⟧) s t a) =
      adamsJ H.unit X s (t - 1)
        (eqToHom (congrArg (Sphere (C := C))
          (show (t - 1) - s = (t - s) - 1 by omega)) ≫
            S.desuspendTower (t - s) s a) := by
  change _ ≫ homotopyDesuspend (adamsLayerAt H.unit X s) (t - s)
      ((a ≫ HasFunctorialCofiber.cofibι _) ≫ (S.layer s).hom) =
    (_ ≫ homotopyDesuspend (adamsTowerAt H.unit X s) (t - s)
      (a ≫ (S.tower s).hom)) ≫ HasFunctorialCofiber.cofibι _
  rw [Category.assoc a, S.layer_inclusion, ← Category.assoc,
    homotopyDesuspend_postcompose, Category.assoc]

omit [HasFunctorialCofiber (C := C)] in
private theorem homotopyDesuspend_transport {Y : C} {m n : ℤ} (h : m = n)
    (a : HomotopyGroup n (Y⟦(1 : ℤ)⟧)) :
    homotopyDesuspend Y m (eqToHom (congrArg (Sphere (C := C)) h) ≫ a) =
      eqToHom (congrArg (Sphere (C := C)) (congrArg (fun k : ℤ => k - 1) h)) ≫
        homotopyDesuspend Y n a := by
  subst m
  simp only [eqToHom_refl, Category.id_comp]

private theorem TowerComparison.desuspend_adamsK_raw (s t : ℤ)
    (a : adamsE1 H.unit (X⟦(1 : ℤ)⟧) s t) :
    S.desuspendTower (t - s - 1) (s + 1)
        (adamsK H.unit (X⟦(1 : ℤ)⟧) s t a) =
      -homotopyDesuspend (adamsTowerAt H.unit X (s + 1)) (t - s - 1)
        (homotopyDesuspend (adamsLayerAt H.unit X s) (t - s)
          (a ≫ (S.layer s).hom) ≫
            HasFunctorialCofiber.cofibδ
              (adamsTowerMapAt H.unit X s (s + 1) (by omega))) := by
  have hc : (S.layer s).hom ≫ (HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit X s (s + 1) (by omega)))⟦(1 : ℤ)⟧' =
      -(HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s (s + 1) (by omega)) ≫
          (S.tower (s + 1)).hom⟦(1 : ℤ)⟧') := by
    have h := S.layer_connecting s
    rw [shiftFunctorComm_eq_refl] at h
    change (S.layer s).hom ≫ (HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit X s (s + 1) (by omega)))⟦(1 : ℤ)⟧' ≫ 𝟙 _ = _ at h
    simpa only [Category.comp_id] using h
  have hc' : HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s (s + 1) (by omega)) ≫
        (S.tower (s + 1)).hom⟦(1 : ℤ)⟧' =
      -((S.layer s).hom ≫ (HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit X s (s + 1) (by omega)))⟦(1 : ℤ)⟧') := by
    rw [hc, neg_neg]
  change homotopyDesuspend (adamsTowerAt H.unit X (s + 1)) (t - s - 1)
    (connectingHomomorphism (HoCofiberSequence.ofMorphism
      (adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s (s + 1) (by omega)))
        (t - s) a ≫ (S.tower (s + 1)).hom) = _
  rw [connectingHomomorphism_eq_desuspend]
  change homotopyDesuspend (adamsTowerAt H.unit X (s + 1)) (t - s - 1)
    (homotopyDesuspend (adamsTowerAt H.unit (X⟦(1 : ℤ)⟧) (s + 1)) (t - s)
      (a ≫ HasFunctorialCofiber.cofibδ
        (adamsTowerMapAt H.unit (X⟦(1 : ℤ)⟧) s (s + 1) (by omega))) ≫
          (S.tower (s + 1)).hom) = _
  rw [← homotopyDesuspend_postcompose, Category.assoc a, hc',
    Preadditive.comp_neg, map_neg, ← Category.assoc,
    homotopyDesuspend_postcompose, map_neg]

/-- One desuspension anticommutes with the actual connecting map. The
domain transport retains the full integer grading and no pagewise
differential-compatibility hypothesis is added. -/
theorem TowerComparison.desuspend_adamsK (s t : ℤ)
    (a : adamsE1 H.unit (X⟦(1 : ℤ)⟧) s t) :
    adamsK H.unit X s (t - 1) (S.desuspendFirstPage s t a) =
      -(eqToHom (congrArg (Sphere (C := C))
        (show (t - 1) - s - 1 = (t - s - 1) - 1 by omega)) ≫
          S.desuspendTower (t - s - 1) (s + 1)
            (adamsK H.unit (X⟦(1 : ℤ)⟧) s t a)) := by
  rw [S.desuspend_adamsK_raw, Preadditive.comp_neg, neg_neg]
  change connectingHomomorphism (HoCofiberSequence.ofMorphism
      (adamsTowerMapAt H.unit X s (s + 1) (by omega))) ((t - 1) - s)
    (eqToHom (congrArg (Sphere (C := C))
      (show (t - 1) - s = (t - s) - 1 by omega)) ≫
        homotopyDesuspend (adamsLayerAt H.unit X s) (t - s)
          (a ≫ (S.layer s).hom)) = _
  rw [connectingHomomorphism_eq_desuspend]
  change homotopyDesuspend (adamsTowerAt H.unit X (s + 1)) ((t - 1) - s)
    ((eqToHom (congrArg (Sphere (C := C))
      (show (t - 1) - s = (t - s) - 1 by omega)) ≫
        homotopyDesuspend (adamsLayerAt H.unit X s) (t - s)
          (a ≫ (S.layer s).hom)) ≫ HasFunctorialCofiber.cofibδ
            (adamsTowerMapAt H.unit X s (s + 1) (by omega))) = _
  rw [Category.assoc,
    homotopyDesuspend_transport (show (t - 1) - s = (t - s) - 1 by omega)]

/-- The negative desuspended lift witnesses preservation of every finite
cycle submodule; its sign is forced by the connecting-square formula. -/
theorem TowerComparison.desuspendFirstPage_mem_cycles (r : ℕ) (hr : 1 ≤ r)
    (s t : ℤ) {a : adamsE1 H.unit (X⟦(1 : ℤ)⟧) s t}
    (ha : a ∈ adamsCycles H.unit (X⟦(1 : ℤ)⟧) r hr s t) :
    S.desuspendFirstPage s t a ∈ adamsCycles H.unit X r hr s (t - 1) := by
  obtain ⟨b, hb⟩ := ha
  let e := eqToHom (congrArg (Sphere (C := C))
    (show (t - 1) - s - 1 = (t - s - 1) - 1 by omega))
  refine ⟨-(e ≫ S.desuspendTower (t - s - 1) (s + r) b), ?_⟩
  change (-(e ≫ S.desuspendTower (t - s - 1) (s + r) b)) ≫
    adamsTowerMapAt H.unit X (s + 1) (s + r) _ = _
  rw [Preadditive.neg_comp, Category.assoc]
  change -(e ≫ adamsI H.unit X ((t - s - 1) - 1) (s + 1) (s + r) _
    (S.desuspendTower (t - s - 1) (s + r) b)) = _
  rw [← S.desuspend_adamsI, hb]
  exact (S.desuspend_adamsK s t a).symm

/-- Boundaries use the positive desuspended tower witness. Its vanishing
transition is preserved by I and its layer image by J. -/
theorem TowerComparison.desuspendFirstPage_mem_boundaries (r : ℕ) (hr : 1 ≤ r)
    (s t : ℤ) {a : adamsE1 H.unit (X⟦(1 : ℤ)⟧) s t}
    (ha : a ∈ adamsBoundaries H.unit (X⟦(1 : ℤ)⟧) r hr s t) :
    S.desuspendFirstPage s t a ∈ adamsBoundaries H.unit X r hr s (t - 1) := by
  obtain ⟨b, hb, rfl⟩ := ha
  let e := eqToHom (congrArg (Sphere (C := C))
    (show (t - 1) - s = (t - s) - 1 by omega))
  refine ⟨e ≫ S.desuspendTower (t - s) s b, ?_, ?_⟩
  · change (e ≫ S.desuspendTower (t - s) s b) ≫
      adamsTowerMapAt H.unit X (s - r + 1) s _ = 0
    rw [Category.assoc]
    change e ≫ adamsI H.unit X ((t - s) - 1) (s - r + 1) s _
      (S.desuspendTower (t - s) s b) = 0
    rw [← S.desuspend_adamsI, show adamsI H.unit (X⟦(1 : ℤ)⟧)
      (t - s) (s - r + 1) s _ b = 0 from hb, map_zero, Limits.comp_zero]
  · exact (S.desuspend_adamsJ s t b).symm

end
end KIP126.Classical.Adams.Suspension
