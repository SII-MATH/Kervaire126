module

public import KIP126.Def.ClassicalAdams.Suspension.Pages.Data
public import KIP126.Def.ClassicalAdams.TowerDifferential.Data

@[expose] public section


namespace KIP126.Classical.Adams.Suspension
open CategoryTheory KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} {X : C}
  (S : TowerComparison H X)

/-- Quotient descent uses precisely the already constructed cycle map. -/
theorem TowerComparison.desuspendPage_mkQ (r : ℕ) (hr : 1 ≤ r) (s t : ℤ)
    (a : adamsCycles H.unit (X⟦(1 : ℤ)⟧) r hr s t) :
    S.desuspendPage r hr s t
        ((adamsCycleBoundaries H.unit (X⟦(1 : ℤ)⟧) r hr s t).mkQ a) =
      (adamsCycleBoundaries H.unit X r hr s (t - 1)).mkQ
        (S.desuspendCycles r hr s t a) := rfl

theorem TowerComparison.desuspendPage_adamsJToPage (r : ℕ) (hr : 1 ≤ r)
    (s t : ℤ)
    (a : HomotopyGroup (t - s) (adamsTowerAt H.unit (X⟦(1 : ℤ)⟧) s)) :
    S.desuspendPage r hr s t (adamsJToPage H.unit (X⟦(1 : ℤ)⟧) r hr s t a) =
      adamsJToPage H.unit X r hr s (t - 1)
        (eqToHom (congrArg (Sphere (C := C))
          (show (t - 1) - s = (t - s) - 1 by omega)) ≫
            S.desuspendTower (t - s) s a) := by
  apply congrArg (adamsCycleBoundaries H.unit X r hr s (t - 1)).mkQ
  exact Subtype.ext (S.desuspend_adamsJ s t a)

private theorem eqMp_heq {α β γ : Sort v} (h : α = β) (a : α) (b : γ) :
    HEq (Eq.mp h a) b ↔ HEq a b := by
  cases h
  rfl

private theorem heq_eqMp {α β γ : Sort v} (h : β = γ) (a : α) (b : β) :
    HEq a (Eq.mp h b) ↔ HEq a b := by
  cases h
  rfl

omit [HasFunctorialCofiber (C := C)] in
private theorem homotopyCast_neg {Y : C} {m n : ℤ} (h : m = n)
    (a : HomotopyGroup m Y) :
    Eq.mp (congrArg (fun k => HomotopyGroup k Y) h) (-a) =
      -(Eq.mp (congrArg (fun k => HomotopyGroup k Y) h) a) := by
  subst n
  rfl

private theorem TowerComparison.desuspendTower_cast {m n : ℤ} (h : m = n)
    (s : ℤ) (a : HomotopyGroup m (adamsTowerAt H.unit (X⟦(1 : ℤ)⟧) s)) :
    S.desuspendTower n s
        (Eq.mp (congrArg (fun k => HomotopyGroup k
          (adamsTowerAt H.unit (X⟦(1 : ℤ)⟧) s)) h) a) =
      Eq.mp (congrArg (fun k => HomotopyGroup k (adamsTowerAt H.unit X s))
        (congrArg (fun k : ℤ => k - 1) h)) (S.desuspendTower m s a) := by
  subst n
  rfl

private theorem adamsJToPage_cast (r : ℕ) (hr : 1 ≤ r) (s : ℤ)
    {t t' : ℤ} (h : t = t')
    (a : HomotopyGroup (t - s) (adamsTowerAt H.unit X s)) :
    Eq.mp (congrArg (adamsPage H.unit X r hr s) h)
        (adamsJToPage H.unit X r hr s t a) =
      adamsJToPage H.unit X r hr s t'
        (Eq.mp (congrArg (fun k => HomotopyGroup k (adamsTowerAt H.unit X s))
          (congrArg (fun k => k - s) h)) a) := by
  subst t'
  rfl

/-- The actual quotient-page differential anticommutes with one
desuspension. The displayed cast only reorders the integer target degree. -/
theorem TowerComparison.desuspendPage_differential (r : ℕ) (hr : 1 ≤ r)
    (s t : ℤ) (a : adamsPage H.unit (X⟦(1 : ℤ)⟧) r hr s t) :
    Eq.mp (congrArg (adamsPage H.unit X r hr (s + r))
      (show (t + r - 1) - 1 = (t - 1) + r - 1 by omega))
      (S.desuspendPage r hr (s + r) (t + r - 1)
        (adamsDifferential H.unit (X⟦(1 : ℤ)⟧) r hr s t a)) =
      -adamsDifferential H.unit X r hr s (t - 1) (S.desuspendPage r hr s t a) := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    change Eq.mp _ (S.desuspendPage r hr (s + r) (t + r - 1)
      (adamsDifferentialValue H.unit (X⟦(1 : ℤ)⟧) r hr s t a)) =
        -adamsDifferentialValue H.unit X r hr s (t - 1) (S.desuspendCycles r hr s t a)
    let b := adamsCycleLift H.unit (X⟦(1 : ℤ)⟧) r hr s t a
    let e := eqToHom (congrArg (Sphere (C := C))
      (show (t - 1) - s - 1 = (t - s - 1) - 1 by omega))
    have hb : adamsI H.unit (X⟦(1 : ℤ)⟧) (t - s - 1)
        (s + 1) (s + r) (by omega) b = adamsK H.unit (X⟦(1 : ℤ)⟧) s t a :=
      adamsCycleLift_spec H.unit (X⟦(1 : ℤ)⟧) r hr s t a
    have hd : adamsI H.unit X ((t - 1) - s - 1) (s + 1) (s + r) (by omega)
        (-(e ≫ S.desuspendTower (t - s - 1) (s + r) b)) =
          adamsK H.unit X s (t - 1) (S.desuspendCycles r hr s t a) := by
      change (-(e ≫ S.desuspendTower (t - s - 1) (s + r) b)) ≫
        adamsTowerMapAt H.unit X (s + 1) (s + r) _ = _
      rw [Preadditive.neg_comp, Category.assoc]
      change -(e ≫ adamsI H.unit X ((t - s - 1) - 1) (s + 1) (s + r) _
        (S.desuspendTower (t - s - 1) (s + r) b)) = _
      rw [← S.desuspend_adamsI, hb]
      exact (S.desuspend_adamsK s t a).symm
    rw [adamsDifferentialValue_eq_of_lift H.unit X r hr s (t - 1)
      (S.desuspendCycles r hr s t a) _ hd]
    change Eq.mp _ (S.desuspendPage r hr (s + r) (t + r - 1)
      (adamsJToPage H.unit (X⟦(1 : ℤ)⟧) r hr (s + r) (t + r - 1)
        (adamsDifferentialLift H.unit (X⟦(1 : ℤ)⟧) r hr s t a))) = _
    rw [S.desuspendPage_adamsJToPage, adamsJToPage_cast,
      homotopyCast_neg, map_neg, neg_neg]
    apply congrArg (adamsJToPage H.unit X r hr (s + r) ((t - 1) + r - 1))
    unfold adamsDifferentialLift
    rw [S.desuspendTower_cast]
    all_goals try omega
    simp only [e, b]
    apply eq_of_heq
    simp only [eqMp_heq, heq_eqMp, eqToHom_comp_heq_iff,
      heq_eqToHom_comp_iff]
    rfl

/-- One desuspension preserves every finite and infinite cycle condition. -/
theorem TowerComparison.desuspendCycles_mem_cycleSubmodule (s t : ℤ) (r : WithTop ℕ)
    {a : adamsCycleAmbient H.unit (X⟦(1 : ℤ)⟧) s t}
    (ha : a ∈ adamsCycleSubmodule H.unit (X⟦(1 : ℤ)⟧) s t r) :
    S.desuspendCycles 2 (Nat.le_succ 1) s t a ∈
      adamsCycleSubmodule H.unit X s (t - 1) r := by
  rcases eq_or_ne r ⊤ with rfl | hr
  · simp only [adamsCycleSubmodule, Submodule.mem_iInf] at ha ⊢
    intro m
    exact S.desuspendFirstPage_mem_cycles (m + 2) (by omega) s t (ha m)
  · lift r to ℕ using hr
    exact S.desuspendFirstPage_mem_cycles (r + 2) (by omega) s t ha

/-- One desuspension preserves every finite and infinite boundary condition. -/
theorem TowerComparison.desuspendCycles_mem_boundarySubmodule (s t : ℤ) (r : WithTop ℕ)
    {a : adamsCycleAmbient H.unit (X⟦(1 : ℤ)⟧) s t}
    (ha : a ∈ adamsBoundarySubmodule H.unit (X⟦(1 : ℤ)⟧) s t r) :
    S.desuspendCycles 2 (Nat.le_succ 1) s t a ∈
      adamsBoundarySubmodule H.unit X s (t - 1) r := by
  rcases eq_or_ne r ⊤ with rfl | hr
  · have hmap : (adamsBoundarySubmodule H.unit (X⟦(1 : ℤ)⟧) s t ⊤).map
        (S.desuspendCycles 2 (Nat.le_succ 1) s t) ≤ adamsBoundarySubmodule H.unit X s (t - 1) ⊤ := by
      simp only [adamsBoundarySubmodule, Submodule.map_iSup]
      refine iSup_le fun m => ?_
      refine le_trans ?_ (le_iSup (fun n => adamsFiniteBoundarySubmodule H.unit X s (t - 1) n) m)
      rintro _ ⟨b, hb, rfl⟩
      exact S.desuspendFirstPage_mem_boundaries (m + 2) (by omega) s t hb
    exact hmap ⟨a, ha, rfl⟩
  · lift r to ℕ using hr
    exact S.desuspendFirstPage_mem_boundaries (r + 2) (by omega) s t ha

end
end KIP126.Classical.Adams.Suspension
