import KIPBase.Synthetic.Adams
import KIPBase.Synthetic.LambdaE2
import KIPBase.Synthetic.Nu
import KIPBase.StableHomotopy.Adams

/-!
# Adams comparison from E₂ and lambda inversion

The input is an actual inversion comparison, compatible with E₂, lambda,
and passage to homology. No later-page bijectivity or unlocalized
differential formula is an input. The free range is proved by induction.
-/

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v u' v'

set_option maxHeartbeats 1000000

/-- An elementwise presentation of the middle homology of two successive
differentials. The projection is onto, and its kernel is the incoming image. -/
structure AdamsPageHomology
    {A B C H : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup H] (f : A →+ B) (g : B →+ C) where
  π : g.ker →+ H
  surjective : Function.Surjective π
  exact : ∀ z : g.ker, π z = 0 ↔ ∃ a, f a = z.val

namespace AdamsPageHomology

variable {A B C H A' B' C' H' : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup H]
  [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] [AddCommGroup H']
  {f : A →+ B} {g : B →+ C} {f' : A' →+ B'} {g' : B' →+ C'}

theorem surjective_map
    (S : AdamsPageHomology f g (H := H))
    (T : AdamsPageHomology f' g' (H := H'))
    (qB : B →+ B') (qC : C →+ C') (qH : H →+ H')
    (comm : ∀ b, qC (g b) = g' (qB b))
    (next : ∀ (z : g.ker) (z' : g'.ker), qB z.val = z'.val →
      qH (S.π z) = T.π z')
    (hB : Function.Surjective qB) (hC : Function.Injective qC) :
    Function.Surjective qH := by
  intro y
  obtain ⟨z', hz'⟩ := T.surjective y
  obtain ⟨b, hb⟩ := hB z'.val
  have hgb : g b = 0 := by
    apply hC
    rw [comm, hb, z'.property, map_zero]
  exact ⟨S.π ⟨b, hgb⟩, (next ⟨b, hgb⟩ z' hb).trans hz'⟩

theorem injective_map
    (S : AdamsPageHomology f g (H := H))
    (T : AdamsPageHomology f' g' (H := H'))
    (qA : A →+ A') (qB : B →+ B') (qC : C →+ C') (qH : H →+ H')
    (commIn : ∀ a, qB (f a) = f' (qA a))
    (commOut : ∀ b, qC (g b) = g' (qB b))
    (next : ∀ (z : g.ker) (z' : g'.ker), qB z.val = z'.val →
      qH (S.π z) = T.π z')
    (hA : Function.Surjective qA) (hB : Function.Injective qB) :
    Function.Injective qH := by
  have hzero : ∀ h, qH h = 0 → h = 0 := by
    intro h hh
    obtain ⟨z, hz⟩ := S.surjective h
    have hg' : g' (qB z.val) = 0 := by
      rw [← commOut, z.property, map_zero]
    let z' : g'.ker := ⟨qB z.val, hg'⟩
    have hz' : T.π z' = 0 := by
      rw [← next z z' rfl, hz, hh]
    obtain ⟨a', ha'⟩ := (T.exact z').mp hz'
    obtain ⟨a, ha⟩ := hA a'
    have hfa : f a = z.val := by
      apply hB
      rw [commIn, ha]
      exact ha'
    exact hz.symm.trans ((S.exact z).mpr ⟨a, hfa⟩)
  intro x y h
  exact sub_eq_zero.mp (hzero (x - y) (by rw [map_sub, h, sub_self]))

end AdamsPageHomology

variable (𝒮 : Type u) [StableHomotopy.StableHomotopyCategory.{u, v} 𝒮]
variable (Syn : Type u') [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn] [Pretriangulated Syn] [SyntheticCategory Syn]

/-- Synthetic differential with the AIM target indices displayed. -/
noncomputable def synAdamsDifferentialNormalized (Y : Syn) (r s t w : ℤ) :
    (SynAdamsSS Syn Y).Page r (s, t, w) ⟶
      (SynAdamsSS Syn Y).Page r (s + r, t + r - 1, w) :=
  (SynAdamsSS Syn Y).d r (s, t, w) ≫
    eqToHom (congrArg (fun k => (SynAdamsSS Syn Y).Page r k) (by
      rw [synAdamsSS_diffDeg]
      ext <;> dsimp <;> omega))

/-- Classical differential with the AIM target indices displayed. -/
noncomputable def classicalAdamsDifferentialNormalized (X : 𝒮) (r s t : ℤ) :
    (StableHomotopy.AdamsSS 𝒮 X).Page r (s, t) ⟶
      (StableHomotopy.AdamsSS 𝒮 X).Page r (s + r, t + r - 1) :=
  (StableHomotopy.AdamsSS 𝒮 X).d r (s, t) ≫
    eqToHom (congrArg (fun k => (StableHomotopy.AdamsSS 𝒮 X).Page r k) (by
      rw [StableHomotopy.adamsSS_diffDeg]
      ext <;> dsimp [StableHomotopy.adamsDiffDeg] <;> omega))

/-- Actual iterated lambda map with its final weight displayed. -/
noncomputable def synAdamsLambdaPowNormalized (Y : Syn) (n : ℕ)
    (r s t w : ℤ) :
    (SynAdamsSS Syn Y).Page r (s, t, w) ⟶
      (SynAdamsSS Syn Y).Page r (s, t, w - (n : ℤ)) :=
  (synAdamsSS_zlambda_module Syn Y).lambdaPow n r (s, t, w) ≫
    eqToHom (congrArg (fun k => (SynAdamsSS Syn Y).Page r k) (by
      rw [SynAdamsLambdaModule.lambdaIndex_eq]
      ext <;> simp [sub_eq_add_neg]))

noncomputable def synAdamsIncomingDifferentialNormalized (Y : Syn) (r s t w : ℤ) :
    (SynAdamsSS Syn Y).Page r (s - r, t - r + 1, w) ⟶
      (SynAdamsSS Syn Y).Page r (s, t, w) :=
  synAdamsDifferentialNormalized Syn Y r (s-r) (t-r+1) w ≫
    eqToHom (congrArg (fun k => (SynAdamsSS Syn Y).Page r k) (by
      ext <;> dsimp <;> omega))

noncomputable def classicalAdamsIncomingDifferentialNormalized (X : 𝒮) (r s t : ℤ) :
    (StableHomotopy.AdamsSS 𝒮 X).Page r (s-r, t-r+1) ⟶
      (StableHomotopy.AdamsSS 𝒮 X).Page r (s, t) :=
  classicalAdamsDifferentialNormalized 𝒮 X r (s-r) (t-r+1) ≫
    eqToHom (congrArg (fun k => (StableHomotopy.AdamsSS 𝒮 X).Page r k) (by
      ext <;> dsimp <;> omega))

/-- Explicit form of the two comparison inputs. The homology projections
refer to the actual next Adams pages. No later-page freeness is assumed.
This structure is a parameter, not a globally postulated instance. -/
structure NuAdamsLambdaInversionComparison (X : 𝒮) where
  map : ∀ (r : ℕ) (s t w : ℤ),
    (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s,t,w) →+
      (StableHomotopy.AdamsSS 𝒮 X).Page (r : ℤ) (s,t)
  e2 : ∀ s t w, w ≤ t → Function.Bijective (map 2 s t w)
  comm_d : ∀ (r : ℕ), 2 ≤ r → ∀ s t w z,
    map r (s+r) (t+r-1) w
        ((synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X) r s t w).hom z) =
      (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom (map r s t w z)
  comm_in : ∀ (r : ℕ), 2 ≤ r → ∀ s t w z,
    map r s t w
        ((synAdamsIncomingDifferentialNormalized Syn ((nu 𝒮 Syn).obj X) r s t w).hom z) =
      (classicalAdamsIncomingDifferentialNormalized 𝒮 X r s t).hom
        (map r (s-r) (t-r+1) w z)
  lambda : ∀ (r : ℕ), 2 ≤ r → ∀ (s t w : ℤ) (n : ℕ) z,
    map r s t (w-n)
        ((synAdamsLambdaPowNormalized Syn ((nu 𝒮 Syn).obj X) n r s t w).hom z) =
      map r s t w z
  syntheticHomology : ∀ (r : ℕ), 2 ≤ r → ∀ s t w,
    AdamsPageHomology
      (synAdamsIncomingDifferentialNormalized Syn ((nu 𝒮 Syn).obj X) r s t w).hom
      (synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X) r s t w).hom
      (H := (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page ((r+1 : ℕ) : ℤ) (s,t,w))
  classicalHomology : ∀ (r : ℕ), 2 ≤ r → ∀ s t,
    AdamsPageHomology
      (classicalAdamsIncomingDifferentialNormalized 𝒮 X r s t).hom.toAddMonoidHom
      (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom.toAddMonoidHom
      (H := (StableHomotopy.AdamsSS 𝒮 X).Page ((r+1 : ℕ) : ℤ) (s,t))
  next : ∀ (r : ℕ) (hr : 2 ≤ r) (s t w : ℤ)
    (z : (synAdamsDifferentialNormalized Syn ((nu 𝒮 Syn).obj X) r s t w).hom.ker)
    (z' : (classicalAdamsDifferentialNormalized 𝒮 X r s t).hom.toAddMonoidHom.ker),
    map r s t w z.val = z'.val →
      map (r+1) s t w ((syntheticHomology r hr s t w).π z) =
        (classicalHomology r hr s t).π z'

namespace NuAdamsLambdaInversionComparison

variable {𝒮 Syn} {X : 𝒮} (P : NuAdamsLambdaInversionComparison 𝒮 Syn X)

/-- E₂ and homology naturality imply surjectivity in all supported weights
and bijectivity in the free tail, without a rigidity axiom. -/
theorem page_comparison (r : ℕ) (hr : 2 ≤ r) :
    ∀ s t w, (w ≤ t → Function.Surjective (P.map r s t w)) ∧
      ((r : ℤ)-2 ≤ t-w → Function.Bijective (P.map r s t w)) := by
  induction r, hr using Nat.le_induction with
  | base =>
    intro s t w
    constructor
    · exact fun h => (P.e2 s t w h).2
    · intro h
      exact P.e2 s t w (by omega)
  | succ r hr ih =>
    intro s t w
    have hsurj (hw : w ≤ t) : Function.Surjective (P.map (r+1) s t w) := by
      apply AdamsPageHomology.surjective_map
        (P.syntheticHomology r hr s t w) (P.classicalHomology r hr s t)
        (P.map r s t w) (P.map r (s+r) (t+r-1) w) (P.map (r+1) s t w)
        (P.comm_d r hr s t w) (P.next r hr s t w)
      · exact (ih s t w).1 hw
      · exact ((ih (s+r) (t+r-1) w).2 (by omega)).1
    constructor
    · exact hsurj
    · intro hw
      refine ⟨?_, hsurj (by omega)⟩
      apply AdamsPageHomology.injective_map
        (P.syntheticHomology r hr s t w) (P.classicalHomology r hr s t)
        (P.map r (s-r) (t-r+1) w) (P.map r s t w)
        (P.map r (s+r) (t+r-1) w) (P.map (r+1) s t w)
        (P.comm_in r hr s t w) (P.comm_d r hr s t w) (P.next r hr s t w)
      · exact (ih (s-r) (t-r+1) w).1 (by omega)
      · exact ((ih s t w).2 (by omega)).1

/-- The free-tail lift constructed by inverting the proved comparison. -/
noncomputable def classicalLift (r : ℕ) (hr : 2 ≤ r) (s t w : ℤ)
    (hw : (r : ℤ)-2 ≤ t-w) :
    (StableHomotopy.AdamsSS 𝒮 X).Page (r : ℤ) (s,t) →+
      (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s,t,w) :=
  (AddEquiv.ofBijective (P.map r s t w) ((P.page_comparison r hr s t w).2 hw)).symm.toAddMonoidHom

@[simp] theorem map_classicalLift (r : ℕ) (hr : 2 ≤ r) (s t w : ℤ)
    (hw : (r : ℤ)-2 ≤ t-w) (x) :
    P.map r s t w (P.classicalLift r hr s t w hw x) = x :=
  (AddEquiv.ofBijective (P.map r s t w)
    ((P.page_comparison r hr s t w).2 hw)).apply_symm_apply x

theorem map_weight_transport (r : ℕ) (s t w w' : ℤ) (h : w = w')
    (z : (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s,t,w)) :
    P.map r s t w' ((eqToHom (congrArg
      (fun v => (SynAdamsSS Syn ((nu 𝒮 Syn).obj X)).Page (r : ℤ) (s,t,v)) h)).hom z)
      = P.map r s t w z := by
  subst w'
  rfl

end NuAdamsLambdaInversionComparison
end KIPBase.Synthetic
