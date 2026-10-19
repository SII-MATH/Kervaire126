/-
  KIPBase.Synthetic.FESS
  Blueprint §4, Definition `def:synthetic-extension-ss`.

  This file is the user-facing wrapper around the canonical synthetic Adams
  convergence data.  For an actual synthetic map `f : X ⟶ Y`, no auxiliary
  convergence package has to be supplied: it is obtained functorially from
  `synAdamsConvergence` and fed to the unbounded extension construction.
-/
import KIPBase.Synthetic.ExtensionSS

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  KIPBase.SpectralSequence

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/- The unbounded construction uses wide subobject limits in `AddCommGrpCat`.
The objects are small, so universe lifting supplies the required instance. -/
noncomputable local instance syntheticFESSAddCommGrpWellPoweredOne :
    WellPowered.{1} AddCommGrpCat.{0} where
  subobject_small := fun _ => by infer_instance

/-- The canonical synthetic `f`-extension spectral sequence.

The parameter `degree = (stem, weight)` is the fixed abutment bidegree.  The
internal bidegree is `(s,k)`, with `k = 1` the source column and `k = 0` the
target column. -/
noncomputable def syntheticFESS {X Y : Syn} (f : X ⟶ Y) :
    ℤ × ℤ → SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ) :=
  fun degree => (syntheticExtensionCoreDataOfMap f).ess degree

/-- The canonical synthetic `f`-ESS with weight and stem displayed as
separate arguments. -/
noncomputable def syntheticFESSAtWeight {X Y : Syn} (f : X ⟶ Y)
    (weight stem : ℤ) :
    SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ) :=
  syntheticFESS f (stem, weight)

@[simp]
theorem syntheticFESS_r₀ {X Y : Syn} (f : X ⟶ Y) (degree : ℤ × ℤ) :
    (syntheticFESS f degree).r₀ = 0 :=
  rfl

@[simp]
theorem syntheticFESS_diffDeg {X Y : Syn} (f : X ⟶ Y)
    (degree : ℤ × ℤ) (r : ℤ) :
    (syntheticFESS f degree).diffDeg r = (r, -1) :=
  rfl

/-- The two nonzero columns of the zeroth synthetic extension page, written
in the Blueprint tridegree `(s,t,w)`.  The fixed abutment degree is
`(t-s,w)`. -/
noncomputable def syntheticFESSE0 {X Y : Syn} (f : X ⟶ Y)
    (s t w : ℤ) : AddCommGrpCat.{0} :=
  (syntheticFESS f (t - s, w)).Page 0 (s, 1) ⊞
    (syntheticFESS f (t - s, w)).Page 0 (s, 0)

/-- The source and target synthetic Adams limiting terms occurring in the
Blueprint formula for the zeroth `f`-extension page. -/
noncomputable def syntheticFESSEInftySum {X Y : Syn} (_f : X ⟶ Y)
    (s t w : ℤ) : AddCommGrpCat.{0} :=
  ((SynAdamsSS Syn X).ssData (s, t, w)).eInfty ⊞
    ((SynAdamsSS Syn Y).ssData (s, t, w)).eInfty

/-- Blueprint §4 zeroth-page identification

`{}^fE₀^{s,t,w} ≅ E∞^{s,t,w}(X) ⊕ E∞^{s,t,w}(Y)`. -/
noncomputable def syntheticFESSE0Iso {X Y : Syn} (f : X ⟶ Y)
    (s t w : ℤ) :
    syntheticFESSE0 f s t w ≅ syntheticFESSEInftySum f s t w := by
  let data := syntheticExtensionCoreDataOfMap f
  have hindex : syntheticAdamsIndex s (t - s, w) = (s, t, w) := by
    ext <;> simp [syntheticAdamsIndex]
  exact data.e0PageIso s (t - s, w) ≪≫
    biprod.mapIso
      (eqToIso (congrArg
        (fun k => ((SynAdamsSS Syn X).ssData k).eInfty) hindex))
      (eqToIso (congrArg
        (fun k => ((SynAdamsSS Syn Y).ssData k).eInfty) hindex))

/-- The page-`r` differential from the source column to the target column.
In Blueprint tridegrees its source is `(s,t,w)` and its target is
`(s+r,t+r,w)`. -/
noncomputable def syntheticFESSDifferential {X Y : Syn} (f : X ⟶ Y)
    (r : ℕ) (s t w : ℤ) :
    (syntheticFESS f (t - s, w)).Page (r : ℤ) (s, 1) ⟶
      (syntheticFESS f (t - s, w)).Page (r : ℤ) (s + r, 0) := by
  change
    ((syntheticFESS f (t - s, w)).ssData (s, 1)).page r ⟶
      ((syntheticFESS f (t - s, w)).ssData (s + r, 0)).page r
  simpa using (syntheticFESS f (t - s, w)).d (r : ℤ) (s, 1)

/-- Trigraded form of the differential degree: the synthetic `f`-ESS raises
both Adams coordinates by `r` and preserves weight. -/
theorem syntheticFESS_d_tridegree (s t w r : ℤ) :
    (s, t, w) + syntheticESSDiffDegree r = (s + r, t + r, w) := by
  simp [syntheticESSDiffDegree]

end KIPBase.Synthetic
