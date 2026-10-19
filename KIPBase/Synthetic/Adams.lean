/-
  KIPBase.Synthetic.Adams
  §3.3 Synthetic Adams spectral sequence — functor from Syn to 3-graded
  converging SS (grading rule per §3.6), Adams filtration on π_{*,*}X,
  convergence, Z[λ]-module spectral sequence

  Blueprint references:
  - `prerequisites.tex` §0.3.3 (Axiom `prereq:ax:syn-adams-ss`)
  - `synthetic-spectra.tex` §3 (synthetic Adams SS definition, Z[λ]-module structure)
  - `synthetic-extensions.tex` §4 (applications to extension spectral sequences)
  - KIP Appendix A, Corollary A.9, A.11 (convergence of synthetic Adams SS)
-/
import KIPBase.Mathlib
import KIPBase.Synthetic.Sphere
import KIPBase.SpectralSequence.Convergence

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u v

variable {Syn : Type u} [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-! ### Synthetic Adams spectral sequence (3-graded)

The synthetic Adams SS is a trigraded spectral sequence with indices (s, t, w):
- s = Adams filtration degree
- t = stem + filtration degree
- w = weight (synthetic grading)
Differentials: d_r : E_r^{s,t,w} → E_r^{s+r, t+r-1, w}. -/

/-- KIP Appendix A (Axiom `prereq:ax:syn-adams-ss`), cf. `synthetic-spectra.tex` §3:
    The synthetic Adams spectral sequence for an object X in Syn.
    This is a spectral sequence with trigrading (s, t, w) ∈ ℤ³,
    converging to π_{*,*}(X) with Adams filtration. -/
axiom SynAdamsSS (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) :
    SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ × ℤ)

/-- KIP Appendix A (Axiom `prereq:ax:syn-adams-ss`), cf. `synthetic-spectra.tex` §3:
    The differential degree for the synthetic Adams SS:
    d_r has degree (r, r-1, 0) in the trigrading (s, t, w).
    The weight component is zero, reflecting that differentials preserve weight. -/
axiom synAdamsSS_diffDeg (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) (r : ℤ) :
    (SynAdamsSS Syn X).diffDeg r = (r, r - 1, 0)

/-- KIP Appendix A (Axiom `prereq:ax:syn-adams-ss`), cf. `synthetic-spectra.tex` §3:
    The starting page for the synthetic Adams SS is r₀ = 2,
    matching the classical Adams spectral sequence. -/
axiom synAdamsSS_r0 (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) :
    (SynAdamsSS Syn X).r₀ = 2

/-! ### Adams filtration on π_{*,*} -/

/-- KIP §3 (`prereq:def:adams-filtration` in synthetic setting), cf. `synthetic-spectra.tex`:
    The Adams filtration on bigraded homotopy groups π_{m,n}(X).
    This is a decreasing filtration F^s π_{m,n}(X) ⊇ F^{s+1} π_{m,n}(X) ⊇ ⋯
    arising from the synthetic Adams SS. Elements in F^s detect classes
    on the E_∞-page with filtration ≥ s. -/
axiom synAdamsFiltration (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) (m n : ℤ) (s : ℤ) :
    AddSubgroup (Smn (Syn := Syn) m n ⟶ X)

/-- KIP §3 (`prereq:def:adams-filtration`): The filtration is decreasing: F^{s+1} ⊆ F^s.
    This is a standard property of Adams filtrations (cf. `prereq:rem:decreasing-filtration`). -/
axiom synAdamsFiltration_mono (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) (m n : ℤ) (s : ℤ) :
    synAdamsFiltration Syn X m n (s + 1) ≤ synAdamsFiltration Syn X m n s

/-! ### Convergence -/

/-- Fully typed convergence data for the synthetic Adams spectral sequence.
The abstract small abutment objects are identified with the actual represented
bigraded homotopy groups, and every filtration subobject is identified with
the declared Adams-filtration subgroup.  The explicit equivalences avoid a
false universe-level definitional equality between these two presentations. -/
structure SynAdamsConvergenceData (X : Syn) where
  abutment : ℤ × ℤ → AddCommGrpCat.{0}
  filtration : Filtration abutment
  convergence : Convergence (SynAdamsSS Syn X) abutment filtration
  reindex_eq : convergence.reindex =
    fun ⟨s, t, w⟩ => (s, (t - s, w))
  abutmentEquiv : ∀ degree : ℤ × ℤ,
    ↑(abutment degree) ≃+ (Smn (Syn := Syn) degree.1 degree.2 ⟶ X)
  filtrationEquiv : ∀ (s : ℤ) (degree : ℤ × ℤ),
    ↑(Subobject.underlying.obj (filtration.F s degree)) ≃+
      synAdamsFiltration Syn X degree.1 degree.2 s
  filtrationEquiv_comm : ∀ (s : ℤ) (degree : ℤ × ℤ)
      (a : ↑(Subobject.underlying.obj (filtration.F s degree))),
    abutmentEquiv degree ((filtration.F s degree).arrow.hom a) =
      (filtrationEquiv s degree a).1

/-- Synthetic Adams converges to the actual represented homotopy groups with
the actual Adams filtration. -/
axiom synAdamsConvergence (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) :
  SynAdamsConvergenceData X

/-! ### Functoriality -/

/-- Coherent functoriality of synthetic Adams, including the map on its
actual homotopy abutment.  The page map laws prevent independently chosen
maps for identities and composites, while `abutment_naturality` identifies
the filtered abutment map with postcomposition by the original map. -/
structure SynAdamsFunctorialityData where
  map : ∀ {X Y : Syn} (f : X ⟶ Y),
    SynAdamsSS Syn X ⟶ SynAdamsSS Syn Y
  map_id : ∀ X : Syn, map (𝟙 X) = 𝟙 (SynAdamsSS Syn X)
  map_comp : ∀ {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = map f ≫ map g
  convergenceMap : ∀ {X Y : Syn} (f : X ⟶ Y),
    ConvergenceMorphism
      (synAdamsConvergence Syn X).convergence
      (synAdamsConvergence Syn Y).convergence
  eMap_eq : ∀ {X Y : Syn} (f : X ⟶ Y),
    (convergenceMap f).eMap = (map f).eInftyMap
  abutment_naturality : ∀ {X Y : Syn} (f : X ⟶ Y)
      (degree : ℤ × ℤ) (a : (synAdamsConvergence Syn X).abutment degree),
    (synAdamsConvergence Syn Y).abutmentEquiv degree
        (((convergenceMap f).aMap degree).hom a) =
      (synAdamsConvergence Syn X).abutmentEquiv degree a ≫ f

/-- The coherent functoriality package for synthetic Adams. -/
axiom synAdamsFunctoriality (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn] :
  SynAdamsFunctorialityData (Syn := Syn)

/-- The spectral-sequence morphism induced by a map of synthetic spectra. -/
noncomputable def synAdamsSS_functorial {X Y : Syn} (f : X ⟶ Y) :
    SpectralSequenceMorphism (SynAdamsSS Syn X) (SynAdamsSS Syn Y) :=
  (synAdamsFunctoriality Syn).map f

@[simp] theorem synAdamsSS_functorial_id (X : Syn) :
    synAdamsSS_functorial (Syn := Syn) (𝟙 X) = 𝟙 (SynAdamsSS Syn X) :=
  (synAdamsFunctoriality Syn).map_id X

theorem synAdamsSS_functorial_comp {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z) :
    synAdamsSS_functorial (Syn := Syn) (f ≫ g) =
      SpectralSequenceMorphism.comp
        (synAdamsSS_functorial (Syn := Syn) f)
        (synAdamsSS_functorial (Syn := Syn) g) :=
  (synAdamsFunctoriality Syn).map_comp f g

/-- The map on the `r`-page induced by a map of synthetic spectra.  The
page index is written using the common starting page `2`, so the source and
target are compared without exposing the transports stored in
`SpectralSequenceMorphism.comm_d`. -/
noncomputable def synAdamsPageMap {X Y : Syn} (f : X ⟶ Y) (r : ℤ)
    (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn X).Page r k ⟶ (SynAdamsSS Syn Y).Page r k := by
  let F := synAdamsSS_functorial (Syn := Syn) f
  let nX : WithTop ℕ := ↑(r - (SynAdamsSS Syn X).r₀).toNat
  let nY : WithTop ℕ := ↑(r - (SynAdamsSS Syn Y).r₀).toNat
  let hn : nX = nY := congrArg
    (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) F.r₀_eq
  exact F.toSSDataMorphism.pageMapOfEq k k rfl nX nY hn

/-- The actual Adams page maps preserve composition, including the
transports between the displayed page numbers. -/
theorem synAdamsPageMap_comp {X Y Z : Syn} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    synAdamsPageMap (f ≫ g) r k =
      synAdamsPageMap f r k ≫ synAdamsPageMap g r k := by
  let F := synAdamsSS_functorial (Syn := Syn) f
  let G := synAdamsSS_functorial (Syn := Syn) g
  let H := synAdamsSS_functorial (Syn := Syn) (f ≫ g)
  apply SSDataMorphism.pageMapOfEq_comp F.toSSDataMorphism G.toSSDataMorphism
    H.toSSDataMorphism k k k rfl rfl
    (↑(r - (SynAdamsSS Syn X).r₀).toNat)
    (↑(r - (SynAdamsSS Syn Y).r₀).toNat)
    (↑(r - (SynAdamsSS Syn Z).r₀).toNat)
    (congrArg (fun q => (↑(r - q).toNat : WithTop ℕ)) F.r₀_eq)
    (congrArg (fun q => (↑(r - q).toNat : WithTop ℕ)) G.r₀_eq)
  exact congrArg (fun M => M.φ k) (synAdamsSS_functorial_comp f g)

/-- Postcomposition preserves the declared Adams-filtration subgroups.
This follows from the existing convergence naturality, rather than from a
new assumption about the subgroup filtration. -/
theorem synAdamsFiltration_postcomp {X Y : Syn} (f : X ⟶ Y)
    (m w s : ℤ) (a : Smn (Syn := Syn) m w ⟶ X)
    (ha : a ∈ synAdamsFiltration Syn X m w s) :
    a ≫ f ∈ synAdamsFiltration Syn Y m w s := by
  let A := synAdamsConvergence Syn X
  let B := synAdamsConvergence Syn Y
  let M := (synAdamsFunctoriality Syn).convergenceMap f
  let x := (A.filtrationEquiv s (m, w)).symm ⟨a, ha⟩
  let p := (M.filtration_compat s (m, w)).choose
  have hp := (M.filtration_compat s (m, w)).choose_spec
  have hxa : A.abutmentEquiv (m, w)
      ((A.filtration.F s (m, w)).arrow.hom x) = a := by
    rw [A.filtrationEquiv_comm]
    exact congrArg Subtype.val ((A.filtrationEquiv s (m, w)).apply_symm_apply ⟨a, ha⟩)
  have hy : (B.filtrationEquiv s (m, w) (p.hom x)).val = a ≫ f := by
    rw [← B.filtrationEquiv_comm]
    have heval := ConcreteCategory.congr_hom hp x
    change (B.filtration.F s (m, w)).arrow.hom (p.hom x) =
      (M.aMap (m, w)).hom ((A.filtration.F s (m, w)).arrow.hom x) at heval
    rw [heval, (synAdamsFunctoriality Syn).abutment_naturality, hxa]
  exact hy ▸ (B.filtrationEquiv s (m, w) (p.hom x)).property

/-- The map on the target of a page differential.  Its grading transport is
the one supplied by functoriality of the two spectral sequences. -/
noncomputable def synAdamsDifferentialTargetMap {X Y : Syn} (f : X ⟶ Y)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    (SynAdamsSS Syn X).Page r (k + (SynAdamsSS Syn X).diffDeg r) ⟶
      (SynAdamsSS Syn Y).Page r (k + (SynAdamsSS Syn Y).diffDeg r) := by
  let F := synAdamsSS_functorial (Syn := Syn) f
  let nX : WithTop ℕ := ↑(r - (SynAdamsSS Syn X).r₀).toNat
  let nY : WithTop ℕ := ↑(r - (SynAdamsSS Syn Y).r₀).toNat
  let hn : nX = nY := congrArg
    (fun r₀ => (↑(r - r₀).toNat : WithTop ℕ)) F.r₀_eq
  let hk : k + (SynAdamsSS Syn X).diffDeg r =
      k + (SynAdamsSS Syn Y).diffDeg r :=
    congrArg (fun d => k + d) (congrFun F.diffDeg_eq r)
  exact F.toSSDataMorphism.pageMapOfEq _ _ hk nX nY hn

/-- The page differential is natural under every map of synthetic spectra. -/
theorem synAdamsPageMap_comm_d {X Y : Syn} (f : X ⟶ Y)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    synAdamsPageMap (Syn := Syn) f r k ≫ (SynAdamsSS Syn Y).d r k =
      (SynAdamsSS Syn X).d r k ≫
        synAdamsDifferentialTargetMap (Syn := Syn) f r k := by
  exact (synAdamsSS_functorial (Syn := Syn) f).comm_d r k

/-! ### Graded λ-module structure -/

/-- A λ-action on a trigraded spectral sequence.  Unlike an ordinary module
structure on one fixed component, λ moves the grading by `(0,0,-1)`.
Compatibility says that applying λ commutes with the page differential; the
final `eqToHom` only exchanges the order of the two degree shifts. -/
structure SynAdamsLambdaModule
    (E : SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ × ℤ)) where
  lambda : ∀ (r : ℤ) (k : ℤ × ℤ × ℤ),
    E.Page r k ⟶ E.Page r (k + (0, 0, -1))
  comm_d : ∀ (r : ℤ) (k : ℤ × ℤ × ℤ),
    lambda r k ≫ E.d r (k + (0, 0, -1)) ≫
        eqToHom (congrArg (fun j => E.Page r j) (by
          abel)) =
      E.d r k ≫ lambda r (k + E.diffDeg r)

/-- A free λ-step between two adjacent weight components of one page.
The chosen isomorphism is required to be the actual λ action. -/
structure FreeLambdaPageStep
    {E : SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ × ℤ)}
    (L : SynAdamsLambdaModule E) (r : ℤ) (k : ℤ × ℤ × ℤ) where
  iso : E.Page r k ≅ E.Page r (k + (0, 0, -1))
  lambda_eq : L.lambda r k = iso.hom

namespace FreeLambdaPageStep

variable {E : SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ × ℤ)}
  {L : SynAdamsLambdaModule E} {r : ℤ} {k : ℤ × ℤ × ℤ}

/-- Multiplication by λ is injective on a free λ-step. -/
theorem lambda_injective (F : FreeLambdaPageStep L r k) :
    Function.Injective (L.lambda r k).hom := by
  rw [F.lambda_eq]
  intro x y hxy
  have h := congrArg (fun z => F.iso.inv.hom z) hxy
  simpa using h

end FreeLambdaPageStep

/-- An element-level page differential `d(x)=y` is essential when its
target class is nonzero on that page. -/
def PageDifferentialEssential
    (E : SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ × ℤ))
    (r : ℤ) (k : ℤ × ℤ × ℤ) (x : E.Page r k)
    (y : E.Page r (k + E.diffDeg r)) : Prop :=
  E.d r k x = y ∧ y ≠ 0

namespace SynAdamsLambdaModule

variable {E : SpectralSequence (AddCommGrpCat.{0}) (ℤ × ℤ × ℤ)}

/-- The differential after lowering source weight by one, transported to
the same target grading as λ applied after the original differential. -/
noncomputable def lambdaShiftedDifferential (L : SynAdamsLambdaModule E)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    E.Page r (k + (0, 0, -1)) ⟶
      E.Page r ((k + E.diffDeg r) + (0, 0, -1)) :=
  E.d r (k + (0, 0, -1)) ≫
    eqToHom (congrArg (fun j => E.Page r j) (by abel))

/-- The grading obtained after multiplying by λ `m` times. -/
def lambdaIndex : ℕ → (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  | 0, k => k
  | m + 1, k => lambdaIndex m k + (0, 0, -1)

@[simp] theorem lambdaIndex_zero (k : ℤ × ℤ × ℤ) :
    lambdaIndex 0 k = k := rfl

@[simp] theorem lambdaIndex_succ (m : ℕ) (k : ℤ × ℤ × ℤ) :
    lambdaIndex (m + 1) k = lambdaIndex m k + (0, 0, -1) := rfl

theorem lambdaIndex_eq (m : ℕ) (k : ℤ × ℤ × ℤ) :
    lambdaIndex m k = k + (0, 0, -(m : ℤ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [lambdaIndex_succ, ih]
      ext <;> dsimp [Nat.cast_succ] <;> omega

/-- Iterated multiplication by λ. -/
noncomputable def lambdaPow (L : SynAdamsLambdaModule E) (m : ℕ)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    E.Page r k ⟶ E.Page r (lambdaIndex m k) := by
  induction m with
  | zero => exact 𝟙 _
  | succ m ih => exact ih ≫ L.lambda r (lambdaIndex m k)

/-- Iterated λ multiplication on the target of the differential.  Its
target grading is written as `lambdaIndex m k + diffDeg r`, matching the
actual target of the shifted differential. -/
noncomputable def lambdaPowTarget (L : SynAdamsLambdaModule E) (m : ℕ)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    E.Page r (k + E.diffDeg r) ⟶
      E.Page r (lambdaIndex m k + E.diffDeg r) := by
  induction m with
  | zero => exact 𝟙 _
  | succ m ih =>
      exact ih ≫ L.lambda r (lambdaIndex m k + E.diffDeg r) ≫
        eqToHom (congrArg (fun j => E.Page r j) (by
          simp only [lambdaIndex_succ]
          abel))

/-- The differential at a source shifted by `λ^m`, with its target
transported to the same grading as `λ^m` applied after the original
differential. -/
noncomputable def lambdaPowShiftedDifferential
    (L : SynAdamsLambdaModule E) (m : ℕ) (r : ℤ)
    (k : ℤ × ℤ × ℤ) :
    E.Page r (lambdaIndex m k) ⟶
      E.Page r (lambdaIndex m k + E.diffDeg r) :=
  E.d r (lambdaIndex m k)

/-- Iterated λ multiplication commutes with the page differential. -/
theorem lambdaPow_naturality (L : SynAdamsLambdaModule E) (m : ℕ)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    L.lambdaPow m r k ≫ L.lambdaPowShiftedDifferential m r k =
      E.d r k ≫ L.lambdaPowTarget m r k := by
  induction m with
  | zero =>
      change 𝟙 (E.Page r k) ≫ E.d r k =
        E.d r k ≫ 𝟙 (E.Page r (k + E.diffDeg r))
      simp
  | succ m ih =>
      let hcommute : lambdaIndex m k + E.diffDeg r + (0, 0, -1) =
          lambdaIndex (Nat.succ m) k + E.diffDeg r := by
        rw [lambdaIndex_succ]
        abel
      change (L.lambdaPow m r k ≫ L.lambda r (lambdaIndex m k)) ≫
          L.lambdaPowShiftedDifferential (Nat.succ m) r k =
        E.d r k ≫
          ((L.lambdaPowTarget m r k ≫
            L.lambda r (lambdaIndex m k + E.diffDeg r)) ≫
              eqToHom (congrArg (fun j => E.Page r j) hcommute))
      rw [Category.assoc]
      have hc := L.comm_d r (lambdaIndex m k)
      have hc' : L.lambda r (lambdaIndex m k) ≫
          L.lambdaPowShiftedDifferential (Nat.succ m) r k =
        (L.lambdaPowShiftedDifferential m r k ≫
          L.lambda r (lambdaIndex m k + E.diffDeg r)) ≫
            eqToHom (congrArg (fun j => E.Page r j) hcommute) := by
        have h := congrArg (fun f => f ≫
          eqToHom (congrArg (fun j => E.Page r j) hcommute)) hc
        simpa only [lambdaPowShiftedDifferential, lambdaIndex_succ,
          Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id] using h
      rw [hc']
      have hi := congrArg (fun f =>
        (f ≫ L.lambda r (lambdaIndex m k + E.diffDeg r)) ≫
          eqToHom (congrArg (fun j => E.Page r j) hcommute)) ih
      simpa only [Category.assoc] using hi

/-- An iterated target λ-map is injective when each of its λ-steps is in
the free range. -/
theorem lambdaPowTarget_injective (L : SynAdamsLambdaModule E) (m : ℕ)
    (r : ℤ) (k : ℤ × ℤ × ℤ)
    (F : ∀ i : ℕ, i < m →
      FreeLambdaPageStep L r (lambdaIndex i k + E.diffDeg r)) :
    Function.Injective (L.lambdaPowTarget m r k).hom := by
  induction m with
  | zero =>
      intro x y h
      change x = y at h
      exact h
  | succ m ih =>
      have hprev : Function.Injective (L.lambdaPowTarget m r k).hom :=
        ih (fun i hi => F i (by omega))
      have hlam := (F m (by omega)).lambda_injective
      intro x y hxy
      apply hprev
      apply hlam
      let transport :
          E.Page r ((lambdaIndex m k + E.diffDeg r) + (0, 0, -1)) ⟶
            E.Page r (lambdaIndex (Nat.succ m) k + E.diffDeg r) :=
        eqToHom (congrArg (fun j => E.Page r j) (by
          rw [lambdaIndex_succ]
          abel))
      have htransport : Function.Injective transport.hom := by
        exact AddCommGrpCat.injective_of_mono transport
      apply htransport
      simpa only [lambdaPowTarget, AddCommGrpCat.coe_comp,
        Function.comp_apply] using hxy

/-- Naturality of the Adams differential under λ. -/
theorem lambdaShiftedDifferential_naturality (L : SynAdamsLambdaModule E)
    (r : ℤ) (k : ℤ × ℤ × ℤ) :
    L.lambda r k ≫ L.lambdaShiftedDifferential r k =
      E.d r k ≫ L.lambda r (k + E.diffDeg r) :=
  L.comm_d r k

/-- On a free λ-step at the target, Adams naturality gives
`d(x)=y` essential iff `d(λx)=λy` essential. -/
theorem pageDifferentialEssential_lambda_iff
    (L : SynAdamsLambdaModule E) (r : ℤ) (k : ℤ × ℤ × ℤ)
    (x : E.Page r k) (y : E.Page r (k + E.diffDeg r))
    (F : FreeLambdaPageStep L r (k + E.diffDeg r)) :
    PageDifferentialEssential E r k x y ↔
      ((L.lambdaShiftedDifferential r k).hom
          ((L.lambda r k).hom x) =
        (L.lambda r (k + E.diffDeg r)).hom y ∧
      (L.lambda r (k + E.diffDeg r)).hom y ≠ 0) := by
  have hinj := F.lambda_injective
  have hcomm := congrArg (fun f => f.hom x)
    (L.lambdaShiftedDifferential_naturality r k)
  change (L.lambdaShiftedDifferential r k).hom
      ((L.lambda r k).hom x) =
    (L.lambda r (k + E.diffDeg r)).hom ((E.d r k).hom x) at hcomm
  constructor
  · rintro ⟨hxy, hy⟩
    constructor
    · rw [hcomm, hxy]
    · intro hzero
      apply hy
      apply hinj
      simpa using hzero
  · rintro ⟨hxy, hly⟩
    constructor
    · apply hinj
      rw [← hcomm, hxy]
    · intro hy
      apply hly
      simp [hy]

end SynAdamsLambdaModule

/-- KIP §3: every page of the synthetic Adams spectral sequence has its
graded λ-action, and that action commutes with the differential.  This
replaces the former componentwise `Module (Polynomial ℤ)` statement, which
could not express the change in weight. -/
axiom synAdamsSS_zlambda_module (Syn : Type u) [Category.{v} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn] (X : Syn) :
    SynAdamsLambdaModule (SynAdamsSS Syn X)

end KIPBase.Synthetic
