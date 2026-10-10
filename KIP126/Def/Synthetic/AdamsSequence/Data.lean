import KIP126.Def.ClassicalAdams.Grading.Data
import KIP126.Def.SpectralSequence.PageLevel.Data
import KIP126.Def.SpectralSequence.Basic.Category.Data
import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
import KIP126.Def.SpectralSequence.Convergence.Data
import KIP126.Def.Synthetic.Sphere.Data
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Internal synthetic Adams objects

All spectral sequences here use the internal nested-subobject model. A family
is explicit functor data on one synthetic category; evaluating it on νX or a
λ-power cofiber makes the object binding definitional. No family or convergence
witness is chosen globally, and no Mathlib spectral-sequence comparison is
required. Construction of the family and its literature properties remain
separate obligations.
-/

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory CategoryTheory.Limits
open KIP126.Core.SpectralSequence KIP126.Synthetic.Context KIP126.StableHomotopy

universe u v u' v'
noncomputable section

abbrev Tridegree := ℤ × ℤ × ℤ

/-! 底层谱序列必须在所有整数页上给出次数；带 `Raw` 的名称只服务于该接口。 -/
def syntheticAdamsRawShift (r : ℤ) : Tridegree := (r, r - 1, 0)

def syntheticAdamsRawTarget (r : ℤ) (i : Tridegree) : Tridegree :=
  i + syntheticAdamsRawShift r

/-- 有效 synthetic Adams 页的微分次数。 -/
def syntheticAdamsShift (r : AdamsPage) : Tridegree :=
  syntheticAdamsRawShift r.toInt

/-- 有效 synthetic Adams 页微分的目标三次数。 -/
def syntheticAdamsTarget (r : AdamsPage) (i : Tridegree) : Tridegree :=
  i + syntheticAdamsShift r

def syntheticAdamsPageLevel : PageLevelConvention where
  firstPage := 2
  admissibleFrom := 2
  page := fun r => r
  cycleLevel := fun r => r - 1
  quotientExponent := fun r => r - 1
  page_first := by norm_num
  page_succ := by intro r; norm_num
  cycle_succ := by intro r; omega
  quotient_succ := by intro r; omega
  cycleLevel_eq_quotientExponent := by intro r; rfl

/-- A grading shape, not a Mathlib spectral-sequence object. -/
def syntheticAdamsShape (r : ℤ) : ComplexShape Tridegree :=
  ComplexShape.up' (syntheticAdamsRawShift r)

/-- 把有效 Adams 页送入底层整数形状。 -/
def syntheticAdamsShapeAt (r : AdamsPage) : ComplexShape Tridegree :=
  syntheticAdamsShape r.toInt

def lambdaDegree : Tridegree := (0, 0, -1)

def lambdaTarget (i : Tridegree) : Tridegree := i + lambdaDegree

abbrev SyntheticAdamsSpectralSequence :=
  KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree

/-- An internal sequence with exactly the synthetic Adams page convention.
Standard classes and a λ action are not chosen independently in this record. -/
structure SyntheticAdamsSS where
  sequence : SyntheticAdamsSpectralSequence.{v}
  firstPage : sequence.r₀ = 2
  differentialDegree : ∀ r : ℤ, sequence.diffDeg r = syntheticAdamsRawShift r

namespace SyntheticAdamsSS

/-- Normalized page accessor; its cycle level is always `(r - 2).toNat`. -/
def Page (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree) : ModuleCat.{v} ℤ :=
  (A.sequence.ssData i).page (↑(r - 2).toNat : WithTop ℕ)

def E₂ (A : SyntheticAdamsSS.{v}) := A.Page 2

def E₃ (A : SyntheticAdamsSS.{v}) := A.Page 3

/-- The actual internal differential, with only its proven degree transported. -/
def d (A : SyntheticAdamsSS.{v}) (r : ℤ) (i : Tridegree) :
    A.Page r i ⟶ A.Page r (syntheticAdamsRawTarget r i) :=
  eqToHom (by simp only [Page, A.firstPage]) ≫
    A.sequence.d r i ≫ eqToHom (by
      simp only [Page, A.firstPage, A.differentialDegree, syntheticAdamsRawTarget])

/-- Successor-page homology, derived from the internal cycle/boundary axioms. -/
def e₂ToE₃ (A : SyntheticAdamsSS.{v}) (i : Tridegree) :
    (A.sequence.pageShortComplex 2 (i - A.sequence.diffDeg 2)).homology ≅ A.E₃ i :=
  (pageHomologyIso A.sequence 2 i (by simp [A.firstPage])).symm ≪≫
    eqToIso (by norm_num [E₃, Page, KIP126.Core.SpectralSequence.Page, A.firstPage])

def d₂ (A : SyntheticAdamsSS.{v}) (i : Tridegree) :
    A.E₂ i ⟶ A.E₂ (syntheticAdamsTarget AdamsPage.two i) := A.d 2 i

end SyntheticAdamsSS

/-- A λ action on the internal cycle and boundary towers. Each page map is the
canonical quotient map of `ambient`; there are no independently chosen page
maps. Binding this action to the synthetic deformation map is an additional
compatibility obligation, not an automatic property of an arbitrary action. -/
structure SyntheticLambdaAction (A : SyntheticAdamsSS.{v}) where
  ambient : SSDataMorphism Tridegree A.sequence.ssData
    (fun i => A.sequence.ssData (lambdaTarget i))
  comm_d : ∀ (r : ℤ) (i : Tridegree),
    ambient.pageMap i (↑(r - 2).toNat : WithTop ℕ) ≫
        A.d r (lambdaTarget i) ≫
        eqToHom (congrArg (A.Page r) (show
          syntheticAdamsRawTarget r (lambdaTarget i) =
            lambdaTarget (syntheticAdamsRawTarget r i) by
          simp only [syntheticAdamsRawTarget, lambdaTarget]; abel)) =
      A.d r i ≫ ambient.pageMap (syntheticAdamsRawTarget r i)
        (↑(r - 2).toNat : WithTop ℕ)

def lambdaMapFromAction {A : SyntheticAdamsSS.{v}}
    (action : SyntheticLambdaAction A) (i : Tridegree) :
    A.E₂ i ⟶ A.E₂ (lambdaTarget i) :=
  action.ambient.pageMap i 0

def forgetWeight (i : Tridegree) : KIP126.Classical.Adams.Bidegree :=
  (i.1, i.2.1)

def nuDegree (b : KIP126.Classical.Adams.Bidegree) : Tridegree :=
  (b.1, b.2, b.2)

/-- The fixed-weight graded page of the same internal sequence. -/
def fixedWeightPage (A : SyntheticAdamsSS.{v}) (w r : ℤ)
    (b : KIP126.Classical.Adams.Bidegree) : ModuleCat.{v} ℤ :=
  A.Page r (b.1, b.2, w)

/-- The same internal differential restricted to a fixed weight. -/
def fixedWeightDifferential (A : SyntheticAdamsSS.{v}) (w r : ℤ)
    (b : KIP126.Classical.Adams.Bidegree) :
    fixedWeightPage A w r b ⟶ fixedWeightPage A w r (b + (r, r - 1)) :=
  A.d r (b.1, b.2, w) ≫ eqToHom (by
    unfold fixedWeightPage syntheticAdamsRawTarget syntheticAdamsRawShift
    congr 1
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact add_zero w)

/-- A single functor on the chosen synthetic category, with the Adams grading
fixed on every object. Its existence and construction are not postulated. -/
structure SyntheticAdamsFamily (Syn : Type u) [SyntheticCategory.{u, v} Syn] where
  functor : Syn ⥤ KIP126.Core.SpectralSequence (ModuleCat.{v} ℤ) Tridegree
  firstPage : ∀ X, (functor.obj X).r₀ = 2
  differentialDegree : ∀ X r, (functor.obj X).diffDeg r = syntheticAdamsRawShift r

namespace SyntheticAdamsFamily

variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]

def obj (F : SyntheticAdamsFamily Syn) (X : Syn) : SyntheticAdamsSS.{v} where
  sequence := F.functor.obj X
  firstPage := F.firstPage X
  differentialDegree := F.differentialDegree X

/-- The same family on the synthetic sphere; no independently chosen sequence. -/
def sphere (F : SyntheticAdamsFamily Syn) : SyntheticAdamsSS.{v} :=
  F.obj S_0_0

/-- Evaluate the family on the actual ν-image. -/
def nu {Stable : Type u'} [StableHomotopyCategory.{u', v'} Stable]
    (F : SyntheticAdamsFamily Syn) (N : NuFunctorData Stable Syn) (X : Stable) :
    SyntheticAdamsSS.{v} := F.obj (N.functor.obj X)

/-- The ν-sphere and synthetic unit use the unit identification from the same
ν datum, transported by the same internal spectral-sequence functor. -/
def nuSphereIso {Stable : Type u'} [StableHomotopyCategory.{u', v'} Stable]
    (F : SyntheticAdamsFamily Syn) (N : NuFunctorData Stable Syn) :
    (F.nu N (SphereSpectrum (C := Stable))).sequence ≅ F.sphere.sequence :=
  F.functor.mapIso N.unitIso

/-- Evaluate the family on the chosen cofiber of the same λ power. -/
def quotient [HasFunctorialCofiber (C := Syn)]
    (F : SyntheticAdamsFamily Syn) (X : Syn) (n : ℕ) : SyntheticAdamsSS.{v} :=
  F.obj (XModLambdaN X n)

def nuQuotient {Stable : Type u'} [StableHomotopyCategory.{u', v'} Stable]
    [HasFunctorialCofiber (C := Syn)] (F : SyntheticAdamsFamily Syn)
    (N : NuFunctorData Stable Syn) (X : Stable) (n : ℕ) : SyntheticAdamsSS.{v} :=
  F.quotient (N.functor.obj X) n

/-- The quotient projection is the image of the actual cofiber inclusion. -/
def quotientProjection [HasFunctorialCofiber (C := Syn)]
    (F : SyntheticAdamsFamily Syn) (X : Syn) (n : ℕ) :
    (F.obj X).sequence ⟶ (F.quotient X n).sequence :=
  F.functor.map (HasFunctorialCofiber.cofibι (lambdaPow n X))

/-- The family map of λ has its actual shifted object as source. A regrading
identification is still required to turn this into `SyntheticLambdaAction`. -/
def deformationMap (F : SyntheticAdamsFamily Syn) (X : Syn) :
    (F.obj ((SyntheticCategory.biShift (0, -1)).obj X)).sequence ⟶
      (F.obj X).sequence :=
  F.functor.map (SyntheticCategory.lam.app X)

end SyntheticAdamsFamily

/-- The abutment is the actual bigraded homotopy of the given object. -/
def syntheticHomotopy {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    (X : Syn) (p : ℤ × ℤ) : ModuleCat.{v} ℤ :=
  ModuleCat.of ℤ (BiHom p.1 p.2 X)

/-- A convergence witness for a particular object in the same family. This is
supplied only where justified; arbitrary synthetic objects are not assumed to
converge. The grading is fixed to `E∞^(s,t,w) ≅ gr^s π_(t-s,w) X`. -/
structure SyntheticAdamsConvergence {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    (F : SyntheticAdamsFamily Syn) (X : Syn) where
  filtration : Filtration (syntheticHomotopy X)
  identification : ∀ i : Tridegree,
    ((F.obj X).sequence.ssData i).eInfty ≅
      filtration.associatedGraded i.1 (i.2.1 - i.1, i.2.2)

/-- Convert the object-bound convergence witness to the generic internal API. -/
def SyntheticAdamsConvergence.toConvergence
    {Syn : Type u} [SyntheticCategory.{u, v} Syn]
    {F : SyntheticAdamsFamily Syn} {X : Syn} (c : SyntheticAdamsConvergence F X) :
    Convergence (F.obj X).sequence (syntheticHomotopy X) c.filtration where
  reindex i := (i.1, i.2.1 - i.1, i.2.2)
  reindex_bijective := by
    constructor
    · rintro ⟨s, t, w⟩ ⟨s', t', w'⟩ h
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by omega, h.2.2⟩
    · rintro ⟨s, m, w⟩
      exact ⟨(s, m + s, w), by simp⟩
  iso := c.identification

end
end KIP126.Synthetic.SpectralSequence
