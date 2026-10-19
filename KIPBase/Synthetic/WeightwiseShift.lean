/-
  KIPBase.Synthetic.WeightwiseShift
  Structural suspension/weight input for synthetic ESS transport.
-/
import KIPBase.Synthetic.GeneralizedRules

namespace KIPBase.SpectralSequence

open CategoryTheory

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ESSRelationTransport

variable {E E' E'' : SpectralSequence C (ℤ × ℤ)}
variable {r : ℤ} {index : ℤ × ℤ}
variable {T : C} [Projective T]
variable {x : T ⟶ (E.ssData index).V}
variable {y : T ⟶ (E.ssData (index + E.diffDeg r)).V}
variable {relation : DifferentialRelation E r index x y}

/-- Representative-level transports compose.  Essentiality and no-crossing
are composed as equivalences, so the resulting witness still refers to the
same transported relation rather than to independently chosen elements. -/
def comp
    (W₁ : ESSRelationTransport E E' r index
      (inferInstance : Projective T) relation)
    (W₂ : ESSRelationTransport E' E'' r index
      (inferInstance : Projective T) W₁.transportedRelation) :
    ESSRelationTransport E E'' r index
      (inferInstance : Projective T) relation where
  source := W₂.source
  target := W₂.target
  transportedRelation := W₂.transportedRelation
  essential_iff := W₁.essential_iff.trans W₂.essential_iff
  noCrossing_iff := W₁.noCrossing_iff.trans W₂.noCrossing_iff

end ESSRelationTransport

/-- Uniform transport of the ESS calculus from `E` to `E'`.

Unlike equality of spectral sequences, this permits the canonical
isomorphisms and reindexing transports produced by suspension.  A single
value transports every representative relation and simultaneously preserves
essentiality and relation-level no-crossing. -/
structure ESSCalculusTransport
    (E E' : SpectralSequence C (ℤ × ℤ)) where
  relation : ∀ (r : ℤ) (index : ℤ × ℤ) (T : C)
      (projective : Projective T)
      (x : T ⟶ (E.ssData index).V)
      (y : T ⟶ (E.ssData (index + E.diffDeg r)).V)
      (h : DifferentialRelation E r index x y),
    ESSRelationTransport E E' r index projective h

namespace ESSCalculusTransport

variable {E E' E'' : SpectralSequence C (ℤ × ℤ)}

/-- Identity transport of the complete ESS calculus. -/
def refl (E : SpectralSequence C (ℤ × ℤ)) : ESSCalculusTransport E E where
  relation := by
    intro r index T projective x y h
    letI : Projective T := projective
    exact ESSRelationTransport.refl

/-- Uniform ESS-calculus transports compose. -/
def comp (F : ESSCalculusTransport E E')
    (G : ESSCalculusTransport E' E'') : ESSCalculusTransport E E'' where
  relation := by
    intro r index T projective x y h
    letI : Projective T := projective
    let W₁ := F.relation r index T projective x y h
    let W₂ := G.relation r index T projective W₁.source W₁.target
      W₁.transportedRelation
    exact W₁.comp W₂

end ESSCalculusTransport

end


end KIPBase.SpectralSequence

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u u' v'

noncomputable section

variable (𝒮 : Type u)
    [KIPBase.StableHomotopy.StableHomotopyCategory.{u, 0} 𝒮]
variable (Syn : Type u') [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-- A common shift of source and target transports the canonical synthetic
extension spectral sequence to the correspondingly shifted abutment degree.

This uses uniform ESS-calculus transport, not strict equality: suspension
normally supplies canonical isomorphisms and grading transports rather than
definitional equality of the chosen spectral-sequence data. -/
structure SyntheticESSShiftCompatibility
    (F : Syn ⥤ Syn) (degreeShift : ℤ × ℤ) where
  ess : ∀ {X Y : Syn} (f : X ⟶ Y) (degree : ℤ × ℤ),
    ESSCalculusTransport
      (syntheticFESS f degree)
      (syntheticFESS (F.map f) (degree + degreeShift))

namespace SyntheticESSShiftCompatibility

/-- The identity functor has zero ESS degree shift. -/
def id : SyntheticESSShiftCompatibility (Syn := Syn) (𝟭 Syn) (0, 0) where
  ess := by
    intro X Y f degree
    change ESSCalculusTransport (syntheticFESS f degree)
      (syntheticFESS f (degree + (0, 0)))
    rw [show ((0, 0) : ℤ × ℤ) = 0 by rfl, add_zero]
    exact ESSCalculusTransport.refl _

/-- Uniform ESS shifts compose, and their displayed degree shifts add. -/
def comp {F G : Syn ⥤ Syn} {a b : ℤ × ℤ}
    (hF : SyntheticESSShiftCompatibility (Syn := Syn) F a)
    (hG : SyntheticESSShiftCompatibility (Syn := Syn) G b) :
    SyntheticESSShiftCompatibility (Syn := Syn) (F ⋙ G) (a + b) where
  ess := by
    intro X Y f degree
    change ESSCalculusTransport (syntheticFESS f degree)
      (syntheticFESS (G.map (F.map f)) (degree + (a + b)))
    rw [← add_assoc]
    exact (hF.ess f degree).comp (hG.ess (F.map f) (degree + a))

end SyntheticESSShiftCompatibility

/-- The common endofunctor occurring on the bottom edge of the
`fHat`--lambda-boundary square: first shift weight by `-n`, then suspend. -/
noncomputable def lambdaBoundaryShiftFunctor (n : ℕ) : Syn ⥤ Syn :=
  SyntheticCategory.biShift (0, -(n : ℤ)) ⋙ shiftFunctor Syn (1 : ℤ)

@[simp]
theorem lambdaBoundaryShiftFunctor_map {X Y : Syn} (n : ℕ) (f : X ⟶ Y) :
    (lambdaBoundaryShiftFunctor (Syn := Syn) n).map f =
      (shiftFunctor Syn (1 : ℤ)).map
        ((SyntheticCategory.biShift (0, -(n : ℤ))).map f) :=
  rfl

/-- The complete suspension/weight-shift interface needed by the synthetic
generalized-rule layer.  One uniform compatibility value is supplied for
each lambda-boundary shift; downstream declarations recover it through type
class inference and never ask for a relation-specific witness. -/
class SyntheticAdamsESSShiftSystem where
  lambdaBoundary : ∀ n : ℕ,
    SyntheticESSShiftCompatibility (Syn := Syn)
      (lambdaBoundaryShiftFunctor (Syn := Syn) n) (1, -(n : ℤ))

namespace InfinitePageExtension.BottomWeightwiseTransport

variable {𝒮 : Type u}
    [KIPBase.StableHomotopy.StableHomotopyCategory.{u, 0} 𝒮]
variable {Syn : Type u'} [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ q : ℤ, Functor.Additive (shiftFunctor Syn q)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]
variable {X Y : 𝒮} {f : X ⟶ Y}
variable {family : NormalizedPageESSFamily 𝒮 Syn f}
variable {n s t : ℤ}
variable {P : InfinitePageExtension 𝒮 Syn f family n s t}
variable {hfamily : family.IsCanonical} {hP : P.NoCrossing}
variable {bottomESS : SpectralSequence AddCommGrpCat (ℤ × ℤ)}

/-- Uniform transport of the whole ESS calculus constructs the bottom
transport package.  Essentiality and no-crossing are already tied to the
transported relation by `ESSCalculusTransport`. -/
def ofCalculusTransport
    (H : ESSCalculusTransport
      ((syntheticExtensionCoreDataOfMap
        (fHatInfinitePage 𝒮 Syn f)).ess
          (t - s, t + eHat 𝒮 f)) bottomESS) :
    InfinitePageExtension.BottomWeightwiseTransport
      𝒮 Syn P hfamily hP bottomESS := by
  let Q := P.canonicalNoCrossingExtension hfamily hP.essRelation
  refine ⟨?_⟩
  exact H.relation n (s, 1) Q.1.T Q.1.projective
    Q.1.source Q.1.scaledTarget Q.1.relation

end InfinitePageExtension.BottomWeightwiseTransport

namespace InfinitePageExtension.FHatBottomWeightwiseTransport

variable {𝒮 : Type u}
    [KIPBase.StableHomotopy.StableHomotopyCategory.{u, 0} 𝒮]
variable {Syn : Type u'} [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ q : ℤ, Functor.Additive (shiftFunctor Syn q)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]
variable {X Y : 𝒮} {f : X ⟶ Y}
variable {family : NormalizedPageESSFamily 𝒮 Syn f}
variable {l s t : ℤ}
variable {P : InfinitePageExtension 𝒮 Syn f family l s t}
variable {hfamily : family.IsCanonical} {hP : P.NoCrossing}

/-- Uniform shift compatibility constructs the concrete bottom-edge
transport for `fHat`.  The displayed bottom degree is exactly the original
degree plus the suspension/weight shift `(1,-n)`. -/
def ofShiftCompatibility (n : ℕ)
    (H : SyntheticESSShiftCompatibility (Syn := Syn)
      (lambdaBoundaryShiftFunctor (Syn := Syn) n) (1, -(n : ℤ))) :
    P.FHatBottomWeightwiseTransport 𝒮 hfamily hP n
      ((t - s, t + eHat 𝒮 f) + (1, -(n : ℤ))) := by
  apply InfinitePageExtension.BottomWeightwiseTransport.ofCalculusTransport
  exact H.ess (fHatInfinitePage 𝒮 Syn f) (t - s, t + eHat 𝒮 f)

/-- Canonical bottom transport obtained from the ambient synthetic Adams
shift system.  No explicit ESS comparison or relation-level transport
remains in the caller-facing interface. -/
def ofShiftSystem [SyntheticAdamsESSShiftSystem (Syn := Syn)] (n : ℕ) :
    P.FHatBottomWeightwiseTransport 𝒮 hfamily hP n
      ((t - s, t + eHat 𝒮 f) + (1, -(n : ℤ))) :=
  ofShiftCompatibility n
    (SyntheticAdamsESSShiftSystem.lambdaBoundary (Syn := Syn) n)

end InfinitePageExtension.FHatBottomWeightwiseTransport

end


end KIPBase.Synthetic
