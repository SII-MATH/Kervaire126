/-
  KIPBase.Synthetic.WeightwiseTransport
  Fixed-weight transport interfaces for synthetic extension relations.
-/
import KIPBase.Synthetic.PageExtension

namespace KIPBase.SpectralSequence

open CategoryTheory

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Relation-level no-crossing with the projectivity witness made explicit.
This wrapper is convenient when the witness is stored inside another
dependent structure. -/
def ESSNoCrossingWith
    {E : SpectralSequence C (ℤ × ℤ)} (r : ℤ) (index : ℤ × ℤ)
    {T : C} (projective : Projective T)
    {x : T ⟶ (E.ssData index).V}
    {y : T ⟶ (E.ssData (index + E.diffDeg r)).V}
    (relation : DifferentialRelation E r index x y) : Prop :=
  letI : Projective T := projective
  ESSRelationNoCrossing r index relation

/-- Transport of one representative-level differential relation between two
spectral sequences with the same indexing group.

This deliberately records preservation of essentiality and relation-level
no-crossing, rather than merely giving unrelated source and target elements.
It is the exact fragment of the Blueprint's weightwise ESS transport used by
generalized Leibniz. -/
structure ESSRelationTransport
    (E E' : SpectralSequence C (ℤ × ℤ)) (r : ℤ) (index : ℤ × ℤ)
    {T : C} (projective : Projective T)
    {x : T ⟶ (E.ssData index).V}
    {y : T ⟶ (E.ssData (index + E.diffDeg r)).V}
    (relation : DifferentialRelation E r index x y) where
  source : T ⟶ (E'.ssData index).V
  target : T ⟶ (E'.ssData (index + E'.diffDeg r)).V
  transportedRelation : DifferentialRelation E' r index source target
  essential_iff :
    EssentialDifferentialRelation E r index x y ↔
      EssentialDifferentialRelation E' r index source target
  noCrossing_iff :
    ESSNoCrossingWith r index projective relation ↔
      ESSNoCrossingWith r index projective transportedRelation

namespace ESSRelationTransport

variable {E E' : SpectralSequence C (ℤ × ℤ)}
variable {r : ℤ} {index : ℤ × ℤ}
variable {T : C} [Projective T]
variable {x : T ⟶ (E.ssData index).V}
variable {y : T ⟶ (E.ssData (index + E.diffDeg r)).V}
variable {relation : DifferentialRelation E r index x y}

/-- Identity weightwise transport. -/
def refl : ESSRelationTransport E E r index (inferInstance : Projective T)
    relation where
  source := x
  target := y
  transportedRelation := relation
  essential_iff := Iff.rfl
  noCrossing_iff := Iff.rfl

/-- A no-crossing certificate transports to the target relation. -/
theorem noCrossing
    (W : ESSRelationTransport E E' r index
      (inferInstance : Projective T) relation)
    (h : ESSNoCrossingWith r index (inferInstance : Projective T) relation) :
    ESSNoCrossingWith r index (inferInstance : Projective T)
      W.transportedRelation :=
  W.noCrossing_iff.mp h

/-- Essentiality transports to the target relation. -/
theorem essential
    (W : ESSRelationTransport E E' r index
      (inferInstance : Projective T) relation)
    (h : EssentialDifferentialRelation E r index x y) :
    EssentialDifferentialRelation E' r index W.source W.target :=
  W.essential_iff.mp h

end ESSRelationTransport

end

end KIPBase.SpectralSequence

namespace KIPBase.Synthetic

open CategoryTheory CategoryTheory.Limits KIPBase.SpectralSequence

universe u u' v'

noncomputable section

variable (𝒮 : Type u) [KIPBase.StableHomotopy.StableHomotopyCategory.{u, 0} 𝒮]
variable (Syn : Type u') [Category.{v'} Syn] [Preadditive Syn]
    [HasZeroObject Syn] [HasShift Syn ℤ]
    [∀ n : ℤ, Functor.Additive (shiftFunctor Syn n)]
    [MonoidalCategory Syn]
    [Pretriangulated Syn] [SyntheticCategory Syn]

/-- The remaining weightwise input for the bottom edge of the canonical
`fHat`--lambda-boundary square.

The unshifted infinite page extension and its no-crossing certificate are
first canonicalized together.  The single transport witness then moves that
same relation to the suspended, weight-shifted bottom map.  No classical
comparison occurs here. -/
structure InfinitePageExtension.BottomWeightwiseTransport
    {X Y : 𝒮} {f : X ⟶ Y}
    {family : NormalizedPageESSFamily 𝒮 Syn f}
    {n s t : ℤ}
    (P : InfinitePageExtension 𝒮 Syn f family n s t)
    (hfamily : family.IsCanonical) (hP : P.NoCrossing)
    (bottomESS : SpectralSequence AddCommGrpCat (ℤ × ℤ)) where
  transport :
    let Q := P.canonicalNoCrossingExtension hfamily hP.essRelation
    ESSRelationTransport.{1, 0}
      ((syntheticExtensionCoreDataOfMap
        (fHatInfinitePage 𝒮 Syn f)).ess
          (t - s, t + eHat 𝒮 f))
      bottomESS n (s, 1) Q.1.projective Q.1.relation

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

/-- The transported bottom-edge differential relation. -/
theorem relation
    (W : InfinitePageExtension.BottomWeightwiseTransport
      𝒮 Syn P hfamily hP bottomESS) :
    DifferentialRelation bottomESS
      n (s, 1) W.transport.source W.transport.target :=
  W.transport.transportedRelation

/-- The page-extension no-crossing certificate becomes exactly the
bottom-edge ESS no-crossing hypothesis. -/
theorem noCrossing
    (W : InfinitePageExtension.BottomWeightwiseTransport
      𝒮 Syn P hfamily hP bottomESS) :
    let Q := P.canonicalNoCrossingExtension hfamily hP.essRelation
    ESSNoCrossingWith n (s, 1) Q.1.projective
      W.transport.transportedRelation := by
  dsimp only
  exact W.transport.noCrossing_iff.mp
    (P.canonicalNoCrossingExtension hfamily hP.essRelation).2

end InfinitePageExtension.BottomWeightwiseTransport

end

end KIPBase.Synthetic
