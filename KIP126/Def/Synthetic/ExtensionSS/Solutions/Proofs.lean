import KIP126.Def.Synthetic.ExtensionSS.Data
import KIP126.Def.SpectralSequence.FilteredComplex.Solutions.Page.Converse.Proofs

namespace KIP126.Synthetic.SpectralSequence.SyntheticExtensionData
open CategoryTheory KIP126.Synthetic.Context KIP126.Core.SpectralSequence
universe u v
variable {Syn : Type u} [SyntheticCategory.{u, v} Syn]
  {F : SyntheticAdamsFamily Syn} {X Y : Syn} {g : X ⟶ Y}

set_option backward.isDefEq.respectTransparency false

/-- The actual synthetic ESS relation is exactly a nonempty fiber of its
representative equations, tested on a projective object. -/
theorem differentialRelation_iff_solutions (D : SyntheticExtensionData F g)
    (p : ℤ × ℤ) (n : ℕ) (s : ℤ) {T : ModuleCat.{v} ℤ} [Projective T]
    (x : T ⟶ (D.complex p).assocGraded s 1)
    (y : T ⟶ (D.complex p).assocGraded (s + (n : ℤ)) 0) :
    DifferentialRelation (D.ess p) n (s, 1) x y ↔
      Nonempty (FilteredComplex.Solutions.Fiber (D.complex p) n s 1 x y) :=
  FilteredComplex.Solutions.differentialRelation_iff_nonempty_fiber (D.complex p)
    ((BoundedExtensionSS.mk' D.source.toConvergence D.target.toConvergence D.map
      D.source_bounded D.target_bounded).bounded p) n s 1 x y

end KIP126.Synthetic.SpectralSequence.SyntheticExtensionData
