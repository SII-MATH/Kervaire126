import KIP126.Def.Comparison.Pages.Predicates
import KIP126.Def.SpectralSequence.Basic.PageHomology.Data
import KIP126.Def.SpectralSequence.Computation.Proofs
import KIP126.Def.ClassicalAdams.PageRepresentatives.Proofs

namespace KIP126.Def.Comparison.StageInterfaces

open CategoryTheory
universe u v w

theorem pageCalculus {C : Type u} [Category.{v} C] [Abelian C]
    {ι : Type w} [AddCommGroup ι] [DecidableEq ι]
    (E : Core.SpectralSequence C ι) : Challenge2.PageCalculus E where
  homology r k hr := ⟨Core.SpectralSequence.pageHomologyIso E r k hr⟩
  square_zero := E.d_comp_d

theorem representativeCalculus {R : Type u} [Ring R]
    (E : Core.SpectralSequence (ModuleCat.{v} R) (ℤ × ℤ)) :
    Challenge2.RepresentativeCalculus E where
  page_two _ _ _ h := h.eq_on_page_two
  boundary_cycle _ _ _ h := h.isCycle
  differential_source _ _ _ _ _ h := h.source_survives
  differential_target _ _ _ _ _ h := h.target_survives

theorem paperCycleCalculus {C : Type u}
    [StableHomotopy.StableHomotopyCategory.{u, v} C]
    [StableHomotopy.HasFunctorialCofiber (C := C)]
    (H : StableHomotopy.Cohomology.Mod2EilenbergMacLane (C := C)) (X : C) :
    Challenge2.PaperCycleCalculus H X where
  first_cycles := Classical.Adams.PageRepresentatives.cycles_one H X
  first_boundaries := Classical.Adams.PageRepresentatives.boundaries_one H X
  represents := Classical.Adams.PageRepresentatives.isCycle_iff_represents H X
  degree _ _ _ _ _ h := Classical.Adams.PageRepresentatives.DifferentialAt.degree H X h
  no_crossing_two := Classical.Adams.PageRepresentatives.noCrossingOn_two H X

end KIP126.Def.Comparison.StageInterfaces
