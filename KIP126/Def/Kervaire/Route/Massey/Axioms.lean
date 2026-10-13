import KIP126.Def.Kervaire.Route.Massey.Predicates

/-!
  Explicit interface assumptions for the E₂-to-E₃ passage used by the
  sphere `⟨h₅²,h₀,B⟩` Massey calculation.  Reference-paper location:
  MainPaper/paper.txt, Lemma 7.16 and its proof (printed p.49), which
  identifies the detected Ext class `h₀² x₁₂₅,₉,₂`; the preceding hypotheses
  are Proposition 7.8(3) and (5').  The present `h₅²,h₀,B` notation is the
  route's E₂-level translation of that argument, not a claim that the paper
  uses this exact notation.  These are axioms of the route interface, not
  proved consequences of the predicate file.
-/
namespace KIP126.Kervaire.Route

open CategoryTheory
open KIP126.StableHomotopy KIP126.StableHomotopy.Cohomology
open KIP126.Classical.Adams KIP126.Core.SpectralSequence

universe u v
variable {C : Type u} [StableHomotopyCategory.{u, v} C]
  [HasFunctorialCofiber (C := C)]
  {H : Mod2EilenbergMacLane (C := C)} (M : MilnorCooperations H)

/-!
The missing page-representative bridge in MainPaper Lemma 7.16: an E₂ defining-system pair of
nullhomotopies produces an E₃ representative of the corresponding product
`h₆ · B`.  The axiom deliberately states only the page passage; the two
`d₂` equations remain explicit hypotheses and no indeterminacy conclusion is
smuggled in.
-/
axiom e2_massey_page3_representation
    (B : E2 H SphereSpectrum 8 70)
    (a : E2 H SphereSpectrum 1 64)
    (b : E2 H SphereSpectrum 7 70)
    (ha : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d 2
      (1, 64) a =
      Sphere.Internal.product H M (s := 2) (t := 64) (s' := 1) (t' := 1)
        (Sphere.Internal.hiSquare H M 5) (Sphere.Internal.hi H M 0))
    (hb : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).d 2
      (7, 70) b =
      Sphere.Internal.product H M (s := 1) (t := 1) (s' := 8) (t' := 70)
        (Sphere.Internal.hi H M 0) B) :
    ∃ x : (adamsTowerInternalSpectralSequence H.unit SphereSpectrum).Page 3
        (9, 134),
      RepresentsOnPage
        (adamsTowerInternalSpectralSequence H.unit SphereSpectrum)
        3 (9, 134)
        (Sphere.Internal.product H M (s := 1) (t := 64) (s' := 8) (t' := 70)
          (Sphere.Internal.hi H M 6) B) x

end KIP126.Kervaire.Route
