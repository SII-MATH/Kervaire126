module

public import KIP126.Def.StableHomotopy.Implementation.Generators

@[expose] public section

namespace KIP126.StableHomotopy.Implementation.BasedSpace
open CategoryTheory
open scoped unitInterval
universe u

/-- Homotopy extension in based spaces: both the given homotopy and
its extension keep the specified point fixed for the entire interval. -/
def HasBasedHomotopyExtension {A B : BasedSpace.{u}} (i : A ⟶ B) : Prop :=
  ∀ (Z : BasedSpace.{u}) (f : B ⟶ Z) (p : C(A × I,Z)),
    (∀ t, p (A.point,t) = Z.point) →
    (∀ a, p (a,0) = f.map (i.map a)) →
    ∃ H : C(B × I,Z),
      (∀ t, H (B.point,t) = Z.point) ∧
      (∀ b, H (b,0) = f.map b) ∧
      (∀ a t, H (i.map a,t) = p (a,t))

end KIP126.StableHomotopy.Implementation.BasedSpace
