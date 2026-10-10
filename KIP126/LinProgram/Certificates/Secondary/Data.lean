import KIP126.LinProgram.Certificates.Milnor.StableProduct

/-!
# Coefficient semantics for a finite secondary-resolution input

The product is the dual of the existing explicit Milnor coproduct. Every
coefficient is tested at all monomials of the original rank. Missing images
cause composition to fail; they never become zero differential columns.
This layer does not identify the input with a Steenrod resolution or Adams d₂.
-/
namespace KIP126.Computation.Secondary
open MilnorCertificates

structure ModuleTerm where
  sq : Monomial
  generator : Nat
  deriving DecidableEq, Repr

abbrev ModuleExpression := List ModuleTerm

/-- One selected row of the extracted 96-generator witness. The fields
`id`, `s`, `v`, `t`, `d`, and `f` transcribe the native databases.
`d_f`, `f_d`, and `associator` are auxiliary expressions computed by the
extractor, not native output or assumed chain identities. -/
structure NativeRow where
  id : Nat
  s : Nat
  v : Nat
  t : Nat
  d : ModuleExpression
  f : ModuleExpression
  d_f : ModuleExpression
  f_d : ModuleExpression
  associator : ModuleExpression
  deriving DecidableEq, Repr

structure CompositionPath where
  left : Monomial
  right : Monomial
  target : Nat
  deriving DecidableEq, Repr

/-- All paths must have a known image. Absent data is rejected. -/
def resolvePaths (images : Nat → Option ModuleExpression) :
    ModuleExpression → Option (List CompositionPath)
  | [] => some []
  | a :: rest => do
      let next ← images a.generator
      let tail ← resolvePaths images rest
      pure ((next.map fun b => ⟨a.sq, b.sq, b.generator⟩) ++ tail)

/-- Coefficients of the two-step differential in the explicit dual Milnor algebra. -/
def pathCoefficient (rank : Nat) (target : Nat) (m : Monomial) :
    List CompositionPath → Bool
  | [] => false
  | p :: rest => xor
      (if p.target = target then pairTensor [p.left] [p.right] (coproduct rank m) else false)
      (pathCoefficient rank target m rest)

def expressionCoefficient (a : ModuleExpression) (target : Nat) (m : Monomial) : Bool :=
  coefficient ((a.filter fun t => t.generator == target).map (·.sq)) m

/-- An equality of these functions covers every target generator and every
monomial of the original arity, with no cutoff on its degree. -/
def compose (rank : Nat) (images : Nat → Option ModuleExpression) (a : ModuleExpression) :
    Option (Nat → {m : Monomial // m.length = rank} → Bool) :=
  (resolvePaths images a).map fun paths target m => pathCoefficient rank target m.val paths

end KIP126.Computation.Secondary
