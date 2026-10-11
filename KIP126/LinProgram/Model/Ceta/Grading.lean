module

public import KIP126.LinProgram.Model.Modules

@[expose] public section


/-! Integer degrees of every generator of the unchanged native Ceta quotient.
The finite row-presence proof permits a total lookup without a default row. -/
namespace KIP126.LinModule
namespace Ceta
set_option maxRecDepth 100000 in
theorem generatorRow_present :
    ∀ i : Generator, (RawData.Ceta.generatorRow i.val).isSome = true := by decide

def generatorData (i : Generator) : RawData.GeneratorRow :=
  (RawData.Ceta.generatorRow i.val).get (generatorRow_present i)

def generatorDegree (i : Generator) : ℤ × ℤ :=
  ((generatorData i).s, (generatorData i).t)
end Ceta
end KIP126.LinModule
