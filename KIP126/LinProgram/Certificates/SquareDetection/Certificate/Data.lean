import KIP126.LinProgram.Certificates.SquareDetection.Data

namespace KIP126.LinE2.SquareDetection

/-- Character-list form of the standard natural-number parser's lexical test,
including its underscore convention. -/
def charsAreNat (cs : List Char) : Bool := Id.run do
  let mut lastWasDigit := false
  for c in cs do
    if c = '_' then
      if !lastWasDigit then return false
      lastWasDigit := false
    else if c.isDigit then
      lastWasDigit := true
    else return false
  return lastWasDigit

def charsToNat? (cs : List Char) : Option ℕ :=
  if charsAreNat cs then
    some (cs.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0)
  else none

def charsMonomialOrder (cs : List Char) : ℕ :=
  if cs = [] then 0
  else orderOfPowers ((cs.splitOn ',').map (fun ns => (charsToNat? ns).getD 0))

def charsRelationCheck (cs : List Char) : Bool :=
  (cs.splitOn ';').all (fun m => decide (3 ≤ charsMonomialOrder m))

def charsChunkCheck (cs : List Char) : Bool :=
  (cs.splitOn '\n').all charsRelationCheck

/-- The finite family of character-list certificates, still evaluated on the
original archived strings. -/
def chunksCheck (chunks : List String) : Bool :=
  chunks.all (fun s => charsChunkCheck s.toList)

end KIP126.LinE2.SquareDetection
