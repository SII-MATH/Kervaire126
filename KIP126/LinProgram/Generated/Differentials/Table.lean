import KIP126.LinProgram.Generated.Differentials.Shard000
import KIP126.LinProgram.Generated.Differentials.Shard001
import KIP126.LinProgram.Generated.Differentials.Shard002
import KIP126.LinProgram.Generated.Differentials.Shard003
import KIP126.LinProgram.Generated.Differentials.Shard004
import KIP126.LinProgram.Generated.Differentials.Shard005
import KIP126.LinProgram.Generated.Differentials.Shard006
import KIP126.LinProgram.Generated.Differentials.Shard007
import KIP126.LinProgram.Generated.Differentials.Shard008
import KIP126.LinProgram.Generated.Differentials.Shard009
import KIP126.LinProgram.Generated.Differentials.Shard010
import KIP126.LinProgram.Generated.Differentials.Shard011
import KIP126.LinProgram.Generated.Differentials.Shard012
import KIP126.LinProgram.Generated.Differentials.Shard013
import KIP126.LinProgram.Generated.Differentials.Shard014
import KIP126.LinProgram.Generated.Differentials.Shard015
import KIP126.LinProgram.Generated.Differentials.Shard016
import KIP126.LinProgram.Generated.Differentials.Shard017
import KIP126.LinProgram.Generated.Differentials.Shard018
import KIP126.LinProgram.Generated.Differentials.Shard019
import KIP126.LinProgram.Generated.Differentials.Shard020
import KIP126.LinProgram.Generated.Differentials.Shard021
import KIP126.LinProgram.Generated.Differentials.Shard022
import KIP126.LinProgram.Generated.Differentials.Shard023
import KIP126.LinProgram.Generated.Differentials.Shard024
import KIP126.LinProgram.Generated.Differentials.Shard025
import KIP126.LinProgram.Generated.Differentials.Shard026
import KIP126.LinProgram.Generated.Differentials.Shard027
import KIP126.LinProgram.Generated.Differentials.Shard028
import KIP126.LinProgram.Generated.Differentials.Shard029
import KIP126.LinProgram.Generated.Differentials.Shard030
import KIP126.LinProgram.Generated.Differentials.Shard031
import KIP126.LinProgram.Generated.Differentials.Shard032
import KIP126.LinProgram.Generated.Differentials.Shard033
import KIP126.LinProgram.Generated.Differentials.Shard034
import KIP126.LinProgram.Generated.Differentials.Shard035
import KIP126.LinProgram.Generated.Differentials.Shard036
import KIP126.LinProgram.Generated.Differentials.Shard037
import KIP126.LinProgram.Generated.Differentials.Shard038
import KIP126.LinProgram.Generated.Differentials.Shard039
import KIP126.LinProgram.Generated.Differentials.Shard040
import KIP126.LinProgram.Generated.Differentials.Shard041
import KIP126.LinProgram.Generated.Differentials.Shard042
import KIP126.LinProgram.Generated.Differentials.Shard043
import KIP126.LinProgram.Generated.Differentials.Shard044
import KIP126.LinProgram.Generated.Differentials.Shard045
import KIP126.LinProgram.Generated.Differentials.Shard046
import KIP126.LinProgram.Generated.Differentials.Shard047
import KIP126.LinProgram.Generated.Differentials.Shard048
import KIP126.LinProgram.Generated.Differentials.Shard049
import KIP126.LinProgram.Generated.Differentials.Shard050
import KIP126.LinProgram.Generated.Differentials.Shard051
import KIP126.LinProgram.Generated.Differentials.Shard052
import KIP126.LinProgram.Generated.Differentials.Shard053
import KIP126.LinProgram.Generated.Differentials.Shard054
import KIP126.LinProgram.Generated.Differentials.Shard055
import KIP126.LinProgram.Generated.Differentials.Shard056
import KIP126.LinProgram.Generated.Differentials.Shard057
import KIP126.LinProgram.Generated.Differentials.Shard058
import KIP126.LinProgram.Generated.Differentials.Shard059
import KIP126.LinProgram.Generated.Differentials.Shard060
import KIP126.LinProgram.Generated.Differentials.Shard061
import KIP126.LinProgram.Generated.Differentials.Shard062
import KIP126.LinProgram.Generated.Differentials.Shard063
import KIP126.LinProgram.Generated.Differentials.Shard064
import KIP126.LinProgram.Generated.Differentials.Shard065
import KIP126.LinProgram.Generated.Differentials.Shard066
import KIP126.LinProgram.Generated.Differentials.Shard067
import KIP126.LinProgram.Generated.Differentials.Shard068
import KIP126.LinProgram.Generated.Differentials.Shard069
import KIP126.LinProgram.Generated.Differentials.Shard070
import KIP126.LinProgram.Generated.Differentials.Shard071
import KIP126.LinProgram.Generated.Differentials.Shard072
import KIP126.LinProgram.Generated.Differentials.Shard073
import KIP126.LinProgram.Generated.Differentials.Shard074
import KIP126.LinProgram.Generated.Differentials.Shard075
import KIP126.LinProgram.Generated.Differentials.Shard076
import KIP126.LinProgram.Generated.Differentials.Shard077
import KIP126.LinProgram.Generated.Differentials.Shard078
import KIP126.LinProgram.Generated.Differentials.Shard079
import KIP126.LinProgram.Generated.Differentials.Shard080
import KIP126.LinProgram.Generated.Differentials.Shard081
import KIP126.LinProgram.Generated.Differentials.Shard082
import KIP126.LinProgram.Generated.Differentials.Shard083
import KIP126.LinProgram.Generated.Differentials.Shard084
import KIP126.LinProgram.Generated.Differentials.Shard085

namespace KIP126.Computation.LinProofs.RawData

def databaseSha256 : String := "3a460683c023ee2d8f7e8f904ecef9044a474d88bb7184731e54978ba7dac248"
def sourceRowCount : Nat := 2672275
def differentialRowCount : Nat := 10907

/-- Lookup is shard-local so kernel checks need not unfold the whole table. -/
def lookup (shard offset : Nat) : Option DifferentialRow :=
  match shard with
  | 0 => shard0[offset]?
  | 1 => shard1[offset]?
  | 2 => shard2[offset]?
  | 3 => shard3[offset]?
  | 4 => shard4[offset]?
  | 5 => shard5[offset]?
  | 6 => shard6[offset]?
  | 7 => shard7[offset]?
  | 8 => shard8[offset]?
  | 9 => shard9[offset]?
  | 10 => shard10[offset]?
  | 11 => shard11[offset]?
  | 12 => shard12[offset]?
  | 13 => shard13[offset]?
  | 14 => shard14[offset]?
  | 15 => shard15[offset]?
  | 16 => shard16[offset]?
  | 17 => shard17[offset]?
  | 18 => shard18[offset]?
  | 19 => shard19[offset]?
  | 20 => shard20[offset]?
  | 21 => shard21[offset]?
  | 22 => shard22[offset]?
  | 23 => shard23[offset]?
  | 24 => shard24[offset]?
  | 25 => shard25[offset]?
  | 26 => shard26[offset]?
  | 27 => shard27[offset]?
  | 28 => shard28[offset]?
  | 29 => shard29[offset]?
  | 30 => shard30[offset]?
  | 31 => shard31[offset]?
  | 32 => shard32[offset]?
  | 33 => shard33[offset]?
  | 34 => shard34[offset]?
  | 35 => shard35[offset]?
  | 36 => shard36[offset]?
  | 37 => shard37[offset]?
  | 38 => shard38[offset]?
  | 39 => shard39[offset]?
  | 40 => shard40[offset]?
  | 41 => shard41[offset]?
  | 42 => shard42[offset]?
  | 43 => shard43[offset]?
  | 44 => shard44[offset]?
  | 45 => shard45[offset]?
  | 46 => shard46[offset]?
  | 47 => shard47[offset]?
  | 48 => shard48[offset]?
  | 49 => shard49[offset]?
  | 50 => shard50[offset]?
  | 51 => shard51[offset]?
  | 52 => shard52[offset]?
  | 53 => shard53[offset]?
  | 54 => shard54[offset]?
  | 55 => shard55[offset]?
  | 56 => shard56[offset]?
  | 57 => shard57[offset]?
  | 58 => shard58[offset]?
  | 59 => shard59[offset]?
  | 60 => shard60[offset]?
  | 61 => shard61[offset]?
  | 62 => shard62[offset]?
  | 63 => shard63[offset]?
  | 64 => shard64[offset]?
  | 65 => shard65[offset]?
  | 66 => shard66[offset]?
  | 67 => shard67[offset]?
  | 68 => shard68[offset]?
  | 69 => shard69[offset]?
  | 70 => shard70[offset]?
  | 71 => shard71[offset]?
  | 72 => shard72[offset]?
  | 73 => shard73[offset]?
  | 74 => shard74[offset]?
  | 75 => shard75[offset]?
  | 76 => shard76[offset]?
  | 77 => shard77[offset]?
  | 78 => shard78[offset]?
  | 79 => shard79[offset]?
  | 80 => shard80[offset]?
  | 81 => shard81[offset]?
  | 82 => shard82[offset]?
  | 83 => shard83[offset]?
  | 84 => shard84[offset]?
  | 85 => shard85[offset]?
  | _ => none

end KIP126.Computation.LinProofs.RawData
