import KIP126.LinProgram.Tactic.LinSquareCertificate

/-! Kernel certificates for archived chunks 192 through 223.
The original strings and their order are unchanged. -/

namespace KIP126.LinE2.SquareDetection

set_option maxRecDepth 100000
set_option Elab.async false

-- Each original chunk is checked independently at the default heartbeat limit.
private theorem archivedChunk192 :
    chunksCheck ((RawData.relationChunks.toList.drop 192).take 1) = true := by
  lin_square_chunks 192 1

private theorem archivedChunk193 :
    chunksCheck ((RawData.relationChunks.toList.drop 193).take 1) = true := by
  lin_square_chunks 193 1

private theorem archivedChunk194 :
    chunksCheck ((RawData.relationChunks.toList.drop 194).take 1) = true := by
  lin_square_chunks 194 1

private theorem archivedChunk195 :
    chunksCheck ((RawData.relationChunks.toList.drop 195).take 1) = true := by
  lin_square_chunks 195 1

private theorem archivedChunk196 :
    chunksCheck ((RawData.relationChunks.toList.drop 196).take 1) = true := by
  lin_square_chunks 196 1

private theorem archivedChunk197 :
    chunksCheck ((RawData.relationChunks.toList.drop 197).take 1) = true := by
  lin_square_chunks 197 1

private theorem archivedChunk198 :
    chunksCheck ((RawData.relationChunks.toList.drop 198).take 1) = true := by
  lin_square_chunks 198 1

private theorem archivedChunk199 :
    chunksCheck ((RawData.relationChunks.toList.drop 199).take 1) = true := by
  lin_square_chunks 199 1

private theorem archivedChunk200 :
    chunksCheck ((RawData.relationChunks.toList.drop 200).take 1) = true := by
  lin_square_chunks 200 1

private theorem archivedChunk201 :
    chunksCheck ((RawData.relationChunks.toList.drop 201).take 1) = true := by
  lin_square_chunks 201 1

private theorem archivedChunk202 :
    chunksCheck ((RawData.relationChunks.toList.drop 202).take 1) = true := by
  lin_square_chunks 202 1

private theorem archivedChunk203 :
    chunksCheck ((RawData.relationChunks.toList.drop 203).take 1) = true := by
  lin_square_chunks 203 1

private theorem archivedChunk204 :
    chunksCheck ((RawData.relationChunks.toList.drop 204).take 1) = true := by
  lin_square_chunks 204 1

private theorem archivedChunk205 :
    chunksCheck ((RawData.relationChunks.toList.drop 205).take 1) = true := by
  lin_square_chunks 205 1

private theorem archivedChunk206 :
    chunksCheck ((RawData.relationChunks.toList.drop 206).take 1) = true := by
  lin_square_chunks 206 1

private theorem archivedChunk207 :
    chunksCheck ((RawData.relationChunks.toList.drop 207).take 1) = true := by
  lin_square_chunks 207 1

private theorem archivedChunk208 :
    chunksCheck ((RawData.relationChunks.toList.drop 208).take 1) = true := by
  lin_square_chunks 208 1

private theorem archivedChunk209 :
    chunksCheck ((RawData.relationChunks.toList.drop 209).take 1) = true := by
  lin_square_chunks 209 1

private theorem archivedChunk210 :
    chunksCheck ((RawData.relationChunks.toList.drop 210).take 1) = true := by
  lin_square_chunks 210 1

private theorem archivedChunk211 :
    chunksCheck ((RawData.relationChunks.toList.drop 211).take 1) = true := by
  lin_square_chunks 211 1

private theorem archivedChunk212 :
    chunksCheck ((RawData.relationChunks.toList.drop 212).take 1) = true := by
  lin_square_chunks 212 1

private theorem archivedChunk213 :
    chunksCheck ((RawData.relationChunks.toList.drop 213).take 1) = true := by
  lin_square_chunks 213 1

private theorem archivedChunk214 :
    chunksCheck ((RawData.relationChunks.toList.drop 214).take 1) = true := by
  lin_square_chunks 214 1

private theorem archivedChunk215 :
    chunksCheck ((RawData.relationChunks.toList.drop 215).take 1) = true := by
  lin_square_chunks 215 1

private theorem archivedChunk216 :
    chunksCheck ((RawData.relationChunks.toList.drop 216).take 1) = true := by
  lin_square_chunks 216 1

private theorem archivedChunk217 :
    chunksCheck ((RawData.relationChunks.toList.drop 217).take 1) = true := by
  lin_square_chunks 217 1

private theorem archivedChunk218 :
    chunksCheck ((RawData.relationChunks.toList.drop 218).take 1) = true := by
  lin_square_chunks 218 1

private theorem archivedChunk219 :
    chunksCheck ((RawData.relationChunks.toList.drop 219).take 1) = true := by
  lin_square_chunks 219 1

private theorem archivedChunk220 :
    chunksCheck ((RawData.relationChunks.toList.drop 220).take 1) = true := by
  lin_square_chunks 220 1

private theorem archivedChunk221 :
    chunksCheck ((RawData.relationChunks.toList.drop 221).take 1) = true := by
  lin_square_chunks 221 1

private theorem archivedChunk222 :
    chunksCheck ((RawData.relationChunks.toList.drop 222).take 1) = true := by
  lin_square_chunks 222 1

private theorem archivedChunk223 :
    chunksCheck ((RawData.relationChunks.toList.drop 223).take 1) = true := by
  lin_square_chunks 223 1

/-- A bounded part of the complete archived relation certificate. -/
theorem archivedChunks_batch6 :
    chunksCheck ((RawData.relationChunks.toList.drop 192).take 32) = true := by
  lin_square_compose
    archivedChunk192 archivedChunk193 archivedChunk194 archivedChunk195
    archivedChunk196 archivedChunk197 archivedChunk198 archivedChunk199
    archivedChunk200 archivedChunk201 archivedChunk202 archivedChunk203
    archivedChunk204 archivedChunk205 archivedChunk206 archivedChunk207
    archivedChunk208 archivedChunk209 archivedChunk210 archivedChunk211
    archivedChunk212 archivedChunk213 archivedChunk214 archivedChunk215
    archivedChunk216 archivedChunk217 archivedChunk218 archivedChunk219
    archivedChunk220 archivedChunk221 archivedChunk222 archivedChunk223

end KIP126.LinE2.SquareDetection
