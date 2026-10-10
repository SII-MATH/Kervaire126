import KIP126.LinProgram.Tactic.LinSquareCertificate

/-! Kernel certificates for archived chunks 160 through 191.
The original strings and their order are unchanged. -/

namespace KIP126.LinE2.SquareDetection

set_option maxRecDepth 100000
set_option Elab.async false

-- Each original chunk is checked independently at the default heartbeat limit.
private theorem archivedChunk160 :
    chunksCheck ((RawData.relationChunks.toList.drop 160).take 1) = true := by
  lin_square_chunks 160 1

private theorem archivedChunk161 :
    chunksCheck ((RawData.relationChunks.toList.drop 161).take 1) = true := by
  lin_square_chunks 161 1

private theorem archivedChunk162 :
    chunksCheck ((RawData.relationChunks.toList.drop 162).take 1) = true := by
  lin_square_chunks 162 1

private theorem archivedChunk163 :
    chunksCheck ((RawData.relationChunks.toList.drop 163).take 1) = true := by
  lin_square_chunks 163 1

private theorem archivedChunk164 :
    chunksCheck ((RawData.relationChunks.toList.drop 164).take 1) = true := by
  lin_square_chunks 164 1

private theorem archivedChunk165 :
    chunksCheck ((RawData.relationChunks.toList.drop 165).take 1) = true := by
  lin_square_chunks 165 1

private theorem archivedChunk166 :
    chunksCheck ((RawData.relationChunks.toList.drop 166).take 1) = true := by
  lin_square_chunks 166 1

private theorem archivedChunk167 :
    chunksCheck ((RawData.relationChunks.toList.drop 167).take 1) = true := by
  lin_square_chunks 167 1

private theorem archivedChunk168 :
    chunksCheck ((RawData.relationChunks.toList.drop 168).take 1) = true := by
  lin_square_chunks 168 1

private theorem archivedChunk169 :
    chunksCheck ((RawData.relationChunks.toList.drop 169).take 1) = true := by
  lin_square_chunks 169 1

private theorem archivedChunk170 :
    chunksCheck ((RawData.relationChunks.toList.drop 170).take 1) = true := by
  lin_square_chunks 170 1

private theorem archivedChunk171 :
    chunksCheck ((RawData.relationChunks.toList.drop 171).take 1) = true := by
  lin_square_chunks 171 1

private theorem archivedChunk172 :
    chunksCheck ((RawData.relationChunks.toList.drop 172).take 1) = true := by
  lin_square_chunks 172 1

private theorem archivedChunk173 :
    chunksCheck ((RawData.relationChunks.toList.drop 173).take 1) = true := by
  lin_square_chunks 173 1

private theorem archivedChunk174 :
    chunksCheck ((RawData.relationChunks.toList.drop 174).take 1) = true := by
  lin_square_chunks 174 1

private theorem archivedChunk175 :
    chunksCheck ((RawData.relationChunks.toList.drop 175).take 1) = true := by
  lin_square_chunks 175 1

private theorem archivedChunk176 :
    chunksCheck ((RawData.relationChunks.toList.drop 176).take 1) = true := by
  lin_square_chunks 176 1

private theorem archivedChunk177 :
    chunksCheck ((RawData.relationChunks.toList.drop 177).take 1) = true := by
  lin_square_chunks 177 1

private theorem archivedChunk178 :
    chunksCheck ((RawData.relationChunks.toList.drop 178).take 1) = true := by
  lin_square_chunks 178 1

private theorem archivedChunk179 :
    chunksCheck ((RawData.relationChunks.toList.drop 179).take 1) = true := by
  lin_square_chunks 179 1

private theorem archivedChunk180 :
    chunksCheck ((RawData.relationChunks.toList.drop 180).take 1) = true := by
  lin_square_chunks 180 1

private theorem archivedChunk181 :
    chunksCheck ((RawData.relationChunks.toList.drop 181).take 1) = true := by
  lin_square_chunks 181 1

private theorem archivedChunk182 :
    chunksCheck ((RawData.relationChunks.toList.drop 182).take 1) = true := by
  lin_square_chunks 182 1

private theorem archivedChunk183 :
    chunksCheck ((RawData.relationChunks.toList.drop 183).take 1) = true := by
  lin_square_chunks 183 1

private theorem archivedChunk184 :
    chunksCheck ((RawData.relationChunks.toList.drop 184).take 1) = true := by
  lin_square_chunks 184 1

private theorem archivedChunk185 :
    chunksCheck ((RawData.relationChunks.toList.drop 185).take 1) = true := by
  lin_square_chunks 185 1

private theorem archivedChunk186 :
    chunksCheck ((RawData.relationChunks.toList.drop 186).take 1) = true := by
  lin_square_chunks 186 1

private theorem archivedChunk187 :
    chunksCheck ((RawData.relationChunks.toList.drop 187).take 1) = true := by
  lin_square_chunks 187 1

private theorem archivedChunk188 :
    chunksCheck ((RawData.relationChunks.toList.drop 188).take 1) = true := by
  lin_square_chunks 188 1

private theorem archivedChunk189 :
    chunksCheck ((RawData.relationChunks.toList.drop 189).take 1) = true := by
  lin_square_chunks 189 1

private theorem archivedChunk190 :
    chunksCheck ((RawData.relationChunks.toList.drop 190).take 1) = true := by
  lin_square_chunks 190 1

private theorem archivedChunk191 :
    chunksCheck ((RawData.relationChunks.toList.drop 191).take 1) = true := by
  lin_square_chunks 191 1

/-- A bounded part of the complete archived relation certificate. -/
theorem archivedChunks_batch5 :
    chunksCheck ((RawData.relationChunks.toList.drop 160).take 32) = true := by
  lin_square_compose
    archivedChunk160 archivedChunk161 archivedChunk162 archivedChunk163
    archivedChunk164 archivedChunk165 archivedChunk166 archivedChunk167
    archivedChunk168 archivedChunk169 archivedChunk170 archivedChunk171
    archivedChunk172 archivedChunk173 archivedChunk174 archivedChunk175
    archivedChunk176 archivedChunk177 archivedChunk178 archivedChunk179
    archivedChunk180 archivedChunk181 archivedChunk182 archivedChunk183
    archivedChunk184 archivedChunk185 archivedChunk186 archivedChunk187
    archivedChunk188 archivedChunk189 archivedChunk190 archivedChunk191

end KIP126.LinE2.SquareDetection
