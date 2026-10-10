import KIP126.LinProgram.Tactic.LinSquareCertificate

/-! Kernel certificates for archived chunks 0 through 31.
The original strings and their order are unchanged. -/

namespace KIP126.LinE2.SquareDetection

set_option maxRecDepth 100000
set_option Elab.async false

-- Each original chunk is checked independently at the default heartbeat limit.
private theorem archivedChunk0 :
    chunksCheck ((RawData.relationChunks.toList.drop 0).take 1) = true := by
  lin_square_chunks 0 1

private theorem archivedChunk1 :
    chunksCheck ((RawData.relationChunks.toList.drop 1).take 1) = true := by
  lin_square_chunks 1 1

private theorem archivedChunk2 :
    chunksCheck ((RawData.relationChunks.toList.drop 2).take 1) = true := by
  lin_square_chunks 2 1

private theorem archivedChunk3 :
    chunksCheck ((RawData.relationChunks.toList.drop 3).take 1) = true := by
  lin_square_chunks 3 1

private theorem archivedChunk4 :
    chunksCheck ((RawData.relationChunks.toList.drop 4).take 1) = true := by
  lin_square_chunks 4 1

private theorem archivedChunk5 :
    chunksCheck ((RawData.relationChunks.toList.drop 5).take 1) = true := by
  lin_square_chunks 5 1

private theorem archivedChunk6 :
    chunksCheck ((RawData.relationChunks.toList.drop 6).take 1) = true := by
  lin_square_chunks 6 1

private theorem archivedChunk7 :
    chunksCheck ((RawData.relationChunks.toList.drop 7).take 1) = true := by
  lin_square_chunks 7 1

private theorem archivedChunk8 :
    chunksCheck ((RawData.relationChunks.toList.drop 8).take 1) = true := by
  lin_square_chunks 8 1

private theorem archivedChunk9 :
    chunksCheck ((RawData.relationChunks.toList.drop 9).take 1) = true := by
  lin_square_chunks 9 1

private theorem archivedChunk10 :
    chunksCheck ((RawData.relationChunks.toList.drop 10).take 1) = true := by
  lin_square_chunks 10 1

private theorem archivedChunk11 :
    chunksCheck ((RawData.relationChunks.toList.drop 11).take 1) = true := by
  lin_square_chunks 11 1

private theorem archivedChunk12 :
    chunksCheck ((RawData.relationChunks.toList.drop 12).take 1) = true := by
  lin_square_chunks 12 1

private theorem archivedChunk13 :
    chunksCheck ((RawData.relationChunks.toList.drop 13).take 1) = true := by
  lin_square_chunks 13 1

private theorem archivedChunk14 :
    chunksCheck ((RawData.relationChunks.toList.drop 14).take 1) = true := by
  lin_square_chunks 14 1

private theorem archivedChunk15 :
    chunksCheck ((RawData.relationChunks.toList.drop 15).take 1) = true := by
  lin_square_chunks 15 1

private theorem archivedChunk16 :
    chunksCheck ((RawData.relationChunks.toList.drop 16).take 1) = true := by
  lin_square_chunks 16 1

private theorem archivedChunk17 :
    chunksCheck ((RawData.relationChunks.toList.drop 17).take 1) = true := by
  lin_square_chunks 17 1

private theorem archivedChunk18 :
    chunksCheck ((RawData.relationChunks.toList.drop 18).take 1) = true := by
  lin_square_chunks 18 1

private theorem archivedChunk19 :
    chunksCheck ((RawData.relationChunks.toList.drop 19).take 1) = true := by
  lin_square_chunks 19 1

private theorem archivedChunk20 :
    chunksCheck ((RawData.relationChunks.toList.drop 20).take 1) = true := by
  lin_square_chunks 20 1

private theorem archivedChunk21 :
    chunksCheck ((RawData.relationChunks.toList.drop 21).take 1) = true := by
  lin_square_chunks 21 1

private theorem archivedChunk22 :
    chunksCheck ((RawData.relationChunks.toList.drop 22).take 1) = true := by
  lin_square_chunks 22 1

private theorem archivedChunk23 :
    chunksCheck ((RawData.relationChunks.toList.drop 23).take 1) = true := by
  lin_square_chunks 23 1

private theorem archivedChunk24 :
    chunksCheck ((RawData.relationChunks.toList.drop 24).take 1) = true := by
  lin_square_chunks 24 1

private theorem archivedChunk25 :
    chunksCheck ((RawData.relationChunks.toList.drop 25).take 1) = true := by
  lin_square_chunks 25 1

private theorem archivedChunk26 :
    chunksCheck ((RawData.relationChunks.toList.drop 26).take 1) = true := by
  lin_square_chunks 26 1

private theorem archivedChunk27 :
    chunksCheck ((RawData.relationChunks.toList.drop 27).take 1) = true := by
  lin_square_chunks 27 1

private theorem archivedChunk28 :
    chunksCheck ((RawData.relationChunks.toList.drop 28).take 1) = true := by
  lin_square_chunks 28 1

private theorem archivedChunk29 :
    chunksCheck ((RawData.relationChunks.toList.drop 29).take 1) = true := by
  lin_square_chunks 29 1

private theorem archivedChunk30 :
    chunksCheck ((RawData.relationChunks.toList.drop 30).take 1) = true := by
  lin_square_chunks 30 1

private theorem archivedChunk31 :
    chunksCheck ((RawData.relationChunks.toList.drop 31).take 1) = true := by
  lin_square_chunks 31 1

/-- A bounded part of the complete archived relation certificate. -/
theorem archivedChunks_batch0 :
    chunksCheck ((RawData.relationChunks.toList.drop 0).take 32) = true := by
  lin_square_compose
    archivedChunk0 archivedChunk1 archivedChunk2 archivedChunk3
    archivedChunk4 archivedChunk5 archivedChunk6 archivedChunk7
    archivedChunk8 archivedChunk9 archivedChunk10 archivedChunk11
    archivedChunk12 archivedChunk13 archivedChunk14 archivedChunk15
    archivedChunk16 archivedChunk17 archivedChunk18 archivedChunk19
    archivedChunk20 archivedChunk21 archivedChunk22 archivedChunk23
    archivedChunk24 archivedChunk25 archivedChunk26 archivedChunk27
    archivedChunk28 archivedChunk29 archivedChunk30 archivedChunk31

end KIP126.LinE2.SquareDetection
