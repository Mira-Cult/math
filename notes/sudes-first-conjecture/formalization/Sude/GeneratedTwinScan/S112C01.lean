import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S112C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15331)) 235012141 235044909 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 235012141 235044909).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15331 235012141 235044909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15332)) 235044909 235077677 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 235044909 235077677).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15332 235044909 235077677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15333)) 235077677 235110445 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 235077677 235110445).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15333 235077677 235110445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15334)) 235110445 235143213 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 235110445 235143213).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15334 235110445 235143213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 235012141 235077677).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 235012141 ≤ 235044909)
    (by decide : 235044909 ≤ 235077677) block0 block1

theorem join_0_1 : (twinPrimeSegment 235077677 235143213).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 235077677 ≤ 235110445)
    (by decide : 235110445 ≤ 235143213) block2 block3

theorem join_1_0 : (twinPrimeSegment 235012141 235143213).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 235012141 ≤ 235077677)
    (by decide : 235077677 ≤ 235143213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 235012141 235143213).card = 463 := join_1_0

end S112C01
end Sude.GeneratedTwinScan
