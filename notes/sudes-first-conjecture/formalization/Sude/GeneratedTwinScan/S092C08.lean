import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13929)) 193986605 194019373 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 193986605 194019373).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13929 193986605 194019373
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13930)) 194019373 194052141 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 194019373 194052141).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13930 194019373 194052141
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13931)) 194052141 194084909 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 194052141 194084909).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13931 194052141 194084909
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13932)) 194084909 194117677 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 194084909 194117677).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13932 194084909 194117677
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 193986605 194052141).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 193986605 ≤ 194019373)
    (by decide : 194019373 ≤ 194052141) block0 block1

theorem join_0_1 : (twinPrimeSegment 194052141 194117677).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 194052141 ≤ 194084909)
    (by decide : 194084909 ≤ 194117677) block2 block3

theorem join_1_0 : (twinPrimeSegment 193986605 194117677).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 193986605 ≤ 194052141)
    (by decide : 194052141 ≤ 194117677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 193986605 194117677).card = 458 := join_1_0

end S092C08
end Sude.GeneratedTwinScan
