import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S086C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13503)) 182321197 182353965 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 182321197 182353965).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13503 182321197 182353965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13505)) 182353965 182386733 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 182353965 182386733).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13505 182353965 182386733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13506)) 182386733 182419501 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 182386733 182419501).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13506 182386733 182419501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13507)) 182419501 182452269 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 182419501 182452269).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13507 182419501 182452269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 182321197 182386733).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 182321197 ≤ 182353965)
    (by decide : 182353965 ≤ 182386733) block0 block1

theorem join_0_1 : (twinPrimeSegment 182386733 182452269).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 182386733 ≤ 182419501)
    (by decide : 182419501 ≤ 182452269) block2 block3

theorem join_1_0 : (twinPrimeSegment 182321197 182452269).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 182321197 ≤ 182386733)
    (by decide : 182386733 ≤ 182452269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 182321197 182452269).card = 470 := join_1_0

end S086C15
end Sude.GeneratedTwinScan
