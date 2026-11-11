import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14305)) 204603437 204636205 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 204603437 204636205).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14305 204603437 204636205
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14306)) 204636205 204668973 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 204636205 204668973).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14306 204636205 204668973
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14307)) 204668973 204701741 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 204668973 204701741).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14307 204668973 204701741
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14308)) 204701741 204734509 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 204701741 204734509).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14308 204701741 204734509
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 204603437 204668973).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 204603437 ≤ 204636205)
    (by decide : 204636205 ≤ 204668973) block0 block1

theorem join_0_1 : (twinPrimeSegment 204668973 204734509).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 204668973 ≤ 204701741)
    (by decide : 204701741 ≤ 204734509) block2 block3

theorem join_1_0 : (twinPrimeSegment 204603437 204734509).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 204603437 ≤ 204668973)
    (by decide : 204668973 ≤ 204734509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 204603437 204734509).card = 498 := join_1_0

end S097C09
end Sude.GeneratedTwinScan
