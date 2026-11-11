import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S134C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16764)) 281018413 281051181 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 281018413 281051181).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16764 281018413 281051181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16765)) 281051181 281083949 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 281051181 281083949).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16765 281051181 281083949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16766)) 281083949 281116717 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 281083949 281116717).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16766 281083949 281116717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16767)) 281116717 281149485 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 281116717 281149485).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16767 281116717 281149485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 281018413 281083949).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 281018413 ≤ 281051181)
    (by decide : 281051181 ≤ 281083949) block0 block1

theorem join_0_1 : (twinPrimeSegment 281083949 281149485).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 281083949 ≤ 281116717)
    (by decide : 281116717 ≤ 281149485) block2 block3

theorem join_1_0 : (twinPrimeSegment 281018413 281149485).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 281018413 ≤ 281083949)
    (by decide : 281083949 ≤ 281149485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 281018413 281149485).card = 437 := join_1_0

end S134C00
end Sude.GeneratedTwinScan
