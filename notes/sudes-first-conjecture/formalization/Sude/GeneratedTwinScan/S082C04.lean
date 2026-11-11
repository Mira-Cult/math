import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13134)) 172490797 172523565 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 172490797 172523565).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13134 172490797 172523565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13136)) 172523565 172556333 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 172523565 172556333).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13136 172523565 172556333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13137)) 172556333 172589101 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 172556333 172589101).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13137 172556333 172589101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13138)) 172589101 172621869 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 172589101 172621869).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13138 172589101 172621869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 172490797 172556333).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 172490797 ≤ 172523565)
    (by decide : 172523565 ≤ 172556333) block0 block1

theorem join_0_1 : (twinPrimeSegment 172556333 172621869).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 172556333 ≤ 172589101)
    (by decide : 172589101 ≤ 172621869) block2 block3

theorem join_1_0 : (twinPrimeSegment 172490797 172621869).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 172490797 ≤ 172556333)
    (by decide : 172556333 ≤ 172621869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 172490797 172621869).card = 477 := join_1_0

end S082C04
end Sude.GeneratedTwinScan
