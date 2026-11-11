import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16135)) 260309037 260341805 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 260309037 260341805).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16135 260309037 260341805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16136)) 260341805 260374573 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 260341805 260374573).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16136 260341805 260374573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16137)) 260374573 260407341 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 260374573 260407341).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16137 260374573 260407341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16138)) 260407341 260440109 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 260407341 260440109).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16138 260407341 260440109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 260309037 260374573).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 260309037 ≤ 260341805)
    (by decide : 260341805 ≤ 260374573) block0 block1

theorem join_0_1 : (twinPrimeSegment 260374573 260440109).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 260374573 ≤ 260407341)
    (by decide : 260407341 ≤ 260440109) block2 block3

theorem join_1_0 : (twinPrimeSegment 260309037 260440109).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 260309037 ≤ 260374573)
    (by decide : 260374573 ≤ 260440109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 260309037 260440109).card = 451 := join_1_0

end S124C02
end Sude.GeneratedTwinScan
