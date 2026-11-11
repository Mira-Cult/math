import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19893)) 395706413 395739181 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 395706413 395739181).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19893 395706413 395739181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19894)) 395739181 395771949 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 395739181 395771949).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19894 395739181 395771949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19894)) 395771949 395804717 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 395771949 395804717).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19894 395771949 395804717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19895)) 395804717 395837485 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 395804717 395837485).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19895 395804717 395837485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 395706413 395771949).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 395706413 ≤ 395739181)
    (by decide : 395739181 ≤ 395771949) block0 block1

theorem join_0_1 : (twinPrimeSegment 395771949 395837485).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 395771949 ≤ 395804717)
    (by decide : 395804717 ≤ 395837485) block2 block3

theorem join_1_0 : (twinPrimeSegment 395706413 395837485).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 395706413 ≤ 395771949)
    (by decide : 395771949 ≤ 395837485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 395706413 395837485).card = 430 := join_1_0

end S188C11
end Sude.GeneratedTwinScan
