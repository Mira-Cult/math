import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S162C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18443)) 340131885 340164653 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 340131885 340164653).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18443 340131885 340164653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18444)) 340164653 340197421 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 340164653 340197421).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18444 340164653 340197421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18445)) 340197421 340230189 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 340197421 340230189).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18445 340197421 340230189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18446)) 340230189 340262957 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 340230189 340262957).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18446 340230189 340262957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 340131885 340197421).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 340131885 ≤ 340164653)
    (by decide : 340164653 ≤ 340197421) block0 block1

theorem join_0_1 : (twinPrimeSegment 340197421 340262957).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 340197421 ≤ 340230189)
    (by decide : 340230189 ≤ 340262957) block2 block3

theorem join_1_0 : (twinPrimeSegment 340131885 340262957).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 340131885 ≤ 340197421)
    (by decide : 340197421 ≤ 340262957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 340131885 340262957).card = 467 := join_1_0

end S162C03
end Sude.GeneratedTwinScan
