import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S088C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13658)) 186515501 186548269 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 186515501 186548269).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13658 186515501 186548269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13659)) 186548269 186581037 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 186548269 186581037).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13659 186548269 186581037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13660)) 186581037 186613805 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 186581037 186613805).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13660 186581037 186613805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13661)) 186613805 186646573 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 186613805 186646573).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13661 186613805 186646573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 186515501 186581037).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 186515501 ≤ 186548269)
    (by decide : 186548269 ≤ 186581037) block0 block1

theorem join_0_1 : (twinPrimeSegment 186581037 186646573).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 186581037 ≤ 186613805)
    (by decide : 186613805 ≤ 186646573) block2 block3

theorem join_1_0 : (twinPrimeSegment 186515501 186646573).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 186515501 ≤ 186581037)
    (by decide : 186581037 ≤ 186646573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 186515501 186646573).card = 495 := join_1_0

end S088C15
end Sude.GeneratedTwinScan
