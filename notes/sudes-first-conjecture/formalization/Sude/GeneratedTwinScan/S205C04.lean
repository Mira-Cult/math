import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20747)) 430440493 430473261 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 430440493 430473261).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20747 430440493 430473261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20748)) 430473261 430506029 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 430473261 430506029).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20748 430473261 430506029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20749)) 430506029 430538797 = 83 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 430506029 430538797).card = 83 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20749 430506029 430538797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20750)) 430538797 430571565 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 430538797 430571565).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20750 430538797 430571565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 430440493 430506029).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 430440493 ≤ 430473261)
    (by decide : 430473261 ≤ 430506029) block0 block1

theorem join_0_1 : (twinPrimeSegment 430506029 430571565).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 430506029 ≤ 430538797)
    (by decide : 430538797 ≤ 430571565) block2 block3

theorem join_1_0 : (twinPrimeSegment 430440493 430571565).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 430440493 ≤ 430506029)
    (by decide : 430506029 ≤ 430571565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 430440493 430571565).card = 441 := join_1_0

end S205C04
end Sude.GeneratedTwinScan
