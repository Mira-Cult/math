import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21314)) 454295597 454328365 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 454295597 454328365).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21314 454295597 454328365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21315)) 454328365 454361133 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 454328365 454361133).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21315 454328365 454361133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21316)) 454361133 454393901 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 454361133 454393901).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21316 454361133 454393901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21317)) 454393901 454426669 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 454393901 454426669).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21317 454393901 454426669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 454295597 454361133).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 454295597 ≤ 454328365)
    (by decide : 454328365 ≤ 454361133) block0 block1

theorem join_0_1 : (twinPrimeSegment 454361133 454426669).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 454361133 ≤ 454393901)
    (by decide : 454393901 ≤ 454426669) block2 block3

theorem join_1_0 : (twinPrimeSegment 454295597 454426669).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 454295597 ≤ 454361133)
    (by decide : 454361133 ≤ 454426669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 454295597 454426669).card = 451 := join_1_0

end S216C10
end Sude.GeneratedTwinScan
