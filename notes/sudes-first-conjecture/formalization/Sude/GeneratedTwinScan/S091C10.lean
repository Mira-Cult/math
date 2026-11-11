import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13863)) 192151597 192184365 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 192151597 192184365).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13863 192151597 192184365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13864)) 192184365 192217133 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 192184365 192217133).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13864 192184365 192217133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13865)) 192217133 192249901 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 192217133 192249901).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13865 192217133 192249901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13866)) 192249901 192282669 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 192249901 192282669).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13866 192249901 192282669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 192151597 192217133).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 192151597 ≤ 192184365)
    (by decide : 192184365 ≤ 192217133) block0 block1

theorem join_0_1 : (twinPrimeSegment 192217133 192282669).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 192217133 ≤ 192249901)
    (by decide : 192249901 ≤ 192282669) block2 block3

theorem join_1_0 : (twinPrimeSegment 192151597 192282669).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 192151597 ≤ 192217133)
    (by decide : 192217133 ≤ 192282669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 192151597 192282669).card = 479 := join_1_0

end S091C10
end Sude.GeneratedTwinScan
