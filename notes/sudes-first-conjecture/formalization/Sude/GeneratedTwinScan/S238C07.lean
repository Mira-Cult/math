import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22362)) 500039725 500072493 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 500039725 500072493).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22362 500039725 500072493
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22363)) 500072493 500105261 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 500072493 500105261).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22363 500072493 500105261
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22363)) 500105261 500138029 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 500105261 500138029).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22363 500105261 500138029
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22364)) 500138029 500170797 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 500138029 500170797).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22364 500138029 500170797
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 500039725 500105261).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 500039725 ≤ 500072493)
    (by decide : 500072493 ≤ 500105261) block0 block1

theorem join_0_1 : (twinPrimeSegment 500105261 500170797).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 500105261 ≤ 500138029)
    (by decide : 500138029 ≤ 500170797) block2 block3

theorem join_1_0 : (twinPrimeSegment 500039725 500170797).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 500039725 ≤ 500105261)
    (by decide : 500105261 ≤ 500170797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 500039725 500170797).card = 416 := join_1_0

end S238C07
end Sude.GeneratedTwinScan
