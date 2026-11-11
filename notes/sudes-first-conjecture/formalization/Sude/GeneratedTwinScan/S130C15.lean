import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16571)) 274595885 274628653 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 274595885 274628653).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16571 274595885 274628653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16572)) 274628653 274661421 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 274628653 274661421).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16572 274628653 274661421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16573)) 274661421 274694189 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 274661421 274694189).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16573 274661421 274694189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16574)) 274694189 274726957 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 274694189 274726957).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16574 274694189 274726957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 274595885 274661421).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 274595885 ≤ 274628653)
    (by decide : 274628653 ≤ 274661421) block0 block1

theorem join_0_1 : (twinPrimeSegment 274661421 274726957).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 274661421 ≤ 274694189)
    (by decide : 274694189 ≤ 274726957) block2 block3

theorem join_1_0 : (twinPrimeSegment 274595885 274726957).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 274595885 ≤ 274661421)
    (by decide : 274661421 ≤ 274726957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 274595885 274726957).card = 473 := join_1_0

end S130C15
end Sude.GeneratedTwinScan
