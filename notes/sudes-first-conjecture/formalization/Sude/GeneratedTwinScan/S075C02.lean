import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12553)) 157548589 157581357 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 157548589 157581357).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12553 157548589 157581357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12554)) 157581357 157614125 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 157581357 157614125).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12554 157581357 157614125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12555)) 157614125 157646893 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 157614125 157646893).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12555 157614125 157646893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12557)) 157646893 157679661 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 157646893 157679661).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12557 157646893 157679661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 157548589 157614125).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 157548589 ≤ 157581357)
    (by decide : 157581357 ≤ 157614125) block0 block1

theorem join_0_1 : (twinPrimeSegment 157614125 157679661).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 157614125 ≤ 157646893)
    (by decide : 157646893 ≤ 157679661) block2 block3

theorem join_1_0 : (twinPrimeSegment 157548589 157679661).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 157548589 ≤ 157614125)
    (by decide : 157614125 ≤ 157679661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 157548589 157679661).card = 463 := join_1_0

end S075C02
end Sude.GeneratedTwinScan
