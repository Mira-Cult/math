import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20416)) 416809005 416841773 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 416809005 416841773).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20416 416809005 416841773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20417)) 416841773 416874541 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 416841773 416874541).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20417 416841773 416874541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20418)) 416874541 416907309 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 416874541 416907309).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20418 416874541 416907309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20419)) 416907309 416940077 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 416907309 416940077).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20419 416907309 416940077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 416809005 416874541).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 416809005 ≤ 416841773)
    (by decide : 416841773 ≤ 416874541) block0 block1

theorem join_0_1 : (twinPrimeSegment 416874541 416940077).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 416874541 ≤ 416907309)
    (by decide : 416907309 ≤ 416940077) block2 block3

theorem join_1_0 : (twinPrimeSegment 416809005 416940077).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 416809005 ≤ 416874541)
    (by decide : 416874541 ≤ 416940077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 416809005 416940077).card = 465 := join_1_0

end S198C12
end Sude.GeneratedTwinScan
