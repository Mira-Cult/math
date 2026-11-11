import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S110C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15249)) 232521773 232554541 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 232521773 232554541).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15249 232521773 232554541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15250)) 232554541 232587309 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 232554541 232587309).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15250 232554541 232587309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15251)) 232587309 232620077 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 232587309 232620077).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15251 232587309 232620077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15252)) 232620077 232652845 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 232620077 232652845).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15252 232620077 232652845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 232521773 232587309).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 232521773 ≤ 232554541)
    (by decide : 232554541 ≤ 232587309) block0 block1

theorem join_0_1 : (twinPrimeSegment 232587309 232652845).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 232587309 ≤ 232620077)
    (by decide : 232620077 ≤ 232652845) block2 block3

theorem join_1_0 : (twinPrimeSegment 232521773 232652845).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 232521773 ≤ 232587309)
    (by decide : 232587309 ≤ 232652845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 232521773 232652845).card = 506 := join_1_0

end S110C14
end Sude.GeneratedTwinScan
