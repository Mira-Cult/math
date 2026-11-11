import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20112)) 404488237 404521005 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 404488237 404521005).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20112 404488237 404521005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20113)) 404521005 404553773 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 404521005 404553773).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20113 404521005 404553773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20114)) 404553773 404586541 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 404553773 404586541).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20114 404553773 404586541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20115)) 404586541 404619309 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 404586541 404619309).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20115 404586541 404619309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 404488237 404553773).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 404488237 ≤ 404521005)
    (by decide : 404521005 ≤ 404553773) block0 block1

theorem join_0_1 : (twinPrimeSegment 404553773 404619309).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 404553773 ≤ 404586541)
    (by decide : 404586541 ≤ 404619309) block2 block3

theorem join_1_0 : (twinPrimeSegment 404488237 404619309).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 404488237 ≤ 404553773)
    (by decide : 404553773 ≤ 404619309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 404488237 404619309).card = 430 := join_1_0

end S192C14
end Sude.GeneratedTwinScan
