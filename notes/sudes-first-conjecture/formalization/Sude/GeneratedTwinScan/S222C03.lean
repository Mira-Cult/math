import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S222C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21586)) 465961005 465993773 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 465961005 465993773).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21586 465961005 465993773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21587)) 465993773 466026541 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 465993773 466026541).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21587 465993773 466026541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21588)) 466026541 466059309 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 466026541 466059309).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21588 466026541 466059309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21589)) 466059309 466092077 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 466059309 466092077).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21589 466059309 466092077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 465961005 466026541).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 465961005 ≤ 465993773)
    (by decide : 465993773 ≤ 466026541) block0 block1

theorem join_0_1 : (twinPrimeSegment 466026541 466092077).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 466026541 ≤ 466059309)
    (by decide : 466059309 ≤ 466092077) block2 block3

theorem join_1_0 : (twinPrimeSegment 465961005 466092077).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 465961005 ≤ 466026541)
    (by decide : 466026541 ≤ 466092077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 465961005 466092077).card = 427 := join_1_0

end S222C03
end Sude.GeneratedTwinScan
