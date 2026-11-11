import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19175)) 367657005 367689773 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 367657005 367689773).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19175 367657005 367689773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19176)) 367689773 367722541 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 367689773 367722541).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19176 367689773 367722541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19176)) 367722541 367755309 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 367722541 367755309).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19176 367722541 367755309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19177)) 367755309 367788077 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 367755309 367788077).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19177 367755309 367788077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 367657005 367722541).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 367657005 ≤ 367689773)
    (by decide : 367689773 ≤ 367722541) block0 block1

theorem join_0_1 : (twinPrimeSegment 367722541 367788077).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 367722541 ≤ 367755309)
    (by decide : 367755309 ≤ 367788077) block2 block3

theorem join_1_0 : (twinPrimeSegment 367657005 367788077).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 367657005 ≤ 367722541)
    (by decide : 367722541 ≤ 367788077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 367657005 367788077).card = 464 := join_1_0

end S175C05
end Sude.GeneratedTwinScan
