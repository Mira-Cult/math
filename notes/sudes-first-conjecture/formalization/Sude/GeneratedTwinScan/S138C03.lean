import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S138C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17024)) 289800237 289833005 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 289800237 289833005).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17024 289800237 289833005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17025)) 289833005 289865773 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 289833005 289865773).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17025 289833005 289865773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17026)) 289865773 289898541 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 289865773 289898541).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17026 289865773 289898541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17027)) 289898541 289931309 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 289898541 289931309).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17027 289898541 289931309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 289800237 289865773).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 289800237 ≤ 289833005)
    (by decide : 289833005 ≤ 289865773) block0 block1

theorem join_0_1 : (twinPrimeSegment 289865773 289931309).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 289865773 ≤ 289898541)
    (by decide : 289898541 ≤ 289931309) block2 block3

theorem join_1_0 : (twinPrimeSegment 289800237 289931309).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 289800237 ≤ 289865773)
    (by decide : 289865773 ≤ 289931309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 289800237 289931309).card = 438 := join_1_0

end S138C03
end Sude.GeneratedTwinScan
