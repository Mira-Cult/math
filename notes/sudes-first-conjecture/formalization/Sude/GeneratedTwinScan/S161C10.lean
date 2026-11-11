import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S161C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18411)) 338952237 338985005 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 338952237 338985005).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18411 338952237 338985005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18412)) 338985005 339017773 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 338985005 339017773).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18412 338985005 339017773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18413)) 339017773 339050541 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 339017773 339050541).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18413 339017773 339050541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18414)) 339050541 339083309 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 339050541 339083309).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18414 339050541 339083309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 338952237 339017773).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 338952237 ≤ 338985005)
    (by decide : 338985005 ≤ 339017773) block0 block1

theorem join_0_1 : (twinPrimeSegment 339017773 339083309).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 339017773 ≤ 339050541)
    (by decide : 339050541 ≤ 339083309) block2 block3

theorem join_1_0 : (twinPrimeSegment 338952237 339083309).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 338952237 ≤ 339017773)
    (by decide : 339017773 ≤ 339083309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 338952237 339083309).card = 449 := join_1_0

end S161C10
end Sude.GeneratedTwinScan
