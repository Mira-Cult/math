import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S235C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22241)) 494665773 494698541 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 494665773 494698541).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22241 494665773 494698541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22242)) 494698541 494731309 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 494698541 494731309).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22242 494698541 494731309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22243)) 494731309 494764077 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 494731309 494764077).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22243 494731309 494764077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22244)) 494764077 494796845 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 494764077 494796845).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22244 494764077 494796845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 494665773 494731309).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 494665773 ≤ 494698541)
    (by decide : 494698541 ≤ 494731309) block0 block1

theorem join_0_1 : (twinPrimeSegment 494731309 494796845).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 494731309 ≤ 494764077)
    (by decide : 494764077 ≤ 494796845) block2 block3

theorem join_1_0 : (twinPrimeSegment 494665773 494796845).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 494665773 ≤ 494731309)
    (by decide : 494731309 ≤ 494796845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 494665773 494796845).card = 457 := join_1_0

end S235C14
end Sude.GeneratedTwinScan
