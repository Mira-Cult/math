import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17847)) 318505005 318537773 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 318505005 318537773).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17847 318505005 318537773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17848)) 318537773 318570541 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 318537773 318570541).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17848 318537773 318570541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17849)) 318570541 318603309 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 318570541 318603309).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17849 318570541 318603309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17850)) 318603309 318636077 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 318603309 318636077).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17850 318603309 318636077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 318505005 318570541).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 318505005 ≤ 318537773)
    (by decide : 318537773 ≤ 318570541) block0 block1

theorem join_0_1 : (twinPrimeSegment 318570541 318636077).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 318570541 ≤ 318603309)
    (by decide : 318603309 ≤ 318636077) block2 block3

theorem join_1_0 : (twinPrimeSegment 318505005 318636077).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 318505005 ≤ 318570541)
    (by decide : 318570541 ≤ 318636077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 318505005 318636077).card = 484 := join_1_0

end S151C14
end Sude.GeneratedTwinScan
