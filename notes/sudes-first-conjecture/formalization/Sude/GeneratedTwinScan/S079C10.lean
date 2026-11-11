import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12923)) 166985773 167018541 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 166985773 167018541).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12923 166985773 167018541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12924)) 167018541 167051309 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 167018541 167051309).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12924 167018541 167051309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12926)) 167051309 167084077 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 167051309 167084077).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12926 167051309 167084077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12927)) 167084077 167116845 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 167084077 167116845).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12927 167084077 167116845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 166985773 167051309).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 166985773 ≤ 167018541)
    (by decide : 167018541 ≤ 167051309) block0 block1

theorem join_0_1 : (twinPrimeSegment 167051309 167116845).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 167051309 ≤ 167084077)
    (by decide : 167084077 ≤ 167116845) block2 block3

theorem join_1_0 : (twinPrimeSegment 166985773 167116845).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 166985773 ≤ 167051309)
    (by decide : 167051309 ≤ 167116845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 166985773 167116845).card = 498 := join_1_0

end S079C10
end Sude.GeneratedTwinScan
