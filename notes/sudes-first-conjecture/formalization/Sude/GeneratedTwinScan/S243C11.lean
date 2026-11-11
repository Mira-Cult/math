import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22607)) 511049773 511082541 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 511049773 511082541).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22607 511049773 511082541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22607)) 511082541 511115309 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 511082541 511115309).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22607 511082541 511115309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22608)) 511115309 511148077 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 511115309 511148077).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22608 511115309 511148077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22609)) 511148077 511180845 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 511148077 511180845).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22609 511148077 511180845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 511049773 511115309).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 511049773 ≤ 511082541)
    (by decide : 511082541 ≤ 511115309) block0 block1

theorem join_0_1 : (twinPrimeSegment 511115309 511180845).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 511115309 ≤ 511148077)
    (by decide : 511148077 ≤ 511180845) block2 block3

theorem join_1_0 : (twinPrimeSegment 511049773 511180845).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 511049773 ≤ 511115309)
    (by decide : 511115309 ≤ 511180845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 511049773 511180845).card = 429 := join_1_0

end S243C11
end Sude.GeneratedTwinScan
