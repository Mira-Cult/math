import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19068)) 363593773 363626541 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 363593773 363626541).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19068 363593773 363626541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19069)) 363626541 363659309 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 363626541 363659309).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19069 363626541 363659309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19070)) 363659309 363692077 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 363659309 363692077).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19070 363659309 363692077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19071)) 363692077 363724845 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 363692077 363724845).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19071 363692077 363724845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 363593773 363659309).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 363593773 ≤ 363626541)
    (by decide : 363626541 ≤ 363659309) block0 block1

theorem join_0_1 : (twinPrimeSegment 363659309 363724845).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 363659309 ≤ 363692077)
    (by decide : 363692077 ≤ 363724845) block2 block3

theorem join_1_0 : (twinPrimeSegment 363593773 363724845).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 363593773 ≤ 363659309)
    (by decide : 363659309 ≤ 363724845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 363593773 363724845).card = 482 := join_1_0

end S173C06
end Sude.GeneratedTwinScan
