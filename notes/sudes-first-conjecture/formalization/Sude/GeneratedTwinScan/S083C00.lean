import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S083C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13194)) 174063661 174096429 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 174063661 174096429).card = 143 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13194 174063661 174096429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13195)) 174096429 174129197 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 174096429 174129197).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13195 174096429 174129197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13197)) 174129197 174161965 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 174129197 174161965).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13197 174129197 174161965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13198)) 174161965 174194733 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 174161965 174194733).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13198 174161965 174194733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 174063661 174129197).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 174063661 ≤ 174096429)
    (by decide : 174096429 ≤ 174129197) block0 block1

theorem join_0_1 : (twinPrimeSegment 174129197 174194733).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 174129197 ≤ 174161965)
    (by decide : 174161965 ≤ 174194733) block2 block3

theorem join_1_0 : (twinPrimeSegment 174063661 174194733).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 174063661 ≤ 174129197)
    (by decide : 174129197 ≤ 174194733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 174063661 174194733).card = 517 := join_1_0

end S083C00
end Sude.GeneratedTwinScan
