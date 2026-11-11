import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14631)) 214040621 214073389 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 214040621 214073389).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14631 214040621 214073389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14632)) 214073389 214106157 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 214073389 214106157).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14632 214073389 214106157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14633)) 214106157 214138925 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 214106157 214138925).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14633 214106157 214138925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14634)) 214138925 214171693 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 214138925 214171693).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14634 214138925 214171693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 214040621 214106157).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 214040621 ≤ 214073389)
    (by decide : 214073389 ≤ 214106157) block0 block1

theorem join_0_1 : (twinPrimeSegment 214106157 214171693).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 214106157 ≤ 214138925)
    (by decide : 214138925 ≤ 214171693) block2 block3

theorem join_1_0 : (twinPrimeSegment 214040621 214171693).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 214040621 ≤ 214106157)
    (by decide : 214106157 ≤ 214171693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 214040621 214171693).card = 465 := join_1_0

end S102C01
end Sude.GeneratedTwinScan
