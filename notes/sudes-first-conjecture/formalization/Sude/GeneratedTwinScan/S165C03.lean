import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18613)) 346423341 346456109 = 94 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 346423341 346456109).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18613 346423341 346456109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18614)) 346456109 346488877 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 346456109 346488877).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18614 346456109 346488877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18615)) 346488877 346521645 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 346488877 346521645).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18615 346488877 346521645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18615)) 346521645 346554413 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 346521645 346554413).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18615 346521645 346554413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 346423341 346488877).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 346423341 ≤ 346456109)
    (by decide : 346456109 ≤ 346488877) block0 block1

theorem join_0_1 : (twinPrimeSegment 346488877 346554413).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 346488877 ≤ 346521645)
    (by decide : 346521645 ≤ 346554413) block2 block3

theorem join_1_0 : (twinPrimeSegment 346423341 346554413).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 346423341 ≤ 346488877)
    (by decide : 346488877 ≤ 346554413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 346423341 346554413).card = 428 := join_1_0

end S165C03
end Sude.GeneratedTwinScan
