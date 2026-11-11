import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21089)) 444727341 444760109 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 444727341 444760109).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21089 444727341 444760109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21090)) 444760109 444792877 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 444760109 444792877).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21090 444760109 444792877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21090)) 444792877 444825645 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 444792877 444825645).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21090 444792877 444825645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21091)) 444825645 444858413 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 444825645 444858413).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21091 444825645 444858413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 444727341 444792877).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 444727341 ≤ 444760109)
    (by decide : 444760109 ≤ 444792877) block0 block1

theorem join_0_1 : (twinPrimeSegment 444792877 444858413).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 444792877 ≤ 444825645)
    (by decide : 444825645 ≤ 444858413) block2 block3

theorem join_1_0 : (twinPrimeSegment 444727341 444858413).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 444727341 ≤ 444792877)
    (by decide : 444792877 ≤ 444858413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 444727341 444858413).card = 454 := join_1_0

end S212C01
end Sude.GeneratedTwinScan
