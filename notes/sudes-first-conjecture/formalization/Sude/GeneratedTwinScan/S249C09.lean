import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22878)) 523370541 523403309 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 523370541 523403309).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22878 523370541 523403309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22878)) 523403309 523436077 = 89 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 523403309 523436077).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22878 523403309 523436077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22879)) 523436077 523468845 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 523436077 523468845).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22879 523436077 523468845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22880)) 523468845 523501613 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 523468845 523501613).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22880 523468845 523501613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 523370541 523436077).card = 189 := by
  simpa using combineTwinPrimeSegments (by decide : 523370541 ≤ 523403309)
    (by decide : 523403309 ≤ 523436077) block0 block1

theorem join_0_1 : (twinPrimeSegment 523436077 523501613).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 523436077 ≤ 523468845)
    (by decide : 523468845 ≤ 523501613) block2 block3

theorem join_1_0 : (twinPrimeSegment 523370541 523501613).card = 394 := by
  simpa using combineTwinPrimeSegments (by decide : 523370541 ≤ 523436077)
    (by decide : 523436077 ≤ 523501613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 523370541 523501613).card = 394 := join_1_0

end S249C09
end Sude.GeneratedTwinScan
