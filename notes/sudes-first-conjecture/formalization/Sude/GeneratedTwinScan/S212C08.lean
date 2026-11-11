import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21111)) 445644845 445677613 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 445644845 445677613).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21111 445644845 445677613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21111)) 445677613 445710381 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 445677613 445710381).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21111 445677613 445710381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21112)) 445710381 445743149 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 445710381 445743149).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21112 445710381 445743149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21113)) 445743149 445775917 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 445743149 445775917).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21113 445743149 445775917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 445644845 445710381).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 445644845 ≤ 445677613)
    (by decide : 445677613 ≤ 445710381) block0 block1

theorem join_0_1 : (twinPrimeSegment 445710381 445775917).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 445710381 ≤ 445743149)
    (by decide : 445743149 ≤ 445775917) block2 block3

theorem join_1_0 : (twinPrimeSegment 445644845 445775917).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 445644845 ≤ 445710381)
    (by decide : 445710381 ≤ 445775917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 445644845 445775917).card = 458 := join_1_0

end S212C08
end Sude.GeneratedTwinScan
