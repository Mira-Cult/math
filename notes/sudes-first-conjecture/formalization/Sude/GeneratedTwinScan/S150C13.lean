import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S150C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17785)) 316276781 316309549 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 316276781 316309549).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17785 316276781 316309549
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17786)) 316309549 316342317 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 316309549 316342317).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17786 316309549 316342317
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17786)) 316342317 316375085 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 316342317 316375085).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17786 316342317 316375085
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17787)) 316375085 316407853 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 316375085 316407853).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17787 316375085 316407853
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 316276781 316342317).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 316276781 ≤ 316309549)
    (by decide : 316309549 ≤ 316342317) block0 block1

theorem join_0_1 : (twinPrimeSegment 316342317 316407853).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 316342317 ≤ 316375085)
    (by decide : 316375085 ≤ 316407853) block2 block3

theorem join_1_0 : (twinPrimeSegment 316276781 316407853).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 316276781 ≤ 316342317)
    (by decide : 316342317 ≤ 316407853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 316276781 316407853).card = 474 := join_1_0

end S150C13
end Sude.GeneratedTwinScan
