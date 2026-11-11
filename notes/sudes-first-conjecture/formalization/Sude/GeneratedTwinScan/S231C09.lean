import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22037)) 485621805 485654573 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 485621805 485654573).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22037 485621805 485654573
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22038)) 485654573 485687341 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 485654573 485687341).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22038 485654573 485687341
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22039)) 485687341 485720109 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 485687341 485720109).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22039 485687341 485720109
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22039)) 485720109 485752877 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 485720109 485752877).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22039 485720109 485752877
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 485621805 485687341).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 485621805 ≤ 485654573)
    (by decide : 485654573 ≤ 485687341) block0 block1

theorem join_0_1 : (twinPrimeSegment 485687341 485752877).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 485687341 ≤ 485720109)
    (by decide : 485720109 ≤ 485752877) block2 block3

theorem join_1_0 : (twinPrimeSegment 485621805 485752877).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 485621805 ≤ 485687341)
    (by decide : 485687341 ≤ 485752877) join_0_0 join_0_1

theorem total : (twinPrimeSegment 485621805 485752877).card = 427 := join_1_0

end S231C09
end Sude.GeneratedTwinScan
