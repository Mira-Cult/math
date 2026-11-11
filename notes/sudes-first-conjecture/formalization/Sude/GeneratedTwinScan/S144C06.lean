import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S144C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17401)) 302776365 302809133 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 302776365 302809133).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17401 302776365 302809133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17402)) 302809133 302841901 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 302809133 302841901).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17402 302809133 302841901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17403)) 302841901 302874669 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 302841901 302874669).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17403 302841901 302874669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17404)) 302874669 302907437 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 302874669 302907437).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17404 302874669 302907437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 302776365 302841901).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 302776365 ≤ 302809133)
    (by decide : 302809133 ≤ 302841901) block0 block1

theorem join_0_1 : (twinPrimeSegment 302841901 302907437).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 302841901 ≤ 302874669)
    (by decide : 302874669 ≤ 302907437) block2 block3

theorem join_1_0 : (twinPrimeSegment 302776365 302907437).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 302776365 ≤ 302841901)
    (by decide : 302841901 ≤ 302907437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 302776365 302907437).card = 425 := join_1_0

end S144C06
end Sude.GeneratedTwinScan
