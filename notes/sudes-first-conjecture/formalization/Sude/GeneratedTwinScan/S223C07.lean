import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S223C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21647)) 468582445 468615213 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 468582445 468615213).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21647 468582445 468615213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21648)) 468615213 468647981 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 468615213 468647981).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21648 468615213 468647981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21649)) 468647981 468680749 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 468647981 468680749).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21649 468647981 468680749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21649)) 468680749 468713517 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 468680749 468713517).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21649 468680749 468713517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 468582445 468647981).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 468582445 ≤ 468615213)
    (by decide : 468615213 ≤ 468647981) block0 block1

theorem join_0_1 : (twinPrimeSegment 468647981 468713517).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 468647981 ≤ 468680749)
    (by decide : 468680749 ≤ 468713517) block2 block3

theorem join_1_0 : (twinPrimeSegment 468582445 468713517).card = 425 := by
  simpa using combineTwinPrimeSegments (by decide : 468582445 ≤ 468647981)
    (by decide : 468647981 ≤ 468713517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 468582445 468713517).card = 425 := join_1_0

end S223C07
end Sude.GeneratedTwinScan
