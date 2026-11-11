import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S188C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19880)) 395182125 395214893 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 395182125 395214893).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19880 395182125 395214893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19880)) 395214893 395247661 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 395214893 395247661).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19880 395214893 395247661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19881)) 395247661 395280429 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 395247661 395280429).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19881 395247661 395280429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19882)) 395280429 395313197 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 395280429 395313197).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19882 395280429 395313197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 395182125 395247661).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 395182125 ≤ 395214893)
    (by decide : 395214893 ≤ 395247661) block0 block1

theorem join_0_1 : (twinPrimeSegment 395247661 395313197).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 395247661 ≤ 395280429)
    (by decide : 395280429 ≤ 395313197) block2 block3

theorem join_1_0 : (twinPrimeSegment 395182125 395313197).card = 436 := by
  simpa using combineTwinPrimeSegments (by decide : 395182125 ≤ 395247661)
    (by decide : 395247661 ≤ 395313197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 395182125 395313197).card = 436 := join_1_0

end S188C07
end Sude.GeneratedTwinScan
