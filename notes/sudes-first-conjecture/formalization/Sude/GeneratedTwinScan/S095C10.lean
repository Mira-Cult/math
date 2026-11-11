import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S095C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14162)) 200540205 200572973 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 200540205 200572973).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14162 200540205 200572973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14163)) 200572973 200605741 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 200572973 200605741).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14163 200572973 200605741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14164)) 200605741 200638509 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 200605741 200638509).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14164 200605741 200638509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14165)) 200638509 200671277 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 200638509 200671277).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14165 200638509 200671277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 200540205 200605741).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 200540205 ≤ 200572973)
    (by decide : 200572973 ≤ 200605741) block0 block1

theorem join_0_1 : (twinPrimeSegment 200605741 200671277).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 200605741 ≤ 200638509)
    (by decide : 200638509 ≤ 200671277) block2 block3

theorem join_1_0 : (twinPrimeSegment 200540205 200671277).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 200540205 ≤ 200605741)
    (by decide : 200605741 ≤ 200671277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 200540205 200671277).card = 490 := join_1_0

end S095C10
end Sude.GeneratedTwinScan
