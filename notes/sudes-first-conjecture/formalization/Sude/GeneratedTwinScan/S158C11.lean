import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18243)) 332791853 332824621 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 332791853 332824621).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18243 332791853 332824621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18244)) 332824621 332857389 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 332824621 332857389).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18244 332824621 332857389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18245)) 332857389 332890157 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 332857389 332890157).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18245 332857389 332890157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18246)) 332890157 332922925 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 332890157 332922925).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18246 332890157 332922925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 332791853 332857389).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 332791853 ≤ 332824621)
    (by decide : 332824621 ≤ 332857389) block0 block1

theorem join_0_1 : (twinPrimeSegment 332857389 332922925).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 332857389 ≤ 332890157)
    (by decide : 332890157 ≤ 332922925) block2 block3

theorem join_1_0 : (twinPrimeSegment 332791853 332922925).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 332791853 ≤ 332857389)
    (by decide : 332857389 ≤ 332922925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 332791853 332922925).card = 487 := join_1_0

end S158C11
end Sude.GeneratedTwinScan
