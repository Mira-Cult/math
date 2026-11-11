import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S119C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15839)) 250871853 250904621 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 250871853 250904621).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15839 250871853 250904621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15841)) 250904621 250937389 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 250904621 250937389).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15841 250904621 250937389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15842)) 250937389 250970157 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 250937389 250970157).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15842 250937389 250970157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15843)) 250970157 251002925 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 250970157 251002925).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15843 250970157 251002925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 250871853 250937389).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 250871853 ≤ 250904621)
    (by decide : 250904621 ≤ 250937389) block0 block1

theorem join_0_1 : (twinPrimeSegment 250937389 251002925).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 250937389 ≤ 250970157)
    (by decide : 250970157 ≤ 251002925) block2 block3

theorem join_1_0 : (twinPrimeSegment 250871853 251002925).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 250871853 ≤ 250937389)
    (by decide : 250937389 ≤ 251002925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 250871853 251002925).card = 465 := join_1_0

end S119C10
end Sude.GeneratedTwinScan
