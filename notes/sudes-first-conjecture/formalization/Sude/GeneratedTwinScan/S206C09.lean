import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20814)) 433193005 433225773 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 433193005 433225773).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20814 433193005 433225773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20814)) 433225773 433258541 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 433225773 433258541).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20814 433225773 433258541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20815)) 433258541 433291309 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 433258541 433291309).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20815 433258541 433291309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20816)) 433291309 433324077 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 433291309 433324077).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20816 433291309 433324077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 433193005 433258541).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 433193005 ≤ 433225773)
    (by decide : 433225773 ≤ 433258541) block0 block1

theorem join_0_1 : (twinPrimeSegment 433258541 433324077).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 433258541 ≤ 433291309)
    (by decide : 433291309 ≤ 433324077) block2 block3

theorem join_1_0 : (twinPrimeSegment 433193005 433324077).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 433193005 ≤ 433258541)
    (by decide : 433258541 ≤ 433324077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 433193005 433324077).card = 432 := join_1_0

end S206C09
end Sude.GeneratedTwinScan
