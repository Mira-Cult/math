import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S175C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19188)) 368181293 368214061 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 368181293 368214061).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19188 368181293 368214061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19189)) 368214061 368246829 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 368214061 368246829).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19189 368214061 368246829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19190)) 368246829 368279597 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 368246829 368279597).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19190 368246829 368279597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19191)) 368279597 368312365 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 368279597 368312365).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19191 368279597 368312365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 368181293 368246829).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 368181293 ≤ 368214061)
    (by decide : 368214061 ≤ 368246829) block0 block1

theorem join_0_1 : (twinPrimeSegment 368246829 368312365).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 368246829 ≤ 368279597)
    (by decide : 368279597 ≤ 368312365) block2 block3

theorem join_1_0 : (twinPrimeSegment 368181293 368312365).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 368181293 ≤ 368246829)
    (by decide : 368246829 ≤ 368312365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 368181293 368312365).card = 428 := join_1_0

end S175C09
end Sude.GeneratedTwinScan
