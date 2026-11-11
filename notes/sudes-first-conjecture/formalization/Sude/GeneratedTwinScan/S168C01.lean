import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18774)) 352452653 352485421 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 352452653 352485421).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18774 352452653 352485421
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18775)) 352485421 352518189 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 352485421 352518189).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18775 352485421 352518189
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18776)) 352518189 352550957 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 352518189 352550957).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18776 352518189 352550957
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18777)) 352550957 352583725 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 352550957 352583725).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18777 352550957 352583725
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 352452653 352518189).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 352452653 ≤ 352485421)
    (by decide : 352485421 ≤ 352518189) block0 block1

theorem join_0_1 : (twinPrimeSegment 352518189 352583725).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 352518189 ≤ 352550957)
    (by decide : 352550957 ≤ 352583725) block2 block3

theorem join_1_0 : (twinPrimeSegment 352452653 352583725).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 352452653 ≤ 352518189)
    (by decide : 352518189 ≤ 352583725) join_0_0 join_0_1

theorem total : (twinPrimeSegment 352452653 352583725).card = 430 := join_1_0

end S168C01
end Sude.GeneratedTwinScan
