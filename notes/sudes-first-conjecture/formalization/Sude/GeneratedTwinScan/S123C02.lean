import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16069)) 258211885 258244653 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 258211885 258244653).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16069 258211885 258244653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16071)) 258244653 258277421 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 258244653 258277421).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16071 258244653 258277421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16072)) 258277421 258310189 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 258277421 258310189).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16072 258277421 258310189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16073)) 258310189 258342957 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 258310189 258342957).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16073 258310189 258342957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 258211885 258277421).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 258211885 ≤ 258244653)
    (by decide : 258244653 ≤ 258277421) block0 block1

theorem join_0_1 : (twinPrimeSegment 258277421 258342957).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 258277421 ≤ 258310189)
    (by decide : 258310189 ≤ 258342957) block2 block3

theorem join_1_0 : (twinPrimeSegment 258211885 258342957).card = 474 := by
  simpa using combineTwinPrimeSegments (by decide : 258211885 ≤ 258277421)
    (by decide : 258277421 ≤ 258342957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 258211885 258342957).card = 474 := join_1_0

end S123C02
end Sude.GeneratedTwinScan
