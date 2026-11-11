import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13985)) 195559469 195592237 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 195559469 195592237).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13985 195559469 195592237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13986)) 195592237 195625005 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 195592237 195625005).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13986 195592237 195625005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13987)) 195625005 195657773 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 195625005 195657773).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13987 195625005 195657773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13988)) 195657773 195690541 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 195657773 195690541).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13988 195657773 195690541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 195559469 195625005).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 195559469 ≤ 195592237)
    (by decide : 195592237 ≤ 195625005) block0 block1

theorem join_0_1 : (twinPrimeSegment 195625005 195690541).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 195625005 ≤ 195657773)
    (by decide : 195657773 ≤ 195690541) block2 block3

theorem join_1_0 : (twinPrimeSegment 195559469 195690541).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 195559469 ≤ 195625005)
    (by decide : 195625005 ≤ 195690541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 195559469 195690541).card = 470 := join_1_0

end S093C04
end Sude.GeneratedTwinScan
