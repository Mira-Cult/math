import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22452)) 504102957 504135725 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 504102957 504135725).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22452 504102957 504135725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22453)) 504135725 504168493 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 504135725 504168493).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22453 504135725 504168493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22454)) 504168493 504201261 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 504168493 504201261).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22454 504168493 504201261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22455)) 504201261 504234029 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 504201261 504234029).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22455 504201261 504234029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 504102957 504168493).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 504102957 ≤ 504135725)
    (by decide : 504135725 ≤ 504168493) block0 block1

theorem join_0_1 : (twinPrimeSegment 504168493 504234029).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 504168493 ≤ 504201261)
    (by decide : 504201261 ≤ 504234029) block2 block3

theorem join_1_0 : (twinPrimeSegment 504102957 504234029).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 504102957 ≤ 504168493)
    (by decide : 504168493 ≤ 504234029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 504102957 504234029).card = 458 := join_1_0

end S240C06
end Sude.GeneratedTwinScan
