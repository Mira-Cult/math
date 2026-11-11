import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S198C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20426)) 417202221 417234989 = 93 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 417202221 417234989).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20426 417202221 417234989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20427)) 417234989 417267757 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 417234989 417267757).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20427 417234989 417267757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20427)) 417267757 417300525 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 417267757 417300525).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20427 417267757 417300525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20428)) 417300525 417333293 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 417300525 417333293).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20428 417300525 417333293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 417202221 417267757).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 417202221 ≤ 417234989)
    (by decide : 417234989 ≤ 417267757) block0 block1

theorem join_0_1 : (twinPrimeSegment 417267757 417333293).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 417267757 ≤ 417300525)
    (by decide : 417300525 ≤ 417333293) block2 block3

theorem join_1_0 : (twinPrimeSegment 417202221 417333293).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 417202221 ≤ 417267757)
    (by decide : 417267757 ≤ 417333293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 417202221 417333293).card = 444 := join_1_0

end S198C15
end Sude.GeneratedTwinScan
