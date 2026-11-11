import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22592)) 510394413 510427181 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 510394413 510427181).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22592 510394413 510427181
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22593)) 510427181 510459949 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 510427181 510459949).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22593 510427181 510459949
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22594)) 510459949 510492717 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 510459949 510492717).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22594 510459949 510492717
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22594)) 510492717 510525485 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 510492717 510525485).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22594 510492717 510525485
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 510394413 510459949).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 510394413 ≤ 510427181)
    (by decide : 510427181 ≤ 510459949) block0 block1

theorem join_0_1 : (twinPrimeSegment 510459949 510525485).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 510459949 ≤ 510492717)
    (by decide : 510492717 ≤ 510525485) block2 block3

theorem join_1_0 : (twinPrimeSegment 510394413 510525485).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 510394413 ≤ 510459949)
    (by decide : 510459949 ≤ 510525485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 510394413 510525485).card = 421 := join_1_0

end S243C06
end Sude.GeneratedTwinScan
