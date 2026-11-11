import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15167)) 230031405 230064173 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 230031405 230064173).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15167 230031405 230064173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15168)) 230064173 230096941 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 230064173 230096941).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15168 230064173 230096941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15170)) 230096941 230129709 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 230096941 230129709).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15170 230096941 230129709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15171)) 230129709 230162477 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 230129709 230162477).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15171 230129709 230162477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 230031405 230096941).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 230031405 ≤ 230064173)
    (by decide : 230064173 ≤ 230096941) block0 block1

theorem join_0_1 : (twinPrimeSegment 230096941 230162477).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 230096941 ≤ 230129709)
    (by decide : 230129709 ≤ 230162477) block2 block3

theorem join_1_0 : (twinPrimeSegment 230031405 230162477).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 230031405 ≤ 230096941)
    (by decide : 230096941 ≤ 230162477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 230031405 230162477).card = 461 := join_1_0

end S109C11
end Sude.GeneratedTwinScan
