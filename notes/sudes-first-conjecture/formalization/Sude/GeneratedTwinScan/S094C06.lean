import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14069)) 197918765 197951533 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 197918765 197951533).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14069 197918765 197951533
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14070)) 197951533 197984301 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 197951533 197984301).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14070 197951533 197984301
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14071)) 197984301 198017069 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 197984301 198017069).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14071 197984301 198017069
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14073)) 198017069 198049837 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 198017069 198049837).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14073 198017069 198049837
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 197918765 197984301).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 197918765 ≤ 197951533)
    (by decide : 197951533 ≤ 197984301) block0 block1

theorem join_0_1 : (twinPrimeSegment 197984301 198049837).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 197984301 ≤ 198017069)
    (by decide : 198017069 ≤ 198049837) block2 block3

theorem join_1_0 : (twinPrimeSegment 197918765 198049837).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 197918765 ≤ 197984301)
    (by decide : 197984301 ≤ 198049837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 197918765 198049837).card = 467 := join_1_0

end S094C06
end Sude.GeneratedTwinScan
