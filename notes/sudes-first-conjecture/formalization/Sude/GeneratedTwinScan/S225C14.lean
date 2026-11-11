import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21765)) 473694253 473727021 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 473694253 473727021).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21765 473694253 473727021
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21766)) 473727021 473759789 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 473727021 473759789).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21766 473727021 473759789
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21766)) 473759789 473792557 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 473759789 473792557).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21766 473759789 473792557
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21767)) 473792557 473825325 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 473792557 473825325).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21767 473792557 473825325
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 473694253 473759789).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 473694253 ≤ 473727021)
    (by decide : 473727021 ≤ 473759789) block0 block1

theorem join_0_1 : (twinPrimeSegment 473759789 473825325).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 473759789 ≤ 473792557)
    (by decide : 473792557 ≤ 473825325) block2 block3

theorem join_1_0 : (twinPrimeSegment 473694253 473825325).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 473694253 ≤ 473759789)
    (by decide : 473759789 ≤ 473825325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 473694253 473825325).card = 440 := join_1_0

end S225C14
end Sude.GeneratedTwinScan
