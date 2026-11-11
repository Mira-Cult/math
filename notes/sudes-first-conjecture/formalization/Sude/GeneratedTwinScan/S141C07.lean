import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17223)) 296615981 296648749 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 296615981 296648749).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17223 296615981 296648749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17224)) 296648749 296681517 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 296648749 296681517).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17224 296648749 296681517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17225)) 296681517 296714285 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 296681517 296714285).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17225 296681517 296714285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17226)) 296714285 296747053 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 296714285 296747053).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17226 296714285 296747053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 296615981 296681517).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 296615981 ≤ 296648749)
    (by decide : 296648749 ≤ 296681517) block0 block1

theorem join_0_1 : (twinPrimeSegment 296681517 296747053).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 296681517 ≤ 296714285)
    (by decide : 296714285 ≤ 296747053) block2 block3

theorem join_1_0 : (twinPrimeSegment 296615981 296747053).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 296615981 ≤ 296681517)
    (by decide : 296681517 ≤ 296747053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 296615981 296747053).card = 419 := join_1_0

end S141C07
end Sude.GeneratedTwinScan
