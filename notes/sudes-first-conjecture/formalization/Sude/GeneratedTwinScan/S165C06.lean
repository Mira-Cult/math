import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18623)) 346816557 346849325 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 346816557 346849325).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18623 346816557 346849325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18624)) 346849325 346882093 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 346849325 346882093).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18624 346849325 346882093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18625)) 346882093 346914861 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 346882093 346914861).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18625 346882093 346914861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18626)) 346914861 346947629 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 346914861 346947629).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18626 346914861 346947629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 346816557 346882093).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 346816557 ≤ 346849325)
    (by decide : 346849325 ≤ 346882093) block0 block1

theorem join_0_1 : (twinPrimeSegment 346882093 346947629).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 346882093 ≤ 346914861)
    (by decide : 346914861 ≤ 346947629) block2 block3

theorem join_1_0 : (twinPrimeSegment 346816557 346947629).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 346816557 ≤ 346882093)
    (by decide : 346882093 ≤ 346947629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 346816557 346947629).card = 448 := join_1_0

end S165C06
end Sude.GeneratedTwinScan
