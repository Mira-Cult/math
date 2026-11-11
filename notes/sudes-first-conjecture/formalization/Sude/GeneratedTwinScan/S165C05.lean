import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18620)) 346685485 346718253 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 346685485 346718253).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18620 346685485 346718253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18621)) 346718253 346751021 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 346718253 346751021).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18621 346718253 346751021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18622)) 346751021 346783789 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 346751021 346783789).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18622 346751021 346783789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18623)) 346783789 346816557 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 346783789 346816557).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18623 346783789 346816557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 346685485 346751021).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 346685485 ≤ 346718253)
    (by decide : 346718253 ≤ 346751021) block0 block1

theorem join_0_1 : (twinPrimeSegment 346751021 346816557).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 346751021 ≤ 346783789)
    (by decide : 346783789 ≤ 346816557) block2 block3

theorem join_1_0 : (twinPrimeSegment 346685485 346816557).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 346685485 ≤ 346751021)
    (by decide : 346751021 ≤ 346816557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 346685485 346816557).card = 450 := join_1_0

end S165C05
end Sude.GeneratedTwinScan
