import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14527)) 211025965 211058733 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 211025965 211058733).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14527 211025965 211058733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14528)) 211058733 211091501 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 211058733 211091501).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14528 211058733 211091501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14530)) 211091501 211124269 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 211091501 211124269).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14530 211091501 211124269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14531)) 211124269 211157037 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 211124269 211157037).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14531 211124269 211157037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 211025965 211091501).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 211025965 ≤ 211058733)
    (by decide : 211058733 ≤ 211091501) block0 block1

theorem join_0_1 : (twinPrimeSegment 211091501 211157037).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 211091501 ≤ 211124269)
    (by decide : 211124269 ≤ 211157037) block2 block3

theorem join_1_0 : (twinPrimeSegment 211025965 211157037).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 211025965 ≤ 211091501)
    (by decide : 211091501 ≤ 211157037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 211025965 211157037).card = 433 := join_1_0

end S100C10
end Sude.GeneratedTwinScan
