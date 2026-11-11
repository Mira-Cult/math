import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S100C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14487)) 209846317 209879085 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 209846317 209879085).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14487 209846317 209879085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14488)) 209879085 209911853 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 209879085 209911853).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14488 209879085 209911853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14489)) 209911853 209944621 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 209911853 209944621).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14489 209911853 209944621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14490)) 209944621 209977389 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 209944621 209977389).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14490 209944621 209977389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 209846317 209911853).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 209846317 ≤ 209879085)
    (by decide : 209879085 ≤ 209911853) block0 block1

theorem join_0_1 : (twinPrimeSegment 209911853 209977389).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 209911853 ≤ 209944621)
    (by decide : 209944621 ≤ 209977389) block2 block3

theorem join_1_0 : (twinPrimeSegment 209846317 209977389).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 209846317 ≤ 209911853)
    (by decide : 209911853 ≤ 209977389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 209846317 209977389).card = 458 := join_1_0

end S100C01
end Sude.GeneratedTwinScan
