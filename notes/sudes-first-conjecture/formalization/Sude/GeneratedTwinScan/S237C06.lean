import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22312)) 497811501 497844269 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 497811501 497844269).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22312 497811501 497844269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22313)) 497844269 497877037 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 497844269 497877037).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22313 497844269 497877037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22313)) 497877037 497909805 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 497877037 497909805).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22313 497877037 497909805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22314)) 497909805 497942573 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 497909805 497942573).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22314 497909805 497942573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 497811501 497877037).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 497811501 ≤ 497844269)
    (by decide : 497844269 ≤ 497877037) block0 block1

theorem join_0_1 : (twinPrimeSegment 497877037 497942573).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 497877037 ≤ 497909805)
    (by decide : 497909805 ≤ 497942573) block2 block3

theorem join_1_0 : (twinPrimeSegment 497811501 497942573).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 497811501 ≤ 497877037)
    (by decide : 497877037 ≤ 497942573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 497811501 497942573).card = 452 := join_1_0

end S237C06
end Sude.GeneratedTwinScan
