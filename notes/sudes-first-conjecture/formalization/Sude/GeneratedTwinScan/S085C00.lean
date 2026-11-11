import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S085C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13352)) 178257965 178290733 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 178257965 178290733).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13352 178257965 178290733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13353)) 178290733 178323501 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 178290733 178323501).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13353 178290733 178323501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13355)) 178323501 178356269 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 178323501 178356269).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13355 178323501 178356269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13356)) 178356269 178389037 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 178356269 178389037).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13356 178356269 178389037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 178257965 178323501).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 178257965 ≤ 178290733)
    (by decide : 178290733 ≤ 178323501) block0 block1

theorem join_0_1 : (twinPrimeSegment 178323501 178389037).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 178323501 ≤ 178356269)
    (by decide : 178356269 ≤ 178389037) block2 block3

theorem join_1_0 : (twinPrimeSegment 178257965 178389037).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 178257965 ≤ 178323501)
    (by decide : 178323501 ≤ 178389037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 178257965 178389037).card = 447 := join_1_0

end S085C00
end Sude.GeneratedTwinScan
