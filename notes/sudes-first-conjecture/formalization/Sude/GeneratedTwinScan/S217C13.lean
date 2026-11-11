import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21373)) 456785965 456818733 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 456785965 456818733).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21373 456785965 456818733
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21374)) 456818733 456851501 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 456818733 456851501).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21374 456818733 456851501
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21374)) 456851501 456884269 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 456851501 456884269).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21374 456851501 456884269
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21375)) 456884269 456917037 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 456884269 456917037).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21375 456884269 456917037
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 456785965 456851501).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 456785965 ≤ 456818733)
    (by decide : 456818733 ≤ 456851501) block0 block1

theorem join_0_1 : (twinPrimeSegment 456851501 456917037).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 456851501 ≤ 456884269)
    (by decide : 456884269 ≤ 456917037) block2 block3

theorem join_1_0 : (twinPrimeSegment 456785965 456917037).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 456785965 ≤ 456851501)
    (by decide : 456851501 ≤ 456917037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 456785965 456917037).card = 456 := join_1_0

end S217C13
end Sude.GeneratedTwinScan
