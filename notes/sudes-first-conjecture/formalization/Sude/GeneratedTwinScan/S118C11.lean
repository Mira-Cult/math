import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S118C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15777)) 248905773 248938541 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 248905773 248938541).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15777 248905773 248938541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15778)) 248938541 248971309 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 248938541 248971309).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15778 248938541 248971309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15779)) 248971309 249004077 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 248971309 249004077).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15779 248971309 249004077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15780)) 249004077 249036845 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 249004077 249036845).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15780 249004077 249036845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 248905773 248971309).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 248905773 ≤ 248938541)
    (by decide : 248938541 ≤ 248971309) block0 block1

theorem join_0_1 : (twinPrimeSegment 248971309 249036845).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 248971309 ≤ 249004077)
    (by decide : 249004077 ≤ 249036845) block2 block3

theorem join_1_0 : (twinPrimeSegment 248905773 249036845).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 248905773 ≤ 248971309)
    (by decide : 248971309 ≤ 249036845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 248905773 249036845).card = 454 := join_1_0

end S118C11
end Sude.GeneratedTwinScan
