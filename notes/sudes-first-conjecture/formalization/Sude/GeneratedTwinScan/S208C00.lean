import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S208C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20886)) 436207661 436240429 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 436207661 436240429).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20886 436207661 436240429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20887)) 436240429 436273197 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 436240429 436273197).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20887 436240429 436273197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20887)) 436273197 436305965 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 436273197 436305965).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20887 436273197 436305965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20888)) 436305965 436338733 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 436305965 436338733).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20888 436305965 436338733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 436207661 436273197).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 436207661 ≤ 436240429)
    (by decide : 436240429 ≤ 436273197) block0 block1

theorem join_0_1 : (twinPrimeSegment 436273197 436338733).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 436273197 ≤ 436305965)
    (by decide : 436305965 ≤ 436338733) block2 block3

theorem join_1_0 : (twinPrimeSegment 436207661 436338733).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 436207661 ≤ 436273197)
    (by decide : 436273197 ≤ 436338733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 436207661 436338733).card = 447 := join_1_0

end S208C00
end Sude.GeneratedTwinScan
