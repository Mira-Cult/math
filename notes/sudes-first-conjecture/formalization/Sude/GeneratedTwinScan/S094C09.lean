import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14083)) 198311981 198344749 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 198311981 198344749).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14083 198311981 198344749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14084)) 198344749 198377517 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 198344749 198377517).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14084 198344749 198377517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14085)) 198377517 198410285 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 198377517 198410285).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14085 198377517 198410285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14086)) 198410285 198443053 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 198410285 198443053).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14086 198410285 198443053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 198311981 198377517).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 198311981 ≤ 198344749)
    (by decide : 198344749 ≤ 198377517) block0 block1

theorem join_0_1 : (twinPrimeSegment 198377517 198443053).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 198377517 ≤ 198410285)
    (by decide : 198410285 ≤ 198443053) block2 block3

theorem join_1_0 : (twinPrimeSegment 198311981 198443053).card = 507 := by
  simpa using combineTwinPrimeSegments (by decide : 198311981 ≤ 198377517)
    (by decide : 198377517 ≤ 198443053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 198311981 198443053).card = 507 := join_1_0

end S094C09
end Sude.GeneratedTwinScan
