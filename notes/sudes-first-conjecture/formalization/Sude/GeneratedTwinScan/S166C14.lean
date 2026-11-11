import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18708)) 349962285 349995053 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 349962285 349995053).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18708 349962285 349995053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18709)) 349995053 350027821 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 349995053 350027821).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18709 349995053 350027821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18709)) 350027821 350060589 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 350027821 350060589).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18709 350027821 350060589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18710)) 350060589 350093357 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 350060589 350093357).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18710 350060589 350093357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 349962285 350027821).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 349962285 ≤ 349995053)
    (by decide : 349995053 ≤ 350027821) block0 block1

theorem join_0_1 : (twinPrimeSegment 350027821 350093357).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 350027821 ≤ 350060589)
    (by decide : 350060589 ≤ 350093357) block2 block3

theorem join_1_0 : (twinPrimeSegment 349962285 350093357).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 349962285 ≤ 350027821)
    (by decide : 350027821 ≤ 350093357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 349962285 350093357).card = 438 := join_1_0

end S166C14
end Sude.GeneratedTwinScan
