import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15984)) 255459373 255492141 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 255459373 255492141).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15984 255459373 255492141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15985)) 255492141 255524909 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 255492141 255524909).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15985 255492141 255524909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15986)) 255524909 255557677 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 255524909 255557677).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15986 255524909 255557677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15987)) 255557677 255590445 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 255557677 255590445).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15987 255557677 255590445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 255459373 255524909).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 255459373 ≤ 255492141)
    (by decide : 255492141 ≤ 255524909) block0 block1

theorem join_0_1 : (twinPrimeSegment 255524909 255590445).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 255524909 ≤ 255557677)
    (by decide : 255557677 ≤ 255590445) block2 block3

theorem join_1_0 : (twinPrimeSegment 255459373 255590445).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 255459373 ≤ 255524909)
    (by decide : 255524909 ≤ 255590445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 255459373 255590445).card = 443 := join_1_0

end S121C13
end Sude.GeneratedTwinScan
