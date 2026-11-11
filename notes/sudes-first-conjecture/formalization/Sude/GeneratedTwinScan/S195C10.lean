import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S195C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20255)) 410255405 410288173 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 410255405 410288173).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20255 410255405 410288173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20256)) 410288173 410320941 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 410288173 410320941).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20256 410288173 410320941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20257)) 410320941 410353709 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 410320941 410353709).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20257 410320941 410353709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20257)) 410353709 410386477 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 410353709 410386477).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20257 410353709 410386477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 410255405 410320941).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 410255405 ≤ 410288173)
    (by decide : 410288173 ≤ 410320941) block0 block1

theorem join_0_1 : (twinPrimeSegment 410320941 410386477).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 410320941 ≤ 410353709)
    (by decide : 410353709 ≤ 410386477) block2 block3

theorem join_1_0 : (twinPrimeSegment 410255405 410386477).card = 407 := by
  simpa using combineTwinPrimeSegments (by decide : 410255405 ≤ 410320941)
    (by decide : 410320941 ≤ 410386477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 410255405 410386477).card = 407 := join_1_0

end S195C10
end Sude.GeneratedTwinScan
