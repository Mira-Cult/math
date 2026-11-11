import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16456)) 270794797 270827565 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 270794797 270827565).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16456 270794797 270827565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16457)) 270827565 270860333 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 270827565 270860333).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16457 270827565 270860333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16458)) 270860333 270893101 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 270860333 270893101).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16458 270860333 270893101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16459)) 270893101 270925869 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 270893101 270925869).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16459 270893101 270925869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 270794797 270860333).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 270794797 ≤ 270827565)
    (by decide : 270827565 ≤ 270860333) block0 block1

theorem join_0_1 : (twinPrimeSegment 270860333 270925869).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 270860333 ≤ 270893101)
    (by decide : 270893101 ≤ 270925869) block2 block3

theorem join_1_0 : (twinPrimeSegment 270794797 270925869).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 270794797 ≤ 270860333)
    (by decide : 270860333 ≤ 270925869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 270794797 270925869).card = 465 := join_1_0

end S129C02
end Sude.GeneratedTwinScan
