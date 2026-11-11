import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S149C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17700)) 313262125 313294893 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 313262125 313294893).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17700 313262125 313294893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17701)) 313294893 313327661 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 313294893 313327661).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17701 313294893 313327661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17701)) 313327661 313360429 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 313327661 313360429).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17701 313327661 313360429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17702)) 313360429 313393197 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 313360429 313393197).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17702 313360429 313393197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 313262125 313327661).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 313262125 ≤ 313294893)
    (by decide : 313294893 ≤ 313327661) block0 block1

theorem join_0_1 : (twinPrimeSegment 313327661 313393197).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 313327661 ≤ 313360429)
    (by decide : 313360429 ≤ 313393197) block2 block3

theorem join_1_0 : (twinPrimeSegment 313262125 313393197).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 313262125 ≤ 313327661)
    (by decide : 313327661 ≤ 313393197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 313262125 313393197).card = 445 := join_1_0

end S149C06
end Sude.GeneratedTwinScan
