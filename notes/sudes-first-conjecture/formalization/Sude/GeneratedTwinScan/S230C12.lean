import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21998)) 483917869 483950637 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 483917869 483950637).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21998 483917869 483950637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21999)) 483950637 483983405 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 483950637 483983405).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21999 483950637 483983405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22000)) 483983405 484016173 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 483983405 484016173).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22000 483983405 484016173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22001)) 484016173 484048941 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 484016173 484048941).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22001 484016173 484048941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 483917869 483983405).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 483917869 ≤ 483950637)
    (by decide : 483950637 ≤ 483983405) block0 block1

theorem join_0_1 : (twinPrimeSegment 483983405 484048941).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 483983405 ≤ 484016173)
    (by decide : 484016173 ≤ 484048941) block2 block3

theorem join_1_0 : (twinPrimeSegment 483917869 484048941).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 483917869 ≤ 483983405)
    (by decide : 483983405 ≤ 484048941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 483917869 484048941).card = 458 := join_1_0

end S230C12
end Sude.GeneratedTwinScan
