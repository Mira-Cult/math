import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15955)) 254541869 254574637 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 254541869 254574637).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15955 254541869 254574637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15956)) 254574637 254607405 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 254574637 254607405).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15956 254574637 254607405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15957)) 254607405 254640173 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 254607405 254640173).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15957 254607405 254640173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15958)) 254640173 254672941 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 254640173 254672941).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15958 254640173 254672941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 254541869 254607405).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 254541869 ≤ 254574637)
    (by decide : 254574637 ≤ 254607405) block0 block1

theorem join_0_1 : (twinPrimeSegment 254607405 254672941).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 254607405 ≤ 254640173)
    (by decide : 254640173 ≤ 254672941) block2 block3

theorem join_1_0 : (twinPrimeSegment 254541869 254672941).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 254541869 ≤ 254607405)
    (by decide : 254607405 ≤ 254672941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 254541869 254672941).card = 489 := join_1_0

end S121C06
end Sude.GeneratedTwinScan
