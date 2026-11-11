import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18343)) 336461869 336494637 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 336461869 336494637).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18343 336461869 336494637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18344)) 336494637 336527405 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 336494637 336527405).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18344 336494637 336527405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18345)) 336527405 336560173 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 336527405 336560173).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18345 336527405 336560173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18346)) 336560173 336592941 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 336560173 336592941).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18346 336560173 336592941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 336461869 336527405).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 336461869 ≤ 336494637)
    (by decide : 336494637 ≤ 336527405) block0 block1

theorem join_0_1 : (twinPrimeSegment 336527405 336592941).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 336527405 ≤ 336560173)
    (by decide : 336560173 ≤ 336592941) block2 block3

theorem join_1_0 : (twinPrimeSegment 336461869 336592941).card = 462 := by
  simpa using combineTwinPrimeSegments (by decide : 336461869 ≤ 336527405)
    (by decide : 336527405 ≤ 336592941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 336461869 336592941).card = 462 := join_1_0

end S160C07
end Sude.GeneratedTwinScan
