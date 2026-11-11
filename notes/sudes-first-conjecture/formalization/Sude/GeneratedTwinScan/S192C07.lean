import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S192C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20089)) 403570733 403603501 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 403570733 403603501).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20089 403570733 403603501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20090)) 403603501 403636269 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 403603501 403636269).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20090 403603501 403636269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20091)) 403636269 403669037 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 403636269 403669037).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20091 403636269 403669037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20092)) 403669037 403701805 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 403669037 403701805).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20092 403669037 403701805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 403570733 403636269).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 403570733 ≤ 403603501)
    (by decide : 403603501 ≤ 403636269) block0 block1

theorem join_0_1 : (twinPrimeSegment 403636269 403701805).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 403636269 ≤ 403669037)
    (by decide : 403669037 ≤ 403701805) block2 block3

theorem join_1_0 : (twinPrimeSegment 403570733 403701805).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 403570733 ≤ 403636269)
    (by decide : 403636269 ≤ 403701805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 403570733 403701805).card = 443 := join_1_0

end S192C07
end Sude.GeneratedTwinScan
