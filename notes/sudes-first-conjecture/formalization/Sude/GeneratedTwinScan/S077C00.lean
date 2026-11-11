import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12708)) 161480749 161513517 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 161480749 161513517).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12708 161480749 161513517
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12710)) 161513517 161546285 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 161513517 161546285).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12710 161513517 161546285
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12711)) 161546285 161579053 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 161546285 161579053).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12711 161546285 161579053
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12712)) 161579053 161611821 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 161579053 161611821).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12712 161579053 161611821
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 161480749 161546285).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 161480749 ≤ 161513517)
    (by decide : 161513517 ≤ 161546285) block0 block1

theorem join_0_1 : (twinPrimeSegment 161546285 161611821).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 161546285 ≤ 161579053)
    (by decide : 161579053 ≤ 161611821) block2 block3

theorem join_1_0 : (twinPrimeSegment 161480749 161611821).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 161480749 ≤ 161546285)
    (by decide : 161546285 ≤ 161611821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 161480749 161611821).card = 481 := join_1_0

end S077C00
end Sude.GeneratedTwinScan
