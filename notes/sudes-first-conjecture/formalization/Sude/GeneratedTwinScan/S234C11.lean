import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S234C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22185)) 492175405 492208173 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 492175405 492208173).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22185 492175405 492208173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22186)) 492208173 492240941 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 492208173 492240941).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22186 492208173 492240941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22187)) 492240941 492273709 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 492240941 492273709).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22187 492240941 492273709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22187)) 492273709 492306477 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 492273709 492306477).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22187 492273709 492306477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 492175405 492240941).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 492175405 ≤ 492208173)
    (by decide : 492208173 ≤ 492240941) block0 block1

theorem join_0_1 : (twinPrimeSegment 492240941 492306477).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 492240941 ≤ 492273709)
    (by decide : 492273709 ≤ 492306477) block2 block3

theorem join_1_0 : (twinPrimeSegment 492175405 492306477).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 492175405 ≤ 492240941)
    (by decide : 492240941 ≤ 492306477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 492175405 492306477).card = 452 := join_1_0

end S234C11
end Sude.GeneratedTwinScan
