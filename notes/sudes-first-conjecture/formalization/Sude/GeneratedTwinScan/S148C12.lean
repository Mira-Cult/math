import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S148C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17663)) 311951405 311984173 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 311951405 311984173).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17663 311951405 311984173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17664)) 311984173 312016941 = 92 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 311984173 312016941).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17664 311984173 312016941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17664)) 312016941 312049709 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 312016941 312049709).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17664 312016941 312049709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17665)) 312049709 312082477 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 312049709 312082477).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17665 312049709 312082477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 311951405 312016941).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 311951405 ≤ 311984173)
    (by decide : 311984173 ≤ 312016941) block0 block1

theorem join_0_1 : (twinPrimeSegment 312016941 312082477).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 312016941 ≤ 312049709)
    (by decide : 312049709 ≤ 312082477) block2 block3

theorem join_1_0 : (twinPrimeSegment 311951405 312082477).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 311951405 ≤ 312016941)
    (by decide : 312016941 ≤ 312082477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 311951405 312082477).card = 457 := join_1_0

end S148C12
end Sude.GeneratedTwinScan
