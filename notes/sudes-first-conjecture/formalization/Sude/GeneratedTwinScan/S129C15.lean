import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S129C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16508)) 272498733 272531501 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 272498733 272531501).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16508 272498733 272531501
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16509)) 272531501 272564269 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 272531501 272564269).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16509 272531501 272564269
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16510)) 272564269 272597037 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 272564269 272597037).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16510 272564269 272597037
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16511)) 272597037 272629805 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 272597037 272629805).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16511 272597037 272629805
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 272498733 272564269).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 272498733 ≤ 272531501)
    (by decide : 272531501 ≤ 272564269) block0 block1

theorem join_0_1 : (twinPrimeSegment 272564269 272629805).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 272564269 ≤ 272597037)
    (by decide : 272597037 ≤ 272629805) block2 block3

theorem join_1_0 : (twinPrimeSegment 272498733 272629805).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 272498733 ≤ 272564269)
    (by decide : 272564269 ≤ 272629805) join_0_0 join_0_1

theorem total : (twinPrimeSegment 272498733 272629805).card = 470 := join_1_0

end S129C15
end Sude.GeneratedTwinScan
