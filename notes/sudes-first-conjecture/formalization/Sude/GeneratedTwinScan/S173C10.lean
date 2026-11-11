import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19082)) 364118061 364150829 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 364118061 364150829).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19082 364118061 364150829
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19083)) 364150829 364183597 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 364150829 364183597).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19083 364150829 364183597
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19084)) 364183597 364216365 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 364183597 364216365).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19084 364183597 364216365
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19085)) 364216365 364249133 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 364216365 364249133).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19085 364216365 364249133
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 364118061 364183597).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 364118061 ≤ 364150829)
    (by decide : 364150829 ≤ 364183597) block0 block1

theorem join_0_1 : (twinPrimeSegment 364183597 364249133).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 364183597 ≤ 364216365)
    (by decide : 364216365 ≤ 364249133) block2 block3

theorem join_1_0 : (twinPrimeSegment 364118061 364249133).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 364118061 ≤ 364183597)
    (by decide : 364183597 ≤ 364249133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 364118061 364249133).card = 472 := join_1_0

end S173C10
end Sude.GeneratedTwinScan
