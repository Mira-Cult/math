import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14941)) 223215661 223248429 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 223215661 223248429).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14941 223215661 223248429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14942)) 223248429 223281197 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 223248429 223281197).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14942 223248429 223281197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14943)) 223281197 223313965 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 223281197 223313965).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14943 223281197 223313965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14944)) 223313965 223346733 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 223313965 223346733).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14944 223313965 223346733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 223215661 223281197).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 223215661 ≤ 223248429)
    (by decide : 223248429 ≤ 223281197) block0 block1

theorem join_0_1 : (twinPrimeSegment 223281197 223346733).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 223281197 ≤ 223313965)
    (by decide : 223313965 ≤ 223346733) block2 block3

theorem join_1_0 : (twinPrimeSegment 223215661 223346733).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 223215661 ≤ 223281197)
    (by decide : 223281197 ≤ 223346733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 223215661 223346733).card = 468 := join_1_0

end S106C07
end Sude.GeneratedTwinScan
