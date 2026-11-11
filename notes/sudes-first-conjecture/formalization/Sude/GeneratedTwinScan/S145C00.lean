import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17439)) 304087085 304119853 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 304087085 304119853).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17439 304087085 304119853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17439)) 304119853 304152621 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 304119853 304152621).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17439 304119853 304152621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17440)) 304152621 304185389 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 304152621 304185389).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17440 304152621 304185389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17441)) 304185389 304218157 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 304185389 304218157).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17441 304185389 304218157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 304087085 304152621).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 304087085 ≤ 304119853)
    (by decide : 304119853 ≤ 304152621) block0 block1

theorem join_0_1 : (twinPrimeSegment 304152621 304218157).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 304152621 ≤ 304185389)
    (by decide : 304185389 ≤ 304218157) block2 block3

theorem join_1_0 : (twinPrimeSegment 304087085 304218157).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 304087085 ≤ 304152621)
    (by decide : 304152621 ≤ 304218157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 304087085 304218157).card = 457 := join_1_0

end S145C00
end Sude.GeneratedTwinScan
