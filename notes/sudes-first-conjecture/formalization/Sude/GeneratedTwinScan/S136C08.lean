import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S136C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16920)) 286261293 286294061 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 286261293 286294061).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16920 286261293 286294061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16921)) 286294061 286326829 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 286294061 286326829).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16921 286294061 286326829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16922)) 286326829 286359597 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 286326829 286359597).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16922 286326829 286359597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16923)) 286359597 286392365 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 286359597 286392365).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16923 286359597 286392365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 286261293 286326829).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 286261293 ≤ 286294061)
    (by decide : 286294061 ≤ 286326829) block0 block1

theorem join_0_1 : (twinPrimeSegment 286326829 286392365).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 286326829 ≤ 286359597)
    (by decide : 286359597 ≤ 286392365) block2 block3

theorem join_1_0 : (twinPrimeSegment 286261293 286392365).card = 486 := by
  simpa using combineTwinPrimeSegments (by decide : 286261293 ≤ 286326829)
    (by decide : 286326829 ≤ 286392365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 286261293 286392365).card = 486 := join_1_0

end S136C08
end Sude.GeneratedTwinScan
