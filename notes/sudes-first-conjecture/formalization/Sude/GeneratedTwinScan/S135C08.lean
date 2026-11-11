import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S135C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16858)) 284164141 284196909 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 284164141 284196909).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16858 284164141 284196909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16859)) 284196909 284229677 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 284196909 284229677).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16859 284196909 284229677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16860)) 284229677 284262445 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 284229677 284262445).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16860 284229677 284262445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16861)) 284262445 284295213 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 284262445 284295213).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16861 284262445 284295213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 284164141 284229677).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 284164141 ≤ 284196909)
    (by decide : 284196909 ≤ 284229677) block0 block1

theorem join_0_1 : (twinPrimeSegment 284229677 284295213).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 284229677 ≤ 284262445)
    (by decide : 284262445 ≤ 284295213) block2 block3

theorem join_1_0 : (twinPrimeSegment 284164141 284295213).card = 434 := by
  simpa using combineTwinPrimeSegments (by decide : 284164141 ≤ 284229677)
    (by decide : 284229677 ≤ 284295213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 284164141 284295213).card = 434 := join_1_0

end S135C08
end Sude.GeneratedTwinScan
