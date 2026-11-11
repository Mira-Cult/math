import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13019)) 169476141 169508909 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 169476141 169508909).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13019 169476141 169508909
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13020)) 169508909 169541677 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 169508909 169541677).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13020 169508909 169541677
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13022)) 169541677 169574445 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 169541677 169574445).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13022 169541677 169574445
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13023)) 169574445 169607213 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 169574445 169607213).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13023 169574445 169607213
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 169476141 169541677).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 169476141 ≤ 169508909)
    (by decide : 169508909 ≤ 169541677) block0 block1

theorem join_0_1 : (twinPrimeSegment 169541677 169607213).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 169541677 ≤ 169574445)
    (by decide : 169574445 ≤ 169607213) block2 block3

theorem join_1_0 : (twinPrimeSegment 169476141 169607213).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 169476141 ≤ 169541677)
    (by decide : 169541677 ≤ 169607213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 169476141 169607213).card = 471 := join_1_0

end S080C13
end Sude.GeneratedTwinScan
