import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S093C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14018)) 196476973 196509741 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 196476973 196509741).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14018 196476973 196509741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14019)) 196509741 196542509 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 196509741 196542509).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14019 196509741 196542509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14020)) 196542509 196575277 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 196542509 196575277).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14020 196542509 196575277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14021)) 196575277 196608045 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 196575277 196608045).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14021 196575277 196608045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 196476973 196542509).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 196476973 ≤ 196509741)
    (by decide : 196509741 ≤ 196542509) block0 block1

theorem join_0_1 : (twinPrimeSegment 196542509 196608045).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 196542509 ≤ 196575277)
    (by decide : 196575277 ≤ 196608045) block2 block3

theorem join_1_0 : (twinPrimeSegment 196476973 196608045).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 196476973 ≤ 196542509)
    (by decide : 196542509 ≤ 196608045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 196476973 196608045).card = 504 := join_1_0

end S093C11
end Sude.GeneratedTwinScan
