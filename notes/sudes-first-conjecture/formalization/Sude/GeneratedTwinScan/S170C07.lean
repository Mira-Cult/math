import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18906)) 357433389 357466157 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 357433389 357466157).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18906 357433389 357466157
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18907)) 357466157 357498925 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 357466157 357498925).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18907 357466157 357498925
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18908)) 357498925 357531693 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 357498925 357531693).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18908 357498925 357531693
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18909)) 357531693 357564461 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 357531693 357564461).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18909 357531693 357564461
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 357433389 357498925).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 357433389 ≤ 357466157)
    (by decide : 357466157 ≤ 357498925) block0 block1

theorem join_0_1 : (twinPrimeSegment 357498925 357564461).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 357498925 ≤ 357531693)
    (by decide : 357531693 ≤ 357564461) block2 block3

theorem join_1_0 : (twinPrimeSegment 357433389 357564461).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 357433389 ≤ 357498925)
    (by decide : 357498925 ≤ 357564461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 357433389 357564461).card = 447 := join_1_0

end S170C07
end Sude.GeneratedTwinScan
