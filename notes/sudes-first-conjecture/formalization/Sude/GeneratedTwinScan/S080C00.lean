import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12953)) 167772205 167804973 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 167772205 167804973).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12953 167772205 167804973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12955)) 167804973 167837741 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 167804973 167837741).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12955 167804973 167837741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12956)) 167837741 167870509 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 167837741 167870509).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12956 167837741 167870509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12957)) 167870509 167903277 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 167870509 167903277).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12957 167870509 167903277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 167772205 167837741).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 167772205 ≤ 167804973)
    (by decide : 167804973 ≤ 167837741) block0 block1

theorem join_0_1 : (twinPrimeSegment 167837741 167903277).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 167837741 ≤ 167870509)
    (by decide : 167870509 ≤ 167903277) block2 block3

theorem join_1_0 : (twinPrimeSegment 167772205 167903277).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 167772205 ≤ 167837741)
    (by decide : 167837741 ≤ 167903277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 167772205 167903277).card = 495 := join_1_0

end S080C00
end Sude.GeneratedTwinScan
