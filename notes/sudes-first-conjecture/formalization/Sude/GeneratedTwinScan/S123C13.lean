import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16114)) 259653677 259686445 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 259653677 259686445).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16114 259653677 259686445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16115)) 259686445 259719213 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 259686445 259719213).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16115 259686445 259719213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16116)) 259719213 259751981 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 259719213 259751981).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16116 259719213 259751981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16117)) 259751981 259784749 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 259751981 259784749).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16117 259751981 259784749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 259653677 259719213).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 259653677 ≤ 259686445)
    (by decide : 259686445 ≤ 259719213) block0 block1

theorem join_0_1 : (twinPrimeSegment 259719213 259784749).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 259719213 ≤ 259751981)
    (by decide : 259751981 ≤ 259784749) block2 block3

theorem join_1_0 : (twinPrimeSegment 259653677 259784749).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 259653677 ≤ 259719213)
    (by decide : 259719213 ≤ 259784749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 259653677 259784749).card = 454 := join_1_0

end S123C13
end Sude.GeneratedTwinScan
