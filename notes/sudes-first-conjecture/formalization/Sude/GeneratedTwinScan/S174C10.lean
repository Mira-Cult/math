import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19137)) 366215213 366247981 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 366215213 366247981).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19137 366215213 366247981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19138)) 366247981 366280749 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 366247981 366280749).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19138 366247981 366280749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19139)) 366280749 366313517 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 366280749 366313517).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19139 366280749 366313517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19140)) 366313517 366346285 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 366313517 366346285).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19140 366313517 366346285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 366215213 366280749).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 366215213 ≤ 366247981)
    (by decide : 366247981 ≤ 366280749) block0 block1

theorem join_0_1 : (twinPrimeSegment 366280749 366346285).card = 193 := by
  simpa using combineTwinPrimeSegments (by decide : 366280749 ≤ 366313517)
    (by decide : 366313517 ≤ 366346285) block2 block3

theorem join_1_0 : (twinPrimeSegment 366215213 366346285).card = 419 := by
  simpa using combineTwinPrimeSegments (by decide : 366215213 ≤ 366280749)
    (by decide : 366280749 ≤ 366346285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 366215213 366346285).card = 419 := join_1_0

end S174C10
end Sude.GeneratedTwinScan
