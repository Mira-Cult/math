import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14055)) 197525549 197558317 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 197525549 197558317).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14055 197525549 197558317
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14056)) 197558317 197591085 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 197558317 197591085).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14056 197558317 197591085
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14057)) 197591085 197623853 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 197591085 197623853).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14057 197591085 197623853
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14059)) 197623853 197656621 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 197623853 197656621).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14059 197623853 197656621
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 197525549 197591085).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 197525549 ≤ 197558317)
    (by decide : 197558317 ≤ 197591085) block0 block1

theorem join_0_1 : (twinPrimeSegment 197591085 197656621).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 197591085 ≤ 197623853)
    (by decide : 197623853 ≤ 197656621) block2 block3

theorem join_1_0 : (twinPrimeSegment 197525549 197656621).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 197525549 ≤ 197591085)
    (by decide : 197591085 ≤ 197656621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 197525549 197656621).card = 445 := join_1_0

end S094C03
end Sude.GeneratedTwinScan
