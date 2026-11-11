import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21287)) 453115949 453148717 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 453115949 453148717).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21287 453115949 453148717
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21288)) 453148717 453181485 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 453148717 453181485).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21288 453148717 453181485
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21288)) 453181485 453214253 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 453181485 453214253).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21288 453181485 453214253
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21289)) 453214253 453247021 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 453214253 453247021).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21289 453214253 453247021
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 453115949 453181485).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 453115949 ≤ 453148717)
    (by decide : 453148717 ≤ 453181485) block0 block1

theorem join_0_1 : (twinPrimeSegment 453181485 453247021).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 453181485 ≤ 453214253)
    (by decide : 453214253 ≤ 453247021) block2 block3

theorem join_1_0 : (twinPrimeSegment 453115949 453247021).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 453115949 ≤ 453181485)
    (by decide : 453181485 ≤ 453247021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 453115949 453247021).card = 437 := join_1_0

end S216C01
end Sude.GeneratedTwinScan
