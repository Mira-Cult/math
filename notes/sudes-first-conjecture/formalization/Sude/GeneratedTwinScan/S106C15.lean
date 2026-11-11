import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14976)) 224264237 224297005 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 224264237 224297005).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14976 224264237 224297005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14977)) 224297005 224329773 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 224297005 224329773).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14977 224297005 224329773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14978)) 224329773 224362541 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 224329773 224362541).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14978 224329773 224362541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14979)) 224362541 224395309 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 224362541 224395309).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14979 224362541 224395309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 224264237 224329773).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 224264237 ≤ 224297005)
    (by decide : 224297005 ≤ 224329773) block0 block1

theorem join_0_1 : (twinPrimeSegment 224329773 224395309).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 224329773 ≤ 224362541)
    (by decide : 224362541 ≤ 224395309) block2 block3

theorem join_1_0 : (twinPrimeSegment 224264237 224395309).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 224264237 ≤ 224329773)
    (by decide : 224329773 ≤ 224395309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 224264237 224395309).card = 461 := join_1_0

end S106C15
end Sude.GeneratedTwinScan
