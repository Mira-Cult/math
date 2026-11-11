import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20773)) 431489069 431521837 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 431489069 431521837).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20773 431489069 431521837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20773)) 431521837 431554605 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 431521837 431554605).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20773 431521837 431554605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20774)) 431554605 431587373 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 431554605 431587373).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20774 431554605 431587373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20775)) 431587373 431620141 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 431587373 431620141).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20775 431587373 431620141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 431489069 431554605).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 431489069 ≤ 431521837)
    (by decide : 431521837 ≤ 431554605) block0 block1

theorem join_0_1 : (twinPrimeSegment 431554605 431620141).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 431554605 ≤ 431587373)
    (by decide : 431587373 ≤ 431620141) block2 block3

theorem join_1_0 : (twinPrimeSegment 431489069 431620141).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 431489069 ≤ 431554605)
    (by decide : 431554605 ≤ 431620141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 431489069 431620141).card = 427 := join_1_0

end S205C12
end Sude.GeneratedTwinScan
