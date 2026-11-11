import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S121C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15980)) 255328301 255361069 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 255328301 255361069).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15980 255328301 255361069
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15981)) 255361069 255393837 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 255361069 255393837).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15981 255361069 255393837
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15982)) 255393837 255426605 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 255393837 255426605).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15982 255393837 255426605
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15983)) 255426605 255459373 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 255426605 255459373).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15983 255426605 255459373
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 255328301 255393837).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 255328301 ≤ 255361069)
    (by decide : 255361069 ≤ 255393837) block0 block1

theorem join_0_1 : (twinPrimeSegment 255393837 255459373).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 255393837 ≤ 255426605)
    (by decide : 255426605 ≤ 255459373) block2 block3

theorem join_1_0 : (twinPrimeSegment 255328301 255459373).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 255328301 ≤ 255393837)
    (by decide : 255393837 ≤ 255459373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 255328301 255459373).card = 472 := join_1_0

end S121C12
end Sude.GeneratedTwinScan
