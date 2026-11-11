import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21741)) 472645677 472678445 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 472645677 472678445).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21741 472645677 472678445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21741)) 472678445 472711213 = 93 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 472678445 472711213).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21741 472678445 472711213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21742)) 472711213 472743981 = 90 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 472711213 472743981).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21742 472711213 472743981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21743)) 472743981 472776749 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 472743981 472776749).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21743 472743981 472776749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 472645677 472711213).card = 203 := by
  simpa using combineTwinPrimeSegments (by decide : 472645677 ≤ 472678445)
    (by decide : 472678445 ≤ 472711213) block0 block1

theorem join_0_1 : (twinPrimeSegment 472711213 472776749).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 472711213 ≤ 472743981)
    (by decide : 472743981 ≤ 472776749) block2 block3

theorem join_1_0 : (twinPrimeSegment 472645677 472776749).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 472645677 ≤ 472711213)
    (by decide : 472711213 ≤ 472776749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 472645677 472776749).card = 409 := join_1_0

end S225C06
end Sude.GeneratedTwinScan
