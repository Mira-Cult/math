import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21834)) 476708909 476741677 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 476708909 476741677).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21834 476708909 476741677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21835)) 476741677 476774445 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 476741677 476774445).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21835 476741677 476774445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21835)) 476774445 476807213 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 476774445 476807213).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21835 476774445 476807213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21836)) 476807213 476839981 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 476807213 476839981).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21836 476807213 476839981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 476708909 476774445).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 476708909 ≤ 476741677)
    (by decide : 476741677 ≤ 476774445) block0 block1

theorem join_0_1 : (twinPrimeSegment 476774445 476839981).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 476774445 ≤ 476807213)
    (by decide : 476807213 ≤ 476839981) block2 block3

theorem join_1_0 : (twinPrimeSegment 476708909 476839981).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 476708909 ≤ 476774445)
    (by decide : 476774445 ≤ 476839981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 476708909 476839981).card = 409 := join_1_0

end S227C05
end Sude.GeneratedTwinScan
