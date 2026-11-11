import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16760)) 280887341 280920109 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 280887341 280920109).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16760 280887341 280920109
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16761)) 280920109 280952877 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 280920109 280952877).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16761 280920109 280952877
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16762)) 280952877 280985645 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 280952877 280985645).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16762 280952877 280985645
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16763)) 280985645 281018413 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 280985645 281018413).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16763 280985645 281018413
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 280887341 280952877).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 280887341 ≤ 280920109)
    (by decide : 280920109 ≤ 280952877) block0 block1

theorem join_0_1 : (twinPrimeSegment 280952877 281018413).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 280952877 ≤ 280985645)
    (by decide : 280985645 ≤ 281018413) block2 block3

theorem join_1_0 : (twinPrimeSegment 280887341 281018413).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 280887341 ≤ 280952877)
    (by decide : 280952877 ≤ 281018413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 280887341 281018413).card = 482 := join_1_0

end S133C15
end Sude.GeneratedTwinScan
