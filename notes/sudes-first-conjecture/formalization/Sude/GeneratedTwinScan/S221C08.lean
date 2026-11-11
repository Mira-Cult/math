import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21553)) 464519213 464551981 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 464519213 464551981).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21553 464519213 464551981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21554)) 464551981 464584749 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 464551981 464584749).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21554 464551981 464584749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21554)) 464584749 464617517 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 464584749 464617517).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21554 464584749 464617517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21555)) 464617517 464650285 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 464617517 464650285).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21555 464617517 464650285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 464519213 464584749).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 464519213 ≤ 464551981)
    (by decide : 464551981 ≤ 464584749) block0 block1

theorem join_0_1 : (twinPrimeSegment 464584749 464650285).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 464584749 ≤ 464617517)
    (by decide : 464617517 ≤ 464650285) block2 block3

theorem join_1_0 : (twinPrimeSegment 464519213 464650285).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 464519213 ≤ 464584749)
    (by decide : 464584749 ≤ 464650285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 464519213 464650285).card = 415 := join_1_0

end S221C08
end Sude.GeneratedTwinScan
