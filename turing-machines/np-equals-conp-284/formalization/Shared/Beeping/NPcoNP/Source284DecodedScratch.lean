import Shared.Beeping.NPcoNP.Source284TaggedMarkerPipeline

/-! Zero cells already supplied by the decoded witness layout. This is a
finite arithmetic guarantee; it does not construct extra padding. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284DecodedScratch

open Shared.Beeping.NPcoNP.Source284BitWindow (Agree)

/-- Exact scratch tail exposed by the joined-source decoder. -/
def tail (limit witnessSuffix : Nat) : Nat :=
  2^(2*((limit+1)+1))*((8*((witnessSuffix/4)/4)+1)/4)

/-- Before the marker seed, at least this many low scratch cells are zero. -/
theorem tail_divisible (limit witnessSuffix : Nat) :
    2^(2*((limit+1)+1)) ∣ 2*tail limit witnessSuffix := by
  refine ⟨2*((8*((witnessSuffix/4)/4)+1)/4),?_⟩
  simp [tail]
  ring

/-- If a number is divisible by `2^(window+skip)`, dropping `skip` low bits
leaves a zero window of the requested size. -/
theorem shifted_zero_window (scratch window skip : Nat)
    (h : 2^(window+skip) ∣ scratch) : Agree window (2*(scratch / 2^skip)) 0 := by
  obtain ⟨q,hq⟩ := h
  have hpow : 0 < 2^skip := pow_pos (by decide) _
  have hd : scratch / 2^skip = 2^window*q := by
    rw [hq,pow_add]
    calc
      (2^window * 2^skip * q) / 2^skip = (2^skip * (2^window*q)) / 2^skip := by congr 1; ring
      _ = 2^window*q := Nat.mul_div_cancel_left _ hpow
  unfold Agree
  rw [hd]
  have hz : 2^window ∣ 2*(2^window*q) := ⟨2*q,by ring⟩
  simp [Nat.mod_eq_zero_of_dvd hz]

/-- The recovered decoder supplies the pipeline's required zero window when
its length plus the fixed marker offset fits in the pre-existing scratch
padding. This sufficient inequality is not asserted for all inputs. -/
theorem decoded_zero_window (limit witnessSuffix window skip : Nat)
    (hsize : window+skip ≤ 2*((limit+1)+1)) :
    Agree window (2*((2*tail limit witnessSuffix)/2^skip)) 0 := by
  apply shifted_zero_window
  exact dvd_trans (pow_dvd_pow 2 hsize) (tail_divisible limit witnessSuffix)

namespace Fixtures
example : Agree 4 (2*((2*tail 4 12345)/2^3)) 0 := by
  apply decoded_zero_window
  omega
end Fixtures

end Shared.Beeping.NPcoNP.Source284DecodedScratch
