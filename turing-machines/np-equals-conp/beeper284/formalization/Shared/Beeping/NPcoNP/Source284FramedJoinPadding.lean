import Shared.Beeping.NPcoNP.Source284FramedJoinCoverage

/-! Quantify the zero runway retained above the joined witness prefix. This
is the input to the separately proved finite-window serializer interface. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FramedJoinPadding

open Shared.Beeping.NPcoNP.Source284CertificateJoin (witnessTail)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284BitWindow (Agree)

/-- One scratch shift consumes a known zero, leaving the indicated power of
two before any original high witness suffix. -/
theorem tail_formula (z n suffix : Nat) :
    witnessTail z n suffix/2 = 2^(z+2*n+4)*(suffix/4) := by
  have he : z+2*n+4 = z+(2*n+2)+2 := by omega
  have hm : witnessTail z n suffix = 2*(2^(z+2*n+4)*(suffix/4)) := by
    unfold witnessTail
    rw [he,pow_add,pow_add,pow_succ]
    norm_num
    ring
  rw [hm]
  omega

theorem tail_divisible (z n suffix : Nat) :
    2^(z+2*n+4) ∣ witnessTail z n suffix/2 := by
  rw [tail_formula]
  exact dvd_mul_right _ _

/-- After a finite prefix is consumed, all remaining low cells are zero
whenever the requested observation depth fits the paid quadratic runway. -/
theorem tail_after_prefix_zero (z n suffix skip depth : Nat)
    (hfit : skip+depth ≤ z+2*n+4) :
    2^depth ∣ (witnessTail z n suffix/2)/2^skip := by
  have hpow : 2^(skip+depth) ∣ witnessTail z n suffix/2 :=
    dvd_trans (Nat.pow_dvd_pow 2 hfit) (tail_divisible z n suffix)
  have hpref : 2^skip ∣ witnessTail z n suffix/2 := by
    exact dvd_trans (Nat.pow_dvd_pow 2 (by omega)) (tail_divisible z n suffix)
  apply (Nat.dvd_div_iff_mul_dvd hpref).2
  simpa [pow_add,Nat.mul_comm] using hpow

/-- The standard finite-window relation follows without any assumption on
the certificate's ignored suffix bits. -/
theorem tail_after_prefix_agree (k n suffix skip depth : Nat)
    (hfit : skip+depth ≤ firstZeros k n+2*n+4) :
    Agree depth ((witnessTail (firstZeros k n) n suffix/2)/2^skip) 0 := by
  have h := tail_after_prefix_zero (firstZeros k n) n suffix skip depth hfit
  simp [Agree,Nat.mod_eq_zero_of_dvd h]

/-- The precise seeded-suffix zero-window hypothesis used by the existing
serializer follows when its seed length and observation depth fit. -/
theorem serializer_seed_agree (k n suffix skip depth : Nat)
    (hfit : skip+depth ≤ firstZeros k n+2*n+4) :
    Agree depth (2*((2*(witnessTail (firstZeros k n) n suffix/2))/2^(skip+1))) 0 := by
  have hd := tail_after_prefix_zero (firstZeros k n) n suffix skip depth hfit
  have he (t : Nat) : 2*t/2^(skip+1)=t/2^skip := by
    rw [pow_succ, Nat.mul_comm (2^skip) 2, Nat.mul_div_mul_left _ _ (by decide)]
  rw [he]
  have hm : 2^depth ∣ 2*((witnessTail (firstZeros k n) n suffix/2)/2^skip) := dvd_mul_of_dvd_right hd 2
  simp [Agree,Nat.mod_eq_zero_of_dvd hm]

end Shared.Beeping.NPcoNP.Source284FramedJoinPadding
