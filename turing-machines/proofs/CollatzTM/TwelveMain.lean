import CollatzTM.Binary
import CollatzTM.Global

namespace CollatzTM.M12

open Arithmetic

/-- The exact positive-one macro, with blank output and its absolute final head. -/
theorem canonicalNat_one (p : Int) :
    Reaches delta 3 (canonicalNat 1 p) (cfg none (p+1) zeros zeros) := by
  simpa [canonicalNat,Binary.bits] using canonical_one p

/-- The exact even macro on every positive even input larger than one. -/
theorem canonicalNat_even (n : Nat) (p : Int) (hn : 1<n) (hp : n%2=0) :
    Reaches delta 2 (canonicalNat n p) (canonicalNat (n/2) (p+2)) := by
  have hN := Binary.bits_normal n (by omega)
  have hV := Binary.value_bits n
  cases he : Binary.bits n with
  | nil => exact False.elim (hN.1 he)
  | cons b bs =>
    have hv : b.toNat+2*value bs=n := by simpa [he,value] using hV
    have hb : b=false := by cases b <;> simp at hv ⊢ <;> omega
    subst b
    have hbs : bs≠[] := by intro e; subst bs; simp [value] at hv; omega
    have hbsN := Binary.normal_tail false bs (by simpa [he] using hN) hbs
    have hbsV : value bs=n/2 := by simp at hv; omega
    have eb : bs=Binary.bits (n/2) := by
      rw [Binary.normal_eq_bits bs hbsN,hbsV]
    simpa only [canonicalNat,he,←eb] using canonical_even bs p

/-- The exact odd macro, including its claimed duration, for every odd n>1. -/
theorem canonicalNat_odd (n : Nat) (p : Int) (hn : 1<n) (hp : n%2=1) :
    Reaches delta (4*Binary.bitlength ((3*n+1)/2)+4)
      (canonicalNat n p) (canonicalNat ((3*n+1)/2) (p+2)) := by
  have hN := Binary.bits_normal n (by omega)
  have hV := Binary.value_bits n
  cases he : Binary.bits n with
  | nil => exact False.elim (hN.1 he)
  | cons b bs =>
    have hv : b.toNat+2*value bs=n := by simpa [he,value] using hV
    have hb : b=true := by cases b <;> simp at hv ⊢ <;> omega
    subst b
    have hbs : bs≠[] := by intro e; subst bs; simp [value] at hv; omega
    have hbsN := Binary.normal_tail true bs (by simpa [he] using hN) hbs
    have hoN := output_normal .c2 bs (normal_good .c2 bs hbsN)
    have hoV : value (output .c2 bs)=(3*n+1)/2 := by
      rw [output_value]
      simp only [carryValue]
      simp at hv
      omega
    have eo : output .c2 bs=Binary.bits ((3*n+1)/2) := by
      rw [Binary.normal_eq_bits _ hoN,hoV]
    have hl : (output .c2 bs).length=Binary.bitlength ((3*n+1)/2) := by
      rw [Binary.normal_length_bitlength _ hoN,hoV]
    simpa only [canonicalNat,he,←eo,←hl] using canonical_odd bs hbsN p

/-- All finite-support, exact-head macros imply this complete evaluator interface. -/
theorem evaluatorSpec : EvaluatorSpec delta shortcut canonicalNat := by
  refine ⟨shortcut_pos,?_,?_,?_⟩
  · intro n p hn
    simp [canonicalNat,canonical,cfg]
  · intro p
    refine ⟨3,?_⟩
    rw [(canonicalNat_one p).1]
    rfl
  · intro n p hn
    by_cases hp : n%2=0
    · refine ⟨2,by decide,?_⟩
      rw [shortcut_even n hp]
      exact (canonicalNat_even n p hn hp).1
    · refine ⟨4*Binary.bitlength ((3*n+1)/2)+4,by omega,?_⟩
      have hp' : n%2=1 := by omega
      rw [shortcut_odd n hp']
      exact (canonicalNat_odd n p hn hp').1

/-- The exact twelve-state table halts precisely when the ordinary positive
    Collatz orbit of its input reaches one. -/
theorem halts_iff_collatz (n : Nat) (p : Int) (hn : 0<n) :
    Halts delta (canonicalNat n p) ↔ ∃ k, uit k n=1 :=
  evaluator_ordinary_correct delta canonicalNat evaluatorSpec n p hn

/-- Universal termination of this exact input-taking machine is equivalent to
    the ordinary Collatz conjecture; the conjecture itself is not asserted. -/
theorem totality_iff_collatz :
    (∀ n, 0<n → Halts delta (canonicalNat n 0)) ↔
    (∀ n, 0<n → ∃ k, uit k n=1) :=
  evaluator_totality_ordinary delta canonicalNat evaluatorSpec

theorem canonicalNat_finite (n : Nat) (p : Int) : FiniteTape (canonicalNat n p).tape :=
  canonical_finite (Binary.bits n) p

end CollatzTM.M12
