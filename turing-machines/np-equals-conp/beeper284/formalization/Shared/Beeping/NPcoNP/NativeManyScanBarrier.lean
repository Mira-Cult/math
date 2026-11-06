import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! Unary scan words exclude early adjacent-zero stops. -/
namespace Shared.Beeping.NPcoNP.NativeManyScanBarrier
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem word_one (t : Int → Bool) (a q : Int) (n : Nat)
    (word : Holds t a (List.replicate n true ++ [false]))
    (lo : a ≤ q) (hi : q < a+(n : Int)) : t q=true := by
  let i := (q-a).toNat
  have he : (i : Int)=q-a := Int.toNat_of_nonneg (by omega)
  have hn : i<n := by omega
  have hl : i<(List.replicate n true ++ [false]).length := by simp; omega
  have hv := holds_get t a (List.replicate n true ++ [false]) word i hl
  have ha : a+(i : Int)=q := by omega
  rw [ha] at hv
  simpa [hn] using hv

/-- Two unary words followed by delimiters cannot contain adjacent zeros
strictly above the cleared selector cell. The second word must be nonempty.
The conclusion also applies to a later tape agreeing on the scanned interval. -/
theorem two_word_barrier (t u : Int → Bool) (d : Int) (p n : Nat)
    (hn : 0<n)
    (first : Holds t (d+1) (List.replicate p true ++ [false]))
    (second : Holds t (d+(p : Int)+2) (List.replicate n true ++ [false]))
    (agree : ∀ q, d+1≤q → q≤d+(p : Int)+(n : Int)+2 → u q=t q) :
    ∀ q, d+2≤q → q≤d+(p : Int)+(n : Int)+2 →
      u q=false → u (q-1)=true := by
  intro q hq htop hz
  have heq : u q=t q := agree q (by omega) htop
  have hpreeq : u (q-1)=t (q-1) := agree (q-1) (by omega) (by omega)
  rw [hpreeq]
  by_cases hfirst : q<d+(p : Int)+1
  · have hh := word_one t (d+1) q p first (by omega) (by omega)
    rw [heq,hh] at hz
    contradiction
  · by_cases hdelim : q=d+(p : Int)+1
    · apply word_one t (d+1) (q-1) p first <;> omega
    · by_cases hsecond : q<d+(p : Int)+(n : Int)+2
      · have hh := word_one t (d+(p : Int)+2) q n second (by omega) (by omega)
        rw [heq,hh] at hz
        contradiction
      · apply word_one t (d+(p : Int)+2) (q-1) n second <;> omega

#print axioms word_one
#print axioms two_word_barrier
end Shared.Beeping.NPcoNP.NativeManyScanBarrier
