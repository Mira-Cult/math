import Shared.Beeping.NPcoNP.UnarySuffixShift
import Shared.Beeping.NPcoNP.NativeHalfSweep

/-! Tape identities for the three writes at the beginning of a prepared
regular native-HALF cycle.  These are functional tape equations, not a
claim that the literal machine reaches the supplied boundary. -/
namespace Shared.Beeping.NPcoNP.NativeHalfCycleTape
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.NativeHalfSweep

/-- Before the three local writes, the boundary cell is zero and the next
two cells are one.  The suffix beginning after them has the producer's
two-zero-gap representation after those writes. -/
def prior (base : Int → Bool) (boundary : Int) (suffix : List Bool) : Int → Bool :=
  put (put (put (before base (boundary+1) suffix) boundary false)
    (boundary+1) true) (boundary+2) true

theorem prior_boundary (base : Int → Bool) (b : Int) (suffix : List Bool) :
    prior base b suffix b = false := by
  simp [prior, put]

theorem prior_first (base : Int → Bool) (b : Int) (suffix : List Bool) :
    prior base b suffix (b+1) = true := by
  have h : b+1 ≠ b+2 := by omega
  simp [prior, put, h]

theorem prior_second (base : Int → Bool) (b : Int) (suffix : List Bool) :
    prior base b suffix (b+2) = true := by simp [prior, put]

/-- Writing one at the boundary and zero at the next two cells creates the
exact input tape required by the checked suffix-shift segment. -/
theorem three_writes (base : Int → Bool) (b : Int) (suffix : List Bool)
    (hb : base b = true) :
    put (put (put (prior base b suffix) b true) (b+1) false) (b+2) false =
      before base (b+1) suffix := by
  funext p
  by_cases h0 : p = b
  · subst p
    have hb' : before base (b+1) suffix b = true := by
      rw [before_prefix base (b+1) b suffix (by omega), hb]
    simpa [prior, put] using hb'.symm
  by_cases h1 : p = b+1
  · subst p
    have hz := (gap_cells base (b+1) suffix).1
    have hne : b+1 ≠ b+2 := by omega
    simpa [prior, put, hne] using hz.symm
  by_cases h2 : p = b+2
  · subst p
    have hz := (gap_cells base (b+1) suffix).2.1
    have he : b+1+1 = b+2 := by omega
    rw [he] at hz
    simpa [prior, put] using hz.symm
  · simp [prior, put, h0, h1, h2]

/-- The suffix shift preserves the boundary's newly written one, so the
actual return-row branch reads one at this protected cell. -/
theorem return_boundary (base : Int → Bool) (b : Int) (suffix : List Bool)
    (hb : base b = true) : after base (b+1) suffix b = true := by
  rw [after_prefix base (b+1) b suffix (by omega), hb]

end Shared.Beeping.NPcoNP.NativeHalfCycleTape
