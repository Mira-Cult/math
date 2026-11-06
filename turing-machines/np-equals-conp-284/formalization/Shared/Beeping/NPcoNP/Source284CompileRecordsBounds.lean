import Shared.Beeping.NPcoNP.Source284CompileRecords

/-! Explicit unary-record bounds for the existing finite binary program
compiler. Terminal destinations are ignored by the compiler, so they need
not be bounded; continuing destinations are bounded by `valid`. These are
size/guard facts, not a proof that records are constructed in polynomial time. -/
namespace Shared.Beeping.NPcoNP.Source284CompileRecordsBounds

open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284CompileRecords

theorem pack_le (w t : Bool) (next : Nat) : pack w t next ≤ 4*next+3 := by
  cases w <;> cases t <;> simp [pack, bit] <;> omega

/-- A valid finite-program row encodes to a unary source-record value linear
in the program state count. -/
theorem encodedRow_le (n : Nat) (rev : Bool) (row : Row)
    (hv : validRow n row = true) : encodedRow n rev row ≤ 16*n+7 := by
  by_cases hzero : row.2.2.2 = 0
  · have hn : row.2.2.1 < n := by
      simpa [validRow, hzero] using hv
    have hb := bit_lt (!row.2.1)
    have hnext : codeState row.2.2.1 (!row.2.1) ≤ 4*n+1 := by
      simp only [codeState]
      omega
    have hp : pack row.1 (xor rev (!row.2.1))
        (codeState row.2.2.1 (!row.2.1)) ≤ 16*n+7 := by
      have hh := pack_le row.1 (xor rev (!row.2.1)) (codeState row.2.2.1 (!row.2.1))
      omega
    simpa only [encodedRow, hzero, ↓reduceIte] using hp
  · by_cases htrue : row.2.2.2 = 2
    · have hp : pack row.1 (xor rev (!row.2.1)) 0 ≤ 16*n+7 := by
        have hh := pack_le row.1 (xor rev (!row.2.1)) 0
        omega
      have h20 : (2 : Nat) ≠ 0 := by decide
      simpa only [encodedRow, htrue, h20, ↓reduceIte] using hp
    · have hnext : rejectState n = 4*n+1 := by simp [rejectState, codeState, bit]
      have hp : pack row.1 (xor rev (!row.2.1)) (rejectState n) ≤ 16*n+7 := by
        have hh := pack_le row.1 (xor rev (!row.2.1)) (rejectState n)
        omega
      simpa only [encodedRow, hzero, htrue, ↓reduceIte] using hp

/-- Every emitted record, including both orientations of the reserved
reject sink, fits the same finite-state bound. -/
theorem records_le (p : Program) (hv : valid p = true) :
    ∀ v ∈ records p, v ≤ 16*p.length+7 := by
  have hall : ∀ rows ∈ p, validRow p.length rows.1 = true ∧
      validRow p.length rows.2 = true := by
    have h := hv
    simp only [valid, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at h
    intro rows hr
    simpa only [Bool.and_eq_true] using h.2 rows hr
  intro v hm
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hm
  by_cases hq : i.val / 4 < p.length
  · have hp := hall p[i.val / 4] (List.getElem_mem hq)
    have hrow : validRow p.length
        (if i.val % 2 = 1 then p[i.val / 4].2 else p[i.val / 4].1) = true := by
      split_ifs <;> simp_all
    simpa only [recordAt, hq, ↓reduceDIte] using
      encodedRow_le p.length (decide ((i.val / 2) % 2 = 1)) _ hrow
  · have hnext : rejectState p.length = 4*p.length+1 := by simp [rejectState, codeState, bit]
    have hp : pack (decide (i.val % 2 = 1)) (decide ((i.val / 2) % 2 = 1))
        (rejectState p.length) ≤ 16*p.length+7 := by
      have hh := pack_le (decide (i.val % 2 = 1)) (decide ((i.val / 2) % 2 = 1))
        (rejectState p.length)
      omega
    simpa only [recordAt, hq, ↓reduceDIte] using hp

/-- The automatic `4 * recordCount + 7` unary budget used by the bounded
serializer covers every record of any valid finite program. -/
theorem records_fit_budget (p : Program) (hv : valid p = true) :
    ∀ v ∈ records p, v ≤ 4*(records p).length+7 := by
  intro v hm
  have h := records_le p hv v hm
  simp only [records, List.length_ofFn]
  omega

end Shared.Beeping.NPcoNP.Source284CompileRecordsBounds
