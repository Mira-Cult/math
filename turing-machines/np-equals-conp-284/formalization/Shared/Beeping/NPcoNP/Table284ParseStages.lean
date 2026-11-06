import Shared.Beeping.NPcoNP.Table284Ascii

/-! Staged parsing helpers for the restricted event-table format. These are
generic list facts; they do not identify the pinned table with any data. -/

namespace Shared.Beeping.NPcoNP.Table284Ascii

/-- Join a nonempty list of lines with a delimiter, preserving a final empty
line when the represented text ends in that delimiter. -/
def joinLines (sep : Char) : List (List Char) → List Char
  | [] => []
  | [line] => line
  | line :: rest => line ++ sep :: joinLines sep rest

theorem split_no_sep (sep : Char) (line : List Char) (h : sep ∉ line) :
    split sep line = [line] := by
  induction line with
  | nil => rfl
  | cons c cs ih =>
    have hh : sep ≠ c ∧ sep ∉ cs := by simpa only [List.mem_cons, not_or] using h
    have hc : c ≠ sep := Ne.symm hh.1
    have ht : sep ∉ cs := hh.2
    simp [split, hc, ih ht]

theorem split_line_sep (sep : Char) (line rest : List Char) (h : sep ∉ line) :
    split sep (line ++ sep :: rest) = line :: split sep rest := by
  induction line with
  | nil => simp [split]
  | cons c cs ih =>
    have hh : sep ≠ c ∧ sep ∉ cs := by simpa only [List.mem_cons, not_or] using h
    have hc : c ≠ sep := Ne.symm hh.1
    have ht : sep ∉ cs := hh.2
    simp [split, hc, ih ht]

/-- Splitting a well-formed nonempty line list round-trips exactly. -/
theorem split_joinLines (sep : Char) (lines : List (List Char))
    (hne : lines ≠ []) (h : ∀ line ∈ lines, sep ∉ line) :
    split sep (joinLines sep lines) = lines := by
  induction lines with
  | nil => contradiction
  | cons line rest ih =>
    have hl : sep ∉ line := h line (by simp)
    cases rest with
    | nil => simpa [joinLines] using split_no_sep sep line hl
    | cons next tail =>
      have ht : ∀ x ∈ next :: tail, sep ∉ x := by
        intro x hx
        exact h x (by simp [hx])
      simp only [joinLines]
      rw [split_line_sep sep line _ hl]
      rw [ih (by simp) ht]

end Shared.Beeping.NPcoNP.Table284Ascii
