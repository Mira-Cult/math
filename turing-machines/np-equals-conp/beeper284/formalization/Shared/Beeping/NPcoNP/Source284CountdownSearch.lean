import Shared.Beeping.NPcoNP.Source284TableCountdown

/-! Executable bounded rectangle search for the countdown guard's paired
state indices. The search uses finite lists and `Nat.pair`, rather than
`Nat.unpair` or square root at runtime. This module proves its semantics;
it does not yet prove a polynomial-time implementation in the canonical
machine model or construct and serialize the whole guarded table. -/
namespace Shared.Beeping.NPcoNP.Source284CountdownSearch

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableCountdown

/-- Enumerate all elapsed-state coordinates in the finite live rectangle. -/
def rectangle (n cutoff : Nat) : List (Nat × Nat) :=
  (List.range cutoff).flatMap fun e => (List.range n).map fun q => (e, q)

@[simp] theorem mem_rectangle (n cutoff e q : Nat) :
    (e, q) ∈ rectangle n cutoff ↔ e < cutoff ∧ q < n := by
  simp [rectangle]

/-- `none` means that the requested source state is outside the live
rectangle; otherwise the unique coordinate pair is returned. -/
def search (n cutoff s : Nat) : Option (Nat × Nat) :=
  (rectangle n cutoff).find? fun p => Nat.pair p.1 p.2 == s

theorem search_some_iff (n cutoff s e q : Nat) :
    search n cutoff s = some (e, q) ↔
      e < cutoff ∧ q < n ∧ Nat.pair e q = s := by
  constructor
  · intro h
    have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    have hm' : (e, q) ∈ rectangle n cutoff := hm
    have hp' : Nat.pair e q = s := by simpa using hp
    rcases (mem_rectangle n cutoff e q).1 hm' with ⟨he, hq⟩
    exact ⟨he, hq, hp'⟩
  · rintro ⟨he, hq, hp⟩
    have hm : (e, q) ∈ rectangle n cutoff := (mem_rectangle n cutoff e q).2 ⟨he, hq⟩
    have hh : (rectangle n cutoff).find? (fun p => Nat.pair p.1 p.2 == s) ≠ none := by
      intro hn
      have hh := (List.find?_eq_none.mp hn) (e, q) hm
      simp [hp] at hh
    cases hs : search n cutoff s with
    | none => exact False.elim (hh hs)
    | some p =>
      have heq := List.find?_some hs
      have heq' : Nat.pair p.1 p.2 = s := by simpa using heq
      have hi : p = (e, q) := by
        apply Prod.ext
        · have hu := congrArg (fun v => (Nat.unpair v).1) (heq'.trans hp.symm)
          simpa using hu
        · have hu := congrArg (fun v => (Nat.unpair v).2) (heq'.trans hp.symm)
          simpa using hu
      simpa [hi]

theorem search_eq (n cutoff s : Nat) :
    search n cutoff s =
      if (Nat.unpair s).1 < cutoff ∧ (Nat.unpair s).2 < n then
        some (Nat.unpair s) else none := by
  by_cases h : (Nat.unpair s).1 < cutoff ∧ (Nat.unpair s).2 < n
  · simp only [h, ↓reduceIte]
    have h' := (search_some_iff n cutoff s (Nat.unpair s).1 (Nat.unpair s).2).2
      ⟨h.1, h.2, Nat.pair_unpair s⟩
    simpa using h'
  · simp only [h, ↓reduceIte]
    cases hs : search n cutoff s with
    | none => rfl
    | some p =>
      obtain ⟨he, hq, hp⟩ := (search_some_iff n cutoff s p.1 p.2).1 (by simpa using hs)
      have hs' : Nat.unpair s = p := by
        rw [← hp, Nat.unpair_pair]
      rw [hs'] at h
      exact False.elim (h ⟨he, hq⟩)

/-- A runtime-search formulation of the identical guard row. -/
def searchTable (n cutoff : Nat) (original : Nat → Bool → Row) (s : Nat) (read : Bool) : Row :=
  if s = sink n cutoff then sinkRow n cutoff read
  else match search n cutoff s with
    | none => sinkRow n cutoff read
    | some p =>
      let r := original p.2 read
      ⟨r.write, r.turn,
        match r.next with
        | none => none
        | some q => if p.1 + 1 < cutoff ∧ q < n then
            some (Nat.pair (p.1+1) q) else some (sink n cutoff)⟩

theorem searchTable_eq (n cutoff : Nat) (original : Nat → Bool → Row)
    (s : Nat) (read : Bool) :
    searchTable n cutoff original s read = table n cutoff original s read := by
  by_cases hs : s = sink n cutoff
  · simp [searchTable, table, hs]
  · by_cases hp : (Nat.unpair s).1 < cutoff ∧ (Nat.unpair s).2 < n <;>
      simp [searchTable, search_eq, table, hs, hp] <;> rfl

end Shared.Beeping.NPcoNP.Source284CountdownSearch
