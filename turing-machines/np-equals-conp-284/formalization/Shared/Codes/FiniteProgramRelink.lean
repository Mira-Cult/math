import Shared.Codes.FiniteProgramTaggedExtend

/-! Generic replacement of a linked table's payload without changing the
prefix. All data and numeric state destinations remain finite. -/
namespace Shared.Codes.FiniteProgramRelink
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair)

/-- Any prefix row is independent of the linked payload and suffix. -/
theorem prefix_step (pre p q suffix₁ suffix₂ : Program) (c : Config) (hc : c.1 < pre.length) :
    step (link pre p suffix₁) c = step (link pre q suffix₂) c := by
  have h₁ : (link pre p suffix₁)[c.1]? = pre[c.1]? := by simp [link,List.getElem?_append_left,hc]
  have h₂ : (link pre q suffix₂)[c.1]? = pre[c.1]? := by simp [link,List.getElem?_append_left,hc]
  simp [step,h₁,h₂]

/-- Replacing a valid payload with a valid payload of at least the same size
preserves validity of the entire linked finite table. -/
theorem valid_relink (pre old new : Program) (hold : valid (link pre old []) = true)
    (hnew : valid new = true) (hlen : old.length ≤ new.length) : valid (link pre new []) = true := by
  let oldTable := link pre old []
  let newTable := link pre new []
  let m := pre.length+new.length
  have hm : newTable.length = m := by simp [newTable,link,m]
  have ho : oldTable.length ≤ m := by simp [oldTable,link,m]; omega
  have hp : ∀ r ∈ pre, validRow m r.1 = true ∧ validRow m r.2 = true := by
    intro r hr
    have hin : r ∈ oldTable := by simp [oldTable,link,hr]
    have hv := hold
    change valid oldTable = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    have h := hv.2 r hin
    have h' : validRow oldTable.length r.1 = true ∧ validRow oldTable.length r.2 = true := by
      simpa only [Bool.and_eq_true] using h
    exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ ho h'.1,
      Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ ho h'.2⟩
  have hn : ∀ r ∈ new, validRow new.length r.1 = true ∧ validRow new.length r.2 = true := by
    intro r hr
    have hv := hnew
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hall : newTable.all (fun r => validRow newTable.length r.1 && validRow newTable.length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ pre ∨ r ∈ new.map (shiftPair pre.length) := by
      simpa [newTable,link,List.mem_append] using hr
    rw [hm]
    rcases hr' with hpre | hmap
    · simpa only [Bool.and_eq_true] using hp r hpre
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hmap
      obtain ⟨h₁,h₂⟩ := hn r' hr'
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 pre.length new.length h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 pre.length new.length h₂⟩
  have hnonempty : newTable.isEmpty = false := by
    have hpos := Shared.Codes.FiniteProgramLink.valid_nonempty new hnew
    cases h : newTable with
    | nil => simp [h] at hm; dsimp [m] at hm; omega
    | cons r rs => rfl
  change (!newTable.isEmpty && newTable.all
    (fun r => validRow newTable.length r.1 && validRow newTable.length r.2)) = true
  rw [hnonempty,hall]
  rfl

end Shared.Codes.FiniteProgramRelink
