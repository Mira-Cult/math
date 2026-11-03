import Shared.PNP.Record285.GrammarCoreZeroEndpoint
import Shared.PNP.Record285.GrammarCoreEndpoint

/-! A finite checker for removing occurrence-specific zero decrements. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarCoreZero
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarCoreGraph

def shortcut (before : Array CoreRow) (selected : List Nat) (i : Nat) : Option Nat :=
  match before[i]? with
  | none => none
  | some row => if selected.contains i then some row.yes else some i

def rewriteRow (before after : Array CoreRow) (selected : List Nat) (mapping : Array Nat) (i : Nat) : Bool :=
  match mapping[i]?, after[i]? with
  | some old, some post =>
    match before[old]?, mapping[post.no]?, mapping[post.yes]? with
    | some pre, some no, some yes =>
      !selected.contains old && decide (pre.edge = post.edge) &&
        decide (shortcut before selected pre.no = some no) &&
        decide (shortcut before selected pre.yes = some yes)
    | _, _, _ => false
  | _, _ => false

def rewriteCheck (before after : Array CoreRow) (selected : List Nat) (mapping : Array Nat) : Bool :=
  decide (after.size = mapping.size) && decide (mapping[0]? = some 0) &&
    (List.range after.size).all (rewriteRow before after selected mapping)

theorem rewriteCheck_at (before after : Array CoreRow) (selected : List Nat) (mapping : Array Nat)
    (h : rewriteCheck before after selected mapping = true) (i : Nat) (hi : i < after.size) :
    rewriteRow before after selected mapping i = true := by
  have hall : (List.range after.size).all (rewriteRow before after selected mapping) = true := by
    simp only [rewriteCheck,Bool.and_eq_true_iff] at h
    exact h.2
  exact List.all_eq_true.mp hall i (List.mem_range.mpr hi)

/-- The certificate exposes both retained successor obligations, independently
of whether either branch is reachable. -/
theorem rewriteRow_sound (before after : Array CoreRow) (selected : List Nat) (mapping : Array Nat)
    (i old : Nat) (post : CoreRow) (hmap : mapping[i]? = some old) (hpost : after[i]? = some post)
    (h : rewriteRow before after selected mapping i = true) :
    ∃ pre no yes, before[old]? = some pre ∧ selected.contains old = false ∧ pre.edge = post.edge ∧
      mapping[post.no]? = some no ∧ mapping[post.yes]? = some yes ∧
      shortcut before selected pre.no = some no ∧ shortcut before selected pre.yes = some yes := by
  simp only [rewriteRow,hmap,hpost] at h
  cases hr : before[old]? with
  | none => simp [hr] at h
  | some pre =>
    cases hn : mapping[post.no]? with
    | none => simp [hr,hn] at h
    | some no =>
      cases hy : mapping[post.yes]? with
      | none => simp [hr,hn,hy] at h
      | some yes =>
        simp only [hr,hn,hy,Bool.and_eq_true_iff,decide_eq_true_eq] at h
        have ha : selected.contains old = false := by simpa using h.1.1.1
        exact ⟨pre,no,yes,rfl,ha,h.1.1.2,rfl,rfl,h.1.2,h.2⟩

/-- At a selected, invariant-satisfying occurrence, the removed instruction
is an actual silent identity transition on the complete bank. -/
theorem selected_step (before : Array CoreRow) (masks : Array (Array Nat)) (selected : List Nat)
    (hall : selected.all (selectedZero before masks) = true) (s : CoreState)
    (hvalid : Valid before masks s) (hmem : s.index ∈ selected) :
    ∃ next, coreStep before s = (⟨next,s.fields⟩,false) ∧
      shortcut before selected s.index = some next := by
  have hzcheck := List.all_eq_true.mp hall s.index hmem
  obtain ⟨reg,no,yes,hreg,hrow,hzero⟩ := selectedZero_sound before masks s hvalid hzcheck
  have hlen := hvalid.2.1
  have hid := decrement_zero_identity s.fields reg (by omega) hzero
  have ht : GrammarControlGraph.test (.dec reg) s.fields = true := by
    simp only [GrammarControlGraph.test,hzero,decide_true]
  refine ⟨yes,?_,?_⟩
  · simp only [coreStep,hrow,Option.getD_some,ht,if_true,hid]
    rfl
  · simp [shortcut,hrow,hmem]

end Shared.PNP.Record285.GrammarCoreZero
