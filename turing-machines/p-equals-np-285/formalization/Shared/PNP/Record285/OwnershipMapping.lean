import Shared.PNP.Record285.OwnershipMoveLoop

/-! Soundness of finite ownership-to-class control correspondence. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarCoreGraph

def LocalMatch (physical : Array CoreRow) (classes mask : Array Nat)
    (row : Row) (pc : Nat) (target : CoreRow) (no yes : Nat) : Prop :=
  target.edge = targetEdge classes row.action ∧
  match row.action with
  | .inc i | .dec i | .half i =>
    peerZero classes mask i = true ∧ target.no = no ∧ target.yes = yes
  | .beep => target.no = no ∧ target.yes = yes
  | .move src dst =>
    ∃ body, physical[target.no]? = some body ∧ peerZero classes mask src = true ∧
      peerZero classes mask dst = true ∧ classAt classes src ≠ classAt classes dst ∧
      body.edge = .inc (classAt classes dst) ∧ body.no = pc ∧ body.yes = pc ∧
      target.yes = no ∧ row.no = row.yes

theorem mappingRow_sound (logical : Array Row) (physical : Array CoreRow) (masks : Array (Array Nat))
    (classes mapping : Array Nat) (i pc : Nat) (row : Row) (mask : Array Nat)
    (hr : logical[i]? = some row) (hm : masks[i]? = some mask) (hp : mapping[i]? = some pc)
    (h : mappingRow logical physical masks classes mapping i = true) :
    ∃ target no yes, physical[pc]? = some target ∧ mapping[row.no]? = some no ∧
      mapping[row.yes]? = some yes ∧ LocalMatch physical classes mask row pc target no yes := by
  simp only [mappingRow,hr,hm,hp] at h
  cases ht : physical[pc]? with
  | none => simp [ht] at h
  | some target =>
    cases hn : mapping[row.no]? with
    | none => simp [ht,hn] at h
    | some no =>
      cases hy : mapping[row.yes]? with
      | none => simp [ht,hn,hy] at h
      | some yes =>
        refine ⟨target,no,yes,rfl,rfl,rfl,?_⟩
        cases row with
        | mk action rno ryes =>
          cases action with
          | inc reg =>
            simpa [ht,hn,hy,LocalMatch,Bool.and_eq_true_iff,and_assoc] using h
          | dec reg =>
            simpa [ht,hn,hy,LocalMatch,Bool.and_eq_true_iff,and_assoc] using h
          | half reg =>
            simpa [ht,hn,hy,LocalMatch,Bool.and_eq_true_iff,and_assoc] using h
          | beep =>
            simpa [ht,hn,hy,LocalMatch,Bool.and_eq_true_iff] using h
          | move src dst =>
            cases hb : physical[target.no]? with
            | none => simp [ht,hn,hy,hb] at h
            | some body =>
              simp only [ht,hn,hy,hb,Bool.and_eq_true_iff,decide_eq_true_eq] at h
              refine ⟨h.1.1.1.1,body,hb,h.1.1.1.2,h.1.1.2,h.1.2,?_⟩
              exact h.2

end Shared.PNP.Record285.OwnershipCore
