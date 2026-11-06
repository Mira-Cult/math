import Shared.Beeping.MarkedTM1Post

/-! Finite reachable-state support for the event-marked TM1-to-post
interpreter. Enumeration uses mathlib's noncomputable statement support. -/
namespace Shared.Beeping.MarkedTM1Support
open Turing
open Shared.Beeping.MarkedTM1Post

noncomputable def support (M : L → S) (labels : Finset L) : Finset Phase := by
  classical
  exact ((labels ×ˢ Finset.univ).image fun p : L × V => Phase.entry p.1 p.2) ∪
    ((TM1.stmts M labels ×ˢ Finset.univ).image fun p : Option S × V =>
      match p.1 with | some s => Phase.inside s p.2 | none => Phase.stopped p.2)

theorem entry_mem (M : L → S) (labels : Finset L) (q : L) (v : V) (h : q ∈ labels) :
    Phase.entry q v ∈ support M labels := by
  classical
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨(q,v),by simp [h],rfl⟩

theorem inside_mem (M : L → S) (labels : Finset L) (s : S) (v : V)
    (h : some s ∈ TM1.stmts M labels) : Phase.inside s v ∈ support M labels := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨(some s,v),by simp [h],rfl⟩

theorem stopped_mem (M : L → S) (labels : Finset L) (v : V) : Phase.stopped v ∈ support M labels := by
  classical
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  exact ⟨(none,v),by simp [TM1.stmts],rfl⟩

theorem entry_only (M : L → S) (labels : Finset L) (q : L) (v : V)
    (h : Phase.entry q v ∈ support M labels) : q ∈ labels := by
  classical
  simp [support] at h
  rcases h with h | ⟨a,ha,w,he⟩
  · exact h
  · cases a <;> simp at he

theorem inside_only (M : L → S) (labels : Finset L) (s : S) (v : V)
    (h : Phase.inside s v ∈ support M labels) : some s ∈ TM1.stmts M labels := by
  classical
  simp [support] at h
  obtain ⟨a,ha,w,he⟩ := h
  cases a with
  | none => simp at he
  | some t =>
    simp only [Phase.inside.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    exact ha

theorem execute_supported (M : L → S) (labels : Finset L) (s : S)
    (hs : some s ∈ TM1.stmts M labels) (hlabel : TM1.SupportsStmt labels s)
    (a : A) (v : V) : (execute s a v).1 ∈ support M labels := by
  classical
  induction s generalizing v with
  | move dir s ih =>
    apply inside_mem
    apply TM1.stmts_trans _ hs
    simp [TM1.stmts₁,TM1.stmts₁_self]
  | write f s ih =>
    apply inside_mem
    apply TM1.stmts_trans _ hs
    simp [TM1.stmts₁,TM1.stmts₁_self]
  | load f s ih =>
    apply ih
    · apply TM1.stmts_trans _ hs
      simp [TM1.stmts₁,TM1.stmts₁_self]
    · exact hlabel
  | branch f s t ihs iht =>
    cases hf : f a v with
    | false =>
      simp only [execute,hf,Bool.false_eq_true,↓reduceIte]
      apply iht
      · apply TM1.stmts_trans _ hs
        simp [TM1.stmts₁,TM1.stmts₁_self]
      · exact hlabel.2
    | true =>
      simp only [execute,hf,↓reduceIte]
      apply ihs
      · apply TM1.stmts_trans _ hs
        simp [TM1.stmts₁,TM1.stmts₁_self]
      · exact hlabel.1
  | goto f => exact entry_mem M labels (f a v) v (hlabel a v)
  | halt => exact stopped_mem M labels v

theorem table_support (M : L → S) (labels : Finset L) (h : TM1.Supports M labels) :
    TM0.Supports (table M) (support M labels : Set Phase) := by
  classical
  constructor
  · change Phase.entry default none ∈ support M labels
    exact entry_mem M labels default none h.1
  · intro q a q' op hrow hq
    cases q with
    | entry q v =>
      have hq' := entry_only M labels q v hq
      have hs : some (M q) ∈ TM1.stmts M labels := by
        simp only [TM1.stmts,Finset.mem_insertNone,Option.mem_def,Option.some.injEq,
          forall_eq',Finset.mem_biUnion]
        exact ⟨q,hq',TM1.stmts₁_self⟩
      have hd := execute_supported M labels (M q) hs (h.2 q hq') a v
      change some (execute (M q) a v) = some (q',op) at hrow
      have he := Option.some.inj hrow
      rw [he] at hd
      exact hd
    | inside s v =>
      have hs := inside_only M labels s v hq
      have hd := execute_supported M labels s hs (TM1.stmts_supportsStmt h hs) a v
      change some (execute s a v) = some (q',op) at hrow
      have he := Option.some.inj hrow
      rw [he] at hd
      exact hd
    | stopped v =>
      change some (Phase.stopped v,TM0.Stmt.write a) = some (q',op) at hrow
      have he := Option.some.inj hrow
      cases he
      exact stopped_mem M labels v

end Shared.Beeping.MarkedTM1Support
