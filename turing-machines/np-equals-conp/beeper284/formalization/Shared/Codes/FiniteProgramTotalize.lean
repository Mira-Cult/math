import Shared.ComplexityBridge.CircuitProgramMove

/-! A finite continuing-program totalization. It represents false, true and
invalid outcomes by separate absorbing states. These states still take a
concrete transition at every step; their tape contents are observationally
irrelevant. This is not yet a polynomial bit-cost construction proof. -/
namespace Shared.Codes.FiniteProgramTotalize
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CircuitProgramMove
open Shared.ComplexityBridge.CircuitTable

/-- Invalid, false-result and true-result states, in that order. -/
def invalidState (p : Program) : Nat := p.length
def falseState (p : Program) : Nat := p.length+1
def trueState (p : Program) : Nat := p.length+2

def sinkRow (q : Nat) : Row := (false,true,q,0)

def liftRow (m : Nat) (row : Row) : Row :=
  match row.2.2.2 with
  | 0 => (row.1,row.2.1,if row.2.2.1 < m then row.2.2.1 else m,0)
  | 1 => sinkRow (m+1)
  | 2 => sinkRow (m+2)
  | _ => sinkRow m

def liftPair (m : Nat) (rows : Row × Row) : Row × Row :=
  (liftRow m rows.1,liftRow m rows.2)

def totalProgram (p : Program) : Program :=
  p.map (liftPair p.length) ++
    [(sinkRow (invalidState p),sinkRow (invalidState p)),
     (sinkRow (falseState p),sinkRow (falseState p)),
     (sinkRow (trueState p),sinkRow (trueState p))]

def embed (p : Program) (c : Config) : Config :=
  (if c.1 < p.length then c.1 else invalidState p,c.2)

theorem totalProgram_length (p : Program) : (totalProgram p).length = p.length+3 := by
  simp [totalProgram]

theorem totalProgram_original (p : Program) (q : Nat) (pair : Row × Row)
    (hp : p[q]? = some pair) : (totalProgram p)[q]? = some (liftPair p.length pair) := by
  have hq : q < p.length := (List.getElem?_eq_some_iff.mp hp).1
  have he : p[q] = pair := (List.getElem?_eq_some_iff.mp hp).2
  simp [totalProgram,List.getElem?_append_left,hq,he]

theorem totalProgram_invalid (p : Program) :
    (totalProgram p)[invalidState p]? = some (sinkRow (invalidState p),sinkRow (invalidState p)) := by
  simp [totalProgram,invalidState,List.getElem?_append_right]

theorem totalProgram_false (p : Program) :
    (totalProgram p)[falseState p]? = some (sinkRow (falseState p),sinkRow (falseState p)) := by
  simp [totalProgram,falseState,invalidState,List.getElem?_append_right]

theorem totalProgram_true (p : Program) :
    (totalProgram p)[trueState p]? = some (sinkRow (trueState p),sinkRow (trueState p)) := by
  simp [totalProgram,trueState,falseState,invalidState,List.getElem?_append_right]

theorem sink_step (p : Program) (q : Nat) (t : Tape)
    (h : (totalProgram p)[q]? = some (sinkRow q,sinkRow q)) :
    step (totalProgram p) (q,t) = some (.inr (q,moveTape false false t)) := by
  simp [step,h,sinkRow]

theorem step_invalid (p : Program) (t : Tape) :
    step (totalProgram p) (invalidState p,t) = some (.inr (invalidState p,moveTape false false t)) :=
  sink_step p _ t (totalProgram_invalid p)

theorem step_false (p : Program) (t : Tape) :
    step (totalProgram p) (falseState p,t) = some (.inr (falseState p,moveTape false false t)) :=
  sink_step p _ t (totalProgram_false p)

theorem step_true (p : Program) (t : Tape) :
    step (totalProgram p) (trueState p,t) = some (.inr (trueState p,moveTape false false t)) :=
  sink_step p _ t (totalProgram_true p)

/-- On a live original state, both tables select corresponding rows. -/
theorem rowAt_total (p : Program) (c : Config) (row : Row)
    (h : rowAt p c = some row) : rowAt (totalProgram p) c = some (liftRow p.length row) := by
  cases hp : p[c.1]? with
  | none => simp [rowAt,hp] at h
  | some pair =>
    have hh := totalProgram_original p c.1 pair hp
    have hr : (if c.2.2.1 then pair.2 else pair.1) = row := by simpa [rowAt,hp] using h
    simp [rowAt,hh,liftPair,←hr]
    cases c.2.2.1 <;> rfl

/-- Simulation relation, treating an out-of-range live state as invalid for
future steps and keeping the tape equal while the original state is valid. -/
def Related (p : Program) (s : Status) (c : Config) : Prop :=
  match s with
  | none => c.1 = invalidState p
  | some (.inl b) => c.1 = if b then trueState p else falseState p
  | some (.inr d) => if d.1 < p.length then c = d else c.1 = invalidState p

theorem related_initial (p : Program) (c : Config) : Related p (some (.inr c)) (embed p c) := by
  by_cases h : c.1 < p.length
  · simp [Related,embed,h]
  · simp [Related,embed,h]

/-- Each original status transition is matched by one continuing concrete
transition in the totalized table. -/
theorem related_step (p : Program) (s : Status) (c : Config) (h : Related p s c) :
    ∃ d, step (totalProgram p) c = some (.inr d) ∧ Related p (advance p s) d := by
  cases s with
  | none =>
    have hc : c.1 = invalidState p := h
    rcases c with ⟨q,t⟩
    simp only at hc
    subst q
    refine ⟨(invalidState p,moveTape false false t),step_invalid p t,?_⟩
    rfl
  | some result =>
    cases result with
    | inl b =>
      cases b with
      | false =>
        have hc : c.1 = falseState p := h
        rcases c with ⟨q,t⟩
        simp only at hc
        subst q
        exact ⟨(falseState p,moveTape false false t),step_false p t, rfl⟩
      | true =>
        have hc : c.1 = trueState p := h
        rcases c with ⟨q,t⟩
        simp only at hc
        subst q
        exact ⟨(trueState p,moveTape false false t),step_true p t, rfl⟩
    | inr old =>
      by_cases hq : old.1 < p.length
      · have heq : c = old := by simpa [Related,hq] using h
        subst c
        have hp : p[old.1]? = some p[old.1] := List.getElem?_eq_getElem hq
        let row : Row := if old.2.2.1 then p[old.1].2 else p[old.1].1
        have hrow : rowAt p old = some row := by simp [rowAt,hp,row]
        have htarget := rowAt_total p old row hrow
        have hs := step_eq_executeRow p old row hrow
        have ht := step_eq_executeRow (totalProgram p) old (liftRow p.length row) htarget
        simp only [advance]
        rw [hs,ht]
        rcases row with ⟨w,dir,next,tag⟩
        cases tag with
        | zero =>
          by_cases hnext : next < p.length
          · refine ⟨(next,moveTape (!dir) w old.2),?_,?_⟩
            · simp [executeRow,liftRow,hnext]
            · simp [advance,executeRow,Related,hnext]
          · refine ⟨(invalidState p,moveTape (!dir) w old.2),?_,?_⟩
            · simp [executeRow,liftRow,hnext,invalidState]
            · simp [advance,executeRow,Related,hnext,invalidState]
        | succ tag =>
          cases tag with
          | zero =>
            refine ⟨(falseState p,moveTape false false old.2),?_,?_⟩
            · simp [executeRow,liftRow,sinkRow,falseState]
            · simp [advance,executeRow,Related,falseState]
          | succ tag =>
            cases tag with
            | zero =>
              refine ⟨(trueState p,moveTape false false old.2),?_,?_⟩
              · simp [executeRow,liftRow,sinkRow,trueState]
              · simp [advance,executeRow,Related,trueState]
            | succ tag =>
              refine ⟨(invalidState p,moveTape false false old.2),?_,?_⟩
              · simp [executeRow,liftRow,sinkRow,invalidState]
              · simp [advance,executeRow,Related,invalidState]
      · have hc : c.1 = invalidState p := by simpa [Related,hq] using h
        have hp : p[old.1]? = none := List.getElem?_eq_none (by omega)
        rcases c with ⟨q,t⟩
        simp only at hc
        subst q
        refine ⟨(invalidState p,moveTape false false t),step_invalid p t,?_⟩
        simp [advance,step,hp,Related]

/-- The true sink is reached exactly for a true result; live, false and
invalid statuses are distinct, including out-of-range live states. -/
theorem related_true_iff (p : Program) (s : Status) (c : Config) (h : Related p s c) :
    s = some (.inl true) ↔ c.1 = trueState p := by
  cases s with
  | none =>
    have hc : c.1 = invalidState p := h
    simp [hc,invalidState,trueState]
  | some result =>
    cases result with
    | inl b =>
      cases b with
      | false =>
        have hc : c.1 = falseState p := h
        simp [hc,falseState,trueState]
      | true =>
        have hc : c.1 = trueState p := h
        simp [hc]
    | inr d =>
      by_cases hd : d.1 < p.length
      · have hc : c = d := by simpa [Related,hd] using h
        subst c
        have hne : d.1 ≠ trueState p := by simp only [trueState]; omega
        simp [hne]
      · have hc : c.1 = invalidState p := by simpa [Related,hd] using h
        simp [hc,invalidState,trueState]

/-- Every finite original run has a same-length, always-continuing
simulation, related at its final status. -/
theorem run_totalized (p : Program) (c : Config) (n : Nat) :
    ∃ d, run (totalProgram p) (embed p c) n = some (.inr d) ∧ Related p (run p c n) d := by
  induction n with
  | zero => exact ⟨embed p c,rfl,related_initial p c⟩
  | succ n ih =>
    obtain ⟨d,hd,hr⟩ := ih
    obtain ⟨d',hs,hr'⟩ := related_step p (run p c n) d hr
    refine ⟨d',?_,?_⟩
    · simp only [run_succ,hd,advance,hs]
    · simpa only [run_succ] using hr'

theorem run_true_iff_totalized (p : Program) (c : Config) (n : Nat) :
    ∃ d, run (totalProgram p) (embed p c) n = some (.inr d) ∧
      (run p c n = some (.inl true) ↔ d.1 = trueState p) := by
  obtain ⟨d,hd,hr⟩ := run_totalized p c n
  exact ⟨d,hd,related_true_iff p (run p c n) d hr⟩

theorem bounded_true_iff_run (p : Program) (input : List Bool) (n : Nat) :
    bounded p input n = some true ↔ run p (initial input) n = some (.inl true) := by
  unfold bounded
  cases h : run p (initial input) n with
  | none => simp [h]
  | some x => cases x <;> simp [h]

theorem bounded_true_iff_totalized (p : Program) (input : List Bool) (n : Nat) :
    ∃ d, run (totalProgram p) (embed p (initial input)) n = some (.inr d) ∧
      (bounded p input n = some true ↔ d.1 = trueState p) := by
  obtain ⟨d,hd,he⟩ := run_true_iff_totalized p (initial input) n
  exact ⟨d,hd,(bounded_true_iff_run p input n).trans he⟩

namespace Fixtures
def accept : Program := [((false,false,0,2),(false,false,0,2))]
def reject : Program := [((false,false,0,1),(false,false,0,1))]
def invalid : Program := [((false,false,0,9),(false,false,0,9))]
def badNext : Program := [((false,true,4,0),(false,true,4,0))]
def start : Config := (0,[],false,[])
example : run (totalProgram accept) (embed accept start) 0 = some (.inr (0,[],false,[])) := by decide
example : (run (totalProgram accept) (embed accept start) 2).map (fun x => x.map id Prod.fst) = some (.inr (trueState accept)) := by decide
example : (run (totalProgram reject) (embed reject start) 2).map (fun x => x.map id Prod.fst) = some (.inr (falseState reject)) := by decide
example : (run (totalProgram invalid) (embed invalid start) 2).map (fun x => x.map id Prod.fst) = some (.inr (invalidState invalid)) := by decide
example : (run (totalProgram badNext) (embed badNext start) 2).map (fun x => x.map id Prod.fst) = some (.inr (invalidState badNext)) := by decide
example : (run (totalProgram []) (embed [] start) 2).map (fun x => x.map id Prod.fst) = some (.inr (invalidState [])) := by decide
end Fixtures

end Shared.Codes.FiniteProgramTotalize
