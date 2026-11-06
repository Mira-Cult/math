import Shared.Beeping.NPcoNP.Source284NestedBranchPre

/-! Redirect the two last return rows to distinct supplied continuation
states, preserving every write and move. The continuation must provide
states 0 and 1; a growth-loop binding is a separate composition. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284NestedBranchDispatch

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def sink (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
def base := Source284NestedBothBranches.table sink

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 30 then let r := base q b; ⟨r.write,r.turn,some 43⟩
  else if q = 41 then let r := base q b; ⟨r.write,r.turn,some 44⟩
  else if q < 43 then base q b
  else shiftRow 43 (continuation (q-43) b)

theorem finite_rows : ∀ q : Fin 43, ∀ b : Bool, (base q.val b).next.getD 43 < 43 := by decide +kernel

theorem base_closed : Closed 43 base := by
  intro q hq b q' hnext
  have h := finite_rows ⟨q,hq⟩ b
  simp [hnext] at h
  exact h

theorem row30 (b : Bool) : base 30 b = ⟨b,true,some 31⟩ := by cases b <;> rfl
theorem row41 (b : Bool) : base 41 b = ⟨b,true,some 42⟩ := by cases b <;> rfl
theorem row31 (b : Bool) : base 31 b = ⟨b,false,some 31⟩ := by cases b <;> rfl
theorem row42 (b : Bool) : base 42 b = ⟨b,false,some 42⟩ := by cases b <;> rfl

def sinkIndex (q : Nat) : Nat := if q=30 then 31 else 42

theorem sink_step (c : Config) (q : Nat) (hq : q=31 ∨ q=42) (hc : c.state=some q) :
    (step base c).state = some q := by
  cases c with
  | mk left right state =>
    simp only at hc
    subst state
    rcases hq with rfl | rfl <;> simp [step,row31,row42]

theorem sink_run (c : Config) (q : Nat) (hq : q=31 ∨ q=42) (hc : c.state=some q) (fuel : Nat) :
    (run base c fuel).state = some q := by
  induction fuel with
  | zero => exact hc
  | succ fuel ih => exact sink_step _ q hq ih

theorem terminal_step (c : Config) (q : Nat) (hq : q=30 ∨ q=41) (hc : c.state=some q) :
    (step base c).state = some (sinkIndex q) := by
  cases c with
  | mk left right state =>
    simp only at hc
    subst state
    rcases hq with rfl | rfl <;> simp [step,row30,row41,sinkIndex]

theorem avoid_before (c : Config) (limit final : Nat) (hfinal : final=30 ∨ final=41)
    (hend : (run base c limit).state = some final) :
    ∀ t < limit, ∀ q, q=30 ∨ q=41 → (run base c t).state ≠ some q := by
  intro t ht q hq hstate
  have hs : (run base c (t+1)).state = some (sinkIndex q) := by
    simp only [run]
    exact terminal_step _ q hq hstate
  have hsi : sinkIndex q=31 ∨ sinkIndex q=42 := by rcases hq with rfl | rfl <;> simp [sinkIndex]
  have h := sink_run (run base c (t+1)) (sinkIndex q) hsi hs (limit-(t+1))
  rw [← Source284PayloadPop.run_add] at h
  have he : t+1+(limit-(t+1)) = limit := by omega
  rw [he,hend] at h
  have hh : sinkIndex q=final := Option.some.inj h.symm
  rcases hq with rfl | rfl <;> rcases hfinal with rfl | rfl <;> simp [sinkIndex] at hh

theorem run_agree (continuation : Nat → Bool → Row) (c : Config) (hv : Valid 43 c) (fuel : Nat)
    (hrows : ∀ t < fuel, ∀ q, q=30 ∨ q=41 → (run base c t).state ≠ some q) :
    run (table continuation) c fuel = run base c fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    have hp : ∀ t < fuel, ∀ q, q=30 ∨ q=41 → (run base c t).state ≠ some q := by
      intro t ht q hq
      exact hrows t (by omega) q hq
    simp only [run,ih hp]
    have hvalid := valid_run 43 base c base_closed hv fuel
    cases hc : run base c fuel with
    | mk left right state =>
      cases state with
      | none => rfl
      | some q =>
        have hq : q < 43 := hvalid q (by simp [hc])
        have h30 : q ≠ 30 := by
          intro he; subst q; exact hrows fuel (by omega) 30 (Or.inl rfl) (by simp [hc])
        have h41 : q ≠ 41 := by
          intro he; subst q; exact hrows fuel (by omega) 41 (Or.inr rfl) (by simp [hc])
        simp [step,table,h30,h41,hq]

theorem redirected (continuation : Nat → Bool → Row) (mode left right : Nat) (hm : mode=0 ∨ mode=1) :
    step (table continuation) ⟨2*right,left,some (if mode=0 then 30 else 41)⟩ =
      ⟨left,2*right,some (43+mode)⟩ := by
  rcases hm with rfl | rfl <;>
    simp [step,table,row30,row41,bit,Nat.testBit_zero] <;> split_ifs <;> omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (43+q) b = shiftRow 43 (continuation q b) := by
  simp [table,show 43+q ≠ 30 by omega,show 43+q ≠ 41 by omega,show ¬ 43+q < 43 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 43 c) = shiftConfig 43 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 43 c) fuel = shiftConfig 43 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- A successful outer mark reaches continuation state 0 after exactly the
original charged computation. -/
theorem mark_then (continuation : Nat → Bool → Row) (m k : Nat) (rest : List Bool)
    (certificate stream fuel : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ false::rest) certificate),
        2*stream,some 0⟩ (4*m+4*k+14+fuel) =
    shiftConfig 43 (run continuation
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
        2*stream,some 0⟩ fuel) := by
  let c : Config := ⟨pairTape (List.replicate m false)
    (pairTape (List.replicate k true ++ false::rest) certificate),2*stream,some 0⟩
  let limit := 4*m+4*k+13
  have hv : Valid 43 c := by intro q hq; simp [c] at hq; subst q; omega
  have hp := Source284NestedBranchPre.mark_pre sink m k rest certificate stream
  change run base c limit = _ at hp
  have hf : (run base c limit).state = some 30 := by rw [hp]
  have he := run_agree continuation c hv limit (avoid_before c limit 30 (Or.inl rfl) hf)
  have ht : 4*m+4*k+14+fuel = (limit+1)+fuel := by dsimp [limit] <;> omega
  change run (table continuation) c _ = _
  rw [ht,Source284ScratchScanner.run_add,run,he,hp]
  have hs := redirected continuation 0
    (pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate)) stream (Or.inl rfl)
  simp only [ite_true,Nat.add_zero] at hs
  rw [hs]
  simpa [shiftConfig] using (relocated_run continuation
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true ++ true::rest) certificate),
      2*stream,some 0⟩ fuel)

/-- Exhaustion reaches continuation state 1, with the same tape restored. -/
theorem exhausted_then (continuation : Nat → Bool → Row) (m k certificate stream fuel : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),
        2*stream,some 0⟩ (4*m+4*k+14+fuel) =
    shiftConfig 43 (run continuation
      ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),
        2*stream,some 1⟩ fuel) := by
  let c : Config := ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),2*stream,some 0⟩
  let limit := 4*m+4*k+13
  have hv : Valid 43 c := by intro q hq; simp [c] at hq; subst q; omega
  have hp := Source284NestedBranchPre.exhausted_pre sink m k certificate stream
  change run base c limit = _ at hp
  have hf : (run base c limit).state = some 41 := by rw [hp]
  have he := run_agree continuation c hv limit (avoid_before c limit 41 (Or.inr rfl) hf)
  have ht : 4*m+4*k+14+fuel = (limit+1)+fuel := by dsimp [limit] <;> omega
  change run (table continuation) c _ = _
  rw [ht,Source284ScratchScanner.run_add,run,he,hp]
  have hs := redirected continuation 1
    (pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate)) stream (Or.inr rfl)
  simp only [show ¬ 1=0 by decide,ite_false] at hs
  rw [hs]
  simpa [shiftConfig] using (relocated_run continuation
    ⟨pairTape (List.replicate m false) (pairTape (List.replicate k true) certificate),
      2*stream,some 1⟩ fuel)

end Shared.Beeping.NPcoNP.Source284NestedBranchDispatch
