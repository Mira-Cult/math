import Shared.Beeping.NPcoNP.Source284CutoffCounter
import Shared.Beeping.NPcoNP.Source284HardwireTable
import Shared.Beeping.NPcoNP.Source284ClockStability

/-! A concrete finite source prefix for a prepared unary window. It clears
one cell per token, crosses the delimiter, then transfers control to an
arbitrary finite relative table without changing its subsequent steps. The
unary tokens and following packed input must themselves be prepared; this is
not a loader from the original raw two tape halves. -/
namespace Shared.Beeping.NPcoNP.Source284UnaryWindowLoader

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284CutoffCounter (tokens)

/-- State zero consumes one token or crosses its zero delimiter. All other
states are the supplied verifier, relocated by one logical state. -/
def table (verifier : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨false,false,some (if b then 0 else 1)⟩
  else shiftRow 1 (verifier (q-1) b)

def description (n : Nat) (verifier : Nat → Bool → Row) (tail : Nat) : Nat :=
  encode (1+n) (table verifier) tail

theorem closed (n : Nat) (verifier : Nat → Bool → Row)
    (hn : 0 < n) (hv : Closed n verifier) : Closed (1+n) (table verifier) := by
  intro q hq b q' hnext
  by_cases hz : q = 0
  · subst q
    cases b <;> simp [table] at hnext <;> subst q' <;> omega
  · have hq' : q-1 < n := by omega
    cases hnxt : (verifier (q-1) b).next with
    | none => simp [table,hz,shiftRow,hnxt] at hnext
    | some target =>
      have ha := hv (q-1) hq' b target hnxt
      simp [table,hz,shiftRow,hnxt] at hnext
      subst q'
      omega

theorem consume_step (verifier : Nat → Bool → Row) (n left tail : Nat) :
    step (table verifier) ⟨left,tokens (n+1) tail,some 0⟩ =
      ⟨2*left,tokens n tail,some 0⟩ := by
  simp [step,table,tokens,Nat.testBit_zero,bit] <;> omega

theorem finish_step (verifier : Nat → Bool → Row) (left tail : Nat) :
    step (table verifier) ⟨left,tokens 0 tail,some 0⟩ = ⟨2*left,tail,some 1⟩ := by
  simp [step,table,tokens,Nat.testBit_zero,bit]

theorem clear_tokens (verifier : Nat → Bool → Row) (n left tail : Nat) :
    run (table verifier) ⟨left,tokens n tail,some 0⟩ (n+1) =
      ⟨2^(n+1)*left,tail,some 1⟩ := by
  induction n generalizing left with
  | zero => simpa [run] using finish_step verifier left tail
  | succ n ih =>
    rw [run_front,consume_step,ih]
    congr 1
    simp [pow_succ]
    ring

theorem relocated_step (verifier : Nat → Bool → Row) (c : Config) :
    step (table verifier) (shiftConfig 1 c) = shiftConfig 1 (step verifier c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,table,show 1+q ≠ 0 by omega,
        ↓reduceIte,show 1+q-1=q by omega,shiftRow]
      split <;> rfl

theorem relocated_run (verifier : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table verifier) (shiftConfig 1 c) clock = shiftConfig 1 (run verifier c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- The real unary-record source program performs the whole clear pass in
exactly `n+1` source steps, for arbitrary data on both far tape ends. -/
theorem source_clear (states : Nat) (verifier : Nat → Bool → Row) (tail n left right : Nat)
    (hn : 0 < states) (hv : Closed states verifier) :
    Source284Relative.run (description states verifier tail)
      (Source284Relative.initial (tokens n right) left) (n+1) =
      ⟨2^(n+1)*left,right,active 1⟩ := by
  have hvalid : Valid (1+states) ⟨left,tokens n right,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    omega
  have h := run_toSource (1+states) (table verifier) tail
    ⟨left,tokens n right,some 0⟩ (closed states verifier hn hv) hvalid (n+1)
  change Source284Relative.run (description states verifier tail)
    (Source284Relative.initial (tokens n right) left) _ = _ at h
  rw [h,clear_tokens]
  rfl

/-- Relocation adds no verifier steps and preserves acceptance, even when
the two complete tape halves contain arbitrary hidden data. -/
theorem source_relocated (states : Nat) (verifier : Nat → Bool → Row) (tail left right clock : Nat)
    (hn : 0 < states) (hv : Closed states verifier) :
    ((Source284Relative.run (description states verifier tail) ⟨left,right,active 1⟩ clock).state == 0) =
      ((Source284Relative.run (encode states verifier 1) ⟨left,right,active 0⟩ clock).state == 0) := by
  have h1 : Valid (1+states) (shiftConfig 1 ⟨left,right,some 0⟩) := by
    intro q hq
    simp [shiftConfig] at hq
    subst q
    omega
  have h0 : Valid states ⟨left,right,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    exact hn
  have hr1 := run_toSource (1+states) (table verifier) tail
    (shiftConfig 1 ⟨left,right,some 0⟩) (closed states verifier hn hv) h1 clock
  have hr0 := run_toSource states verifier 1 ⟨left,right,some 0⟩ hv h0 clock
  change Source284Relative.run (description states verifier tail) ⟨left,right,active 1⟩ clock = _ at hr1
  change Source284Relative.run (encode states verifier 1) ⟨left,right,active 0⟩ clock = _ at hr0
  rw [hr1,hr0,relocated_run]
  cases h : (run verifier ⟨left,right,some 0⟩ clock).state <;>
    simp [toSource,shiftConfig,nextState,h,active]

/-- One actual finite source program pays the unary clear pass, then behaves
as the supplied finite source verifier. -/
theorem source_after_tokens (states : Nat) (verifier : Nat → Bool → Row) (tail n left right clock : Nat)
    (hn : 0 < states) (hv : Closed states verifier) :
    Source284Relative.accepts (description states verifier tail) (tokens n right) left (n+1+clock) =
      ((Source284Relative.run (encode states verifier 1) ⟨2^(n+1)*left,right,active 0⟩ clock).state == 0) := by
  unfold Source284Relative.accepts
  rw [Source284Relative.run_add_clock,source_clear states verifier tail n left right hn hv]
  exact source_relocated states verifier tail _ _ clock hn hv

namespace Fixtures

def acceptAll (_ : Nat) (b : Bool) : Row := ⟨b,false,none⟩
def rejectForever (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩

example : Source284Relative.run (description 1 acceptAll 0)
    (Source284Relative.initial (tokens 2 37) 9) 3 = ⟨72,37,active 1⟩ := by decide +kernel
example : Source284Relative.accepts (description 1 acceptAll 0) (tokens 2 37) 9 4 = true := by decide +kernel
example : Source284Relative.accepts (description 1 rejectForever 0) (tokens 0 5) 7 8 = false := by decide +kernel

end Fixtures

end Shared.Beeping.NPcoNP.Source284UnaryWindowLoader
