import Shared.Beeping.NPcoNP.Source284TableRun
import Shared.Beeping.NPcoNP.Source284FiniteRecordBounds
import Shared.Beeping.NPcoNP.Source284HardwireTable

/-! Effective finite logical-table normalization of every numeric 284-source
program. Numeric source states may be even or odd; logical state `q` denotes
source state `q+1`. This normalization preserves every step and supplies a
finite closure bound without deciding termination. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284RelativeTableDecode

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun

def states (description : Nat) : Nat := max 1 (description/4)

def table (description q : Nat) (read : Bool) : Row :=
  let a := Source284Relative.record description (q+bit read)
  ⟨decide (a%2=1),decide ((a/2)%2=1),if a/4=0 then none else some (a/4-1)⟩

def reflect (c : Source284Relative.Config) : Config :=
  ⟨c.left,c.right,if c.state=0 then none else some (c.state-1)⟩

theorem states_positive (description : Nat) : 0 < states description := by
  unfold states
  omega

theorem closed (description : Nat) : Closed (states description) (table description) := by
  intro q hq read q' hnext
  have hrecord := Source284Relative.record_le description (q+bit read)
  have hdiv : Source284Relative.record description (q+bit read)/4 ≤ description/4 :=
    Nat.div_le_div_right hrecord
  simp only [table] at hnext
  split at hnext
  · contradiction
  · rename_i hne
    simp only [Option.some.injEq] at hnext
    subst q'
    unfold states
    omega

/-- Source configurations with state zero become the logical accepting
state; every other source state is represented without identifying even and
odd source states. -/
theorem reflect_step (description : Nat) (c : Source284Relative.Config) :
    reflect (Source284Relative.step description c) = step (table description) (reflect c) := by
  rcases c with ⟨left,right,s⟩
  by_cases hs : s=0
  · subst s
    simp [Source284Relative.step,reflect,step]
  · have hbit : bit (right.testBit 0) = right%2 := Source284HardwireTable.bit_read right
    let a := Source284Relative.record description (s-1+right%2)
    have hw : bit (decide (a%2=1)) = a%2 := by
      have hm := Nat.mod_lt a (by decide : 0<2)
      by_cases h : a%2=1 <;> simp [bit,h] <;> omega
    have hq : s-1+1=s := by omega
    simp only [Source284Relative.step,hs,↓reduceIte,reflect,step,table,if_neg hs]
    rw [hbit]
    have hw' : bit (decide (Source284Relative.record description (s-1+right%2)%2=1)) =
        Source284Relative.record description (s-1+right%2)%2 := hw
    by_cases ht : (Source284Relative.record description (s-1+right%2)/2)%2=1 <;> simp [ht,hw']

theorem reflect_run (description : Nat) (c : Source284Relative.Config) (clock : Nat) :
    reflect (Source284Relative.run description c clock) = run (table description) (reflect c) clock := by
  induction clock with
  | zero => rfl
  | succ clock ih =>
    simp only [Source284Relative.run_succ,run,← ih]
    exact reflect_step description _

theorem reflected_acceptance (description input certificate clock : Nat) :
    Source284Relative.accepts description input certificate clock =
      (run (table description) ⟨certificate,input,some 0⟩ clock).state.isNone := by
  have h := reflect_run description (Source284Relative.initial input certificate) clock
  have hi : reflect (Source284Relative.initial input certificate) = ⟨certificate,input,some 0⟩ := by
    rfl
  rw [hi] at h
  unfold Source284Relative.accepts
  rw [← h]
  dsimp [reflect]
  split <;> simp_all

end Shared.Beeping.NPcoNP.Source284RelativeTableDecode
