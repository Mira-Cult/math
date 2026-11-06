import Shared.Beeping.NPcoNP.Source284JoinedRawEncodeTM2

/-! A halting variant of the joined-prefix encoder. The original encoder is
unchanged; this variant replaces its absorbing `done` statement by `halt`.
Only exact joined inputs (without a retained suffix) have empty input stacks
and hence satisfy the standard TM2 `haltList` convention. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284JoinedHaltingEncoder

open Turing.TM2 Shared.ComplexityBridge.TM2Symbols Shared.Codes.TM2Program
open Shared.ComplexityBridge.TM2ListCodec (Stack stackVals)
open Shared.Beeping.NPcoNP.Source284JoinedFrames
open Source284JoinedRawEncodeTM2

def haltProgram : Label → Stmt (fun _ : Stack => Bool) Label (Option Bool)
  | .done => .halt
  | l => program l

def machine : Turing.FinTM2 := { Source284JoinedRawEncodeTM2.machine with m := haltProgram }

theorem step_agrees (c : machine.Cfg) (h : c.l ≠ some .done) :
    machine.step c = Source284JoinedRawEncodeTM2.machine.step c := by
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l =>
    cases l <;> first | rfl | exact False.elim (h rfl)

theorem old_done_fixed (c : machine.Cfg) (h : c.l = some .done) :
    Source284JoinedRawEncodeTM2.machine.step c = some c := by
  rcases c with ⟨l,v,S⟩
  simp only at h
  subst l
  rfl

theorem old_done_run (c : machine.Cfg) (h : c.l = some .done) (n : Nat) :
    runSteps Source284JoinedRawEncodeTM2.machine.step n c = some c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runSteps_front,old_done_fixed c h]; exact ih

theorem done_halts (out : List Bool) :
    machine.step (cfg .done none [] [] out) = some (Turing.haltList machine out) := by
  change some (Cfg.mk _ _ _) = some (Cfg.mk _ _ _)
  congr 2; funext k; cases k <;>
    simp [machine,Source284JoinedRawEncodeTM2.machine,stackVals,Turing.haltList]

/-- Replacing the absorbing done statement by halt preserves the output and
reaches the standard halt configuration within one additional block. -/
theorem halt_of_old_done (n : Nat) (c : machine.Cfg) (out : List Bool)
    (h : runSteps Source284JoinedRawEncodeTM2.machine.step n c =
      some (cfg .done none [] [] out)) :
    ∃ k ≤ n+1, runSteps machine.step k c = some (Turing.haltList machine out) := by
  induction n generalizing c with
  | zero =>
    have hc : c = cfg .done none [] [] out := Option.some.inj h
    subst c
    exact ⟨1,by omega,by simpa [runSteps] using done_halts out⟩
  | succ n ih =>
    by_cases hd : c.l = some .done
    · have hc : c = cfg .done none [] [] out := Option.some.inj ((old_done_run c hd (n+1)).symm.trans h)
      subst c
      exact ⟨1,by omega,by simpa [runSteps] using done_halts out⟩
    · rw [runSteps_front] at h
      cases hs : Source284JoinedRawEncodeTM2.machine.step c with
      | none =>
        change (Source284JoinedRawEncodeTM2.machine.step c).bind _ = _ at h
        rw [hs] at h
        contradiction
      | some c' =>
        simp only [hs,Option.bind_some] at h
        obtain ⟨k,hk,hr⟩ := ih c' h
        refine ⟨k+1,by omega,?_⟩
        rw [runSteps_front,step_agrees c hd,hs]
        exact hr

theorem encode_joined_halts (x w : List Bool) :
    ∃ n ≤ 2*(joinedBits x w).length+2,
      runSteps machine.step n (Turing.initList machine (joinedBits x w)) =
        some (Turing.haltList machine (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool)))) := by
  have h := Source284JoinedRawEncodeTM2.encode_joined x w []
  simp only [List.append_nil] at h
  simpa using halt_of_old_done (2*(joinedBits x w).length+1)
    (Turing.initList machine (joinedBits x w))
    (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))) h

namespace Fixtures
example : ∃ n ≤ 14, runSteps machine.step n (Turing.initList machine (joinedBits [] [])) =
    some (Turing.haltList machine (BitstringEncoding.bitEncode (joinedBits [] [],([] : List Bool)))) := by
  simpa [joined_length] using encode_joined_halts [] []

example : ∃ n ≤ 30,
    runSteps machine.step n (Turing.initList machine (joinedBits [false,true] [true,false])) =
      some (Turing.haltList machine
        (BitstringEncoding.bitEncode (joinedBits [false,true] [true,false],([] : List Bool)))) := by
  simpa [joined_length] using encode_joined_halts [false,true] [true,false]
end Fixtures

end Shared.Beeping.NPcoNP.Source284JoinedHaltingEncoder
