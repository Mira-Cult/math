import Shared.Codes.FiniteProgramTaggedLoop
import Shared.Codes.FiniteProgramRestartTwo

/-! A charged finite-table loop for moving a tagged buffer left across cells
whose contents have already been consumed. The current bit is erased, not
appended: callers must establish that it is safe to discard. -/
namespace Shared.Codes.FiniteProgramTaggedSkip
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramTaggedLoop (canonical tapeAt_append_blank)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def stop : Row × Row := ((false,true,0,1),(true,true,0,1))
def base : Program := Shared.Codes.FiniteProgramTaggedAdvance.program [stop]
def program : Program := Shared.Codes.FiniteProgramRestartTwo.program base 14 14

@[simp] theorem base_length : base.length = 15 := by decide
@[simp] theorem program_length : program.length = 17 := by simp [program]
theorem base_valid : valid base = true := by decide
theorem program_valid : valid program = true :=
  Shared.Codes.FiniteProgramRestartTwo.program_valid base 14 14 base_valid

theorem base_stop (t : Tape) : step base (14,t) = some (.inl false) := by
  cases h : t.2.1 <;> simp [step,base,Shared.Codes.FiniteProgramTaggedAdvance.program,stop,h]

/-- One cycle costs `10 * xs.length + 7` physical transitions. The
buffer `xs` is unchanged, while the current cell is erased. -/
theorem cycle (b p : Bool) (xs L : List Bool) :
    run program (canonical (p::L) b xs) (10*xs.length+7) =
      some (.inr (0,Shared.Codes.FiniteProgramThreeExit.bounce
        (tapeAt L (p::false::tagged xs ++ [false,false,false,false])))) := by
  have hf := Shared.Codes.FiniteProgramTaggedAdvance.advance [stop] b p xs L [false,false]
  change run base (canonical (p::L) b xs) (10*xs.length+5) =
    some (.inr (14,tapeAt L (p::false::tagged xs ++ [false,false,false,false]))) at hf
  have hs : ∃ r, ∀ t, step base (14,t) = some (.inl r) := ⟨false,base_stop⟩
  have hp := Shared.Codes.FiniteProgramRestartTwo.first_entry base 14 14 _ _ _ base_valid
    (by simp [canonical]) hs hs hf
  change run program (canonical (p::L) b xs) (10*xs.length+5) = _ at hp
  rw [show 10*xs.length+7 = (10*xs.length+5)+2 by omega,
    run_continue _ _ _ _ _ hp]
  exact Shared.Codes.FiniteProgramRestartTwo.restart_second base 14 14 (by simp) _

/-- The consumed bit is irrecoverably erased by this pass. A compactor must
save or otherwise account for it before entering the skip loop. -/
theorem erased_head (p : Bool) (xs L : List Bool) :
    run program (canonical (p::L) false xs) (10*xs.length+7) =
      run program (canonical (p::L) true xs) (10*xs.length+7) := by
  rw [cycle false p xs L,cycle true p xs L]

/-- The cycle also works on tapes equal modulo trailing blanks. -/
theorem cycle_related (b p : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (p::L) b xs).2) :
    ∃ d, run program c (10*xs.length+7) = some (.inr d) ∧
      d.1 = 0 ∧ TapeRel d.2 (canonical L p xs).2 := by
  have h := run_related program c (canonical (p::L) b xs) (by simpa [canonical] using hq) ht
    (10*xs.length+7)
  rw [cycle b p xs L] at h
  cases hs : run program c (10*xs.length+7) with
  | none => rw [hs] at h; exact False.elim h
  | some v => cases v with
    | inl out => rw [hs] at h; exact False.elim h
    | inr d =>
      have hd : d.1 = 0 ∧ TapeRel d.2 (Shared.Codes.FiniteProgramThreeExit.bounce
          (tapeAt L (p::false::tagged xs ++ [false,false,false,false]))) := by
        simpa only [hs,StatusRel] using h
      refine ⟨d,rfl,hd.1,?_⟩
      apply Eq.trans hd.2
      apply Eq.trans (Shared.Codes.FiniteProgramThreeExit.bounce_related _)
      have hb := tapeAt_append_blank L (false::tagged xs ++ [false,false,false]) p
      change TapeRel (tapeAt L (p::false::tagged xs ++ [false,false,false,false]))
        (canonical L p xs).2
      simpa [canonical,List.append_assoc,TapeRel] using hb.symm

/-- The predecessor bits are listed nearest first; the last becomes the
head after all preceding cells have been discarded. -/
def finalHead : List Bool → Bool → Bool
  | [], b => b
  | p::ps, _ => finalHead ps p

/-- Any finite number of discarded cells is traversed by the same finite
table. The tagged buffer is unchanged and the cost is exact. -/
theorem skips (remaining : List Bool) (b : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (remaining++L) b xs).2) :
    ∃ d, run program c (remaining.length*(10*xs.length+7)) = some (.inr d) ∧
      d.1 = 0 ∧ TapeRel d.2 (canonical L (finalHead remaining b) xs).2 := by
  induction remaining generalizing b c with
  | nil =>
    refine ⟨c,?_,hq,?_⟩
    · simp
    · simpa [finalHead] using ht
  | cons p ps ih =>
    have ht' : TapeRel c.2 (canonical (p::(ps++L)) b xs).2 := by simpa using ht
    obtain ⟨d,hd,hq',htape⟩ := cycle_related b p xs (ps++L) c hq ht'
    obtain ⟨last,hlast,hqlast,htlast⟩ := ih p d hq' htape
    refine ⟨last,?_,hqlast,?_⟩
    · rw [show (p::ps).length*(10*xs.length+7) =
          (10*xs.length+7)+ps.length*(10*xs.length+7) by simp [Nat.add_mul,Nat.add_comm],
        run_continue _ _ _ _ _ hd]
      exact hlast
    · simpa [finalHead] using htlast

end Shared.Codes.FiniteProgramTaggedSkip
