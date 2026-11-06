import Shared.Codes.FiniteProgramProtectedScan
import Shared.Codes.FiniteProgramRestartTwo

/-! Repeat the protected-block scanner until its retained marker is true.
Every unmarked block takes a positive scan and two restart transitions; the
marked block is reached after finitely many steps. No bit is emitted or
compacted by this table. -/
namespace Shared.Codes.FiniteProgramProtectedScanLoop
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTwoWordClassify (mask)
open Shared.Codes.FiniteProgramProtectedScan (state)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def terminal (width : Nat) (b marked : Bool) : Nat := state (width+3) (mask b marked)
def program (width : Nat) : Program :=
  Shared.Codes.FiniteProgramRestartTwo.program (Shared.Codes.FiniteProgramProtectedScan.program width)
    (terminal width false false) (terminal width true false)

def block (b : Bool) (payload : List Bool) (marked : Bool) : List Bool :=
  b::(payload ++ [marked,true])

def blocks (xs : List (Bool × List Bool)) : List Bool :=
  xs.flatMap (fun x => block x.1 x.2 false)

@[simp] theorem program_length (width : Nat) : (program width).length = 4*(width+4)+2 := by
  simp [program,Shared.Codes.FiniteProgramProtectedScan.program_length]

theorem program_valid (width : Nat) : valid (program width) = true :=
  Shared.Codes.FiniteProgramRestartTwo.program_valid _ _ _
    (Shared.Codes.FiniteProgramProtectedScan.program_valid width)

theorem terminal_bound (width : Nat) (b marked : Bool) :
    terminal width b marked < (Shared.Codes.FiniteProgramProtectedScan.program width).length :=
  Shared.Codes.FiniteProgramProtectedScan.state_bound width (width+3) _ (by omega)

theorem unmarked_distinct (width : Nat) : terminal width false false ≠ terminal width true false := by
  simp [terminal,state,mask]

theorem marked_distinct (width : Nat) (b : Bool) :
    terminal width b true ≠ terminal width false false ∧ terminal width b true ≠ terminal width true false := by
  cases b <;> simp [terminal,state,mask]

/-- The underlying scan is retained until it first reaches a terminal row. -/
theorem scan_block (width : Nat) (b marked : Bool) (payload L R : List Bool)
    (hlen : payload.length = width) :
    run (program width) (0,tapeLeft (block b payload marked ++ L) R) (width+3) =
      some (.inr (terminal width b marked,tapeLeft L (true::marked::(payload.reverse ++ b::R)))) := by
  let p := Shared.Codes.FiniteProgramProtectedScan.program width
  let a := terminal width false false
  let d := terminal width true false
  have ha : ∃ r, ∀ t, step p (a,t) = some (.inl r) :=
    ⟨false,fun t => Shared.Codes.FiniteProgramProtectedScan.terminal_placeholder width (mask false false) t⟩
  have hd : ∃ r, ∀ t, step p (d,t) = some (.inl r) :=
    ⟨false,fun t => Shared.Codes.FiniteProgramProtectedScan.terminal_placeholder width (mask true false) t⟩
  have hr : run p (0,tapeLeft (block b payload marked ++ L) R) (width+3) =
      some (.inr (terminal width b marked,tapeLeft L (true::marked::(payload.reverse ++ b::R)))) := by
    simpa [p,block,terminal] using Shared.Codes.FiniteProgramProtectedScan.scan_block width b marked payload L R hlen
  change run (Shared.Codes.FiniteProgramRestartTwo.program p a d) _ _ = _
  apply Shared.Codes.FiniteProgramRestartTwo.first_entry p a d _ _ _
    (Shared.Codes.FiniteProgramProtectedScan.program_valid width) (by simp [p]) ha hd hr

/-- Marked exits remain terminal placeholders, rather than restarting. -/
theorem marked_placeholder (width : Nat) (b : Bool) (t : Tape) :
    step (program width) (terminal width b true,t) = some (.inl false) := by
  let p := Shared.Codes.FiniteProgramProtectedScan.program width
  let a := terminal width false false
  let d := terminal width true false
  have hne := marked_distinct width b
  have h := Shared.Codes.FiniteProgramRestartTwo.source_other p a d (terminal width b true,t)
    (terminal_bound width b true) hne.1 hne.2
  change step p (terminal width b true,t) = step (program width) (terminal width b true,t) at h
  rw [← h]
  exact Shared.Codes.FiniteProgramProtectedScan.terminal_placeholder width (mask b true) t

/-- An unmarked block is scanned and restarted with no tape change except for
moving the head left by its width. -/
theorem cycle (width : Nat) (b : Bool) (payload L R : List Bool) (hlen : payload.length = width) :
    run (program width) (0,tapeLeft (block b payload false ++ L) R) (width+5) =
      some (.inr (0,Shared.Codes.FiniteProgramThreeExit.bounce
        (tapeLeft L (true::false::(payload.reverse ++ b::R))))) := by
  let p := Shared.Codes.FiniteProgramProtectedScan.program width
  let a := terminal width false false
  let d := terminal width true false
  let after := tapeLeft L (true::false::(payload.reverse ++ b::R))
  have hscan := scan_block width b false payload L R hlen
  rw [show width+5 = (width+3)+2 by omega,run_continue _ _ _ _ _ hscan]
  cases b with
  | false =>
    exact Shared.Codes.FiniteProgramRestartTwo.restart_first p a d (terminal_bound width false false)
      (unmarked_distinct width) after
  | true =>
    exact Shared.Codes.FiniteProgramRestartTwo.restart_second p a d (terminal_bound width true false) after

/-- A scan on a blank-equivalent physical tape reaches the same marked or
unmarked state and a blank-equivalent tape. -/
theorem scan_related (width : Nat) (b marked : Bool) (payload L R : List Bool)
    (hlen : payload.length = width) (t : Tape) (ht : TapeRel t (tapeLeft (block b payload marked ++ L) R)) :
    ∃ t', run (program width) (0,t) (width+3) = some (.inr (terminal width b marked,t')) ∧
      TapeRel t' (tapeLeft L (true::marked::(payload.reverse ++ b::R))) := by
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program width) (0,t)
    (0,tapeLeft (block b payload marked ++ L) R) rfl ht (width+3)
  rw [scan_block width b marked payload L R hlen] at h
  cases hr : run (program width) (0,t) (width+3) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = terminal width b marked ∧ _ at h
      refine ⟨t',?_,h.2⟩
      rw [h.1]

/-- An unmarked cycle is stable under finite blank padding. -/
theorem cycle_related (width : Nat) (b : Bool) (payload L R : List Bool)
    (hlen : payload.length = width) (t : Tape) (ht : TapeRel t (tapeLeft (block b payload false ++ L) R)) :
    ∃ t', run (program width) (0,t) (width+5) = some (.inr (0,t')) ∧
      TapeRel t' (tapeLeft L (true::false::(payload.reverse ++ b::R))) := by
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program width) (0,t)
    (0,tapeLeft (block b payload false ++ L) R) rfl ht (width+5)
  rw [cycle width b payload L R hlen] at h
  cases hr : run (program width) (0,t) (width+5) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = 0 ∧ TapeRel t' (Shared.Codes.FiniteProgramThreeExit.bounce _) at h
      refine ⟨t',?_,h.2.trans (Shared.Codes.FiniteProgramThreeExit.bounce_related _)⟩
      rw [h.1]

/-- Every finite sequence of unmarked blocks completes, followed by exactly
one marked block. The table never stalls inside a scan or restart, and the
entire scanned tape is retained in order modulo blank padding. -/
theorem run_to_marked (width : Nat) (xs : List (Bool × List Bool))
    (hxs : ∀ x ∈ xs, x.2.length = width)
    (first : Bool) (payload L R : List Bool) (hfirst : payload.length = width)
    (t : Tape) (ht : TapeRel t (tapeLeft (blocks xs ++ block first payload true ++ L) R)) :
    ∃ t', run (program width) (0,t) (xs.length*(width+5)+(width+3)) =
        some (.inr (terminal width first true,t')) ∧
      TapeRel t' (tapeLeft L ((block first payload true).reverse ++ (blocks xs).reverse ++ R)) := by
  induction xs generalizing t R with
  | nil =>
    obtain ⟨u,hu,hurel⟩ := scan_related width first true payload L R hfirst t
      (by simpa [blocks] using ht)
    refine ⟨u,?_,?_⟩
    · simpa using hu
    · simpa [blocks,block,List.reverse_append,List.reverse_cons,List.append_assoc] using hurel
  | cons x xs ih =>
    rcases x with ⟨b,word⟩
    have hword : word.length = width := hxs (b,word) (by simp)
    have htail : ∀ x ∈ xs, x.2.length = width := by
      intro x hx
      exact hxs x (by simp [hx])
    have hin : TapeRel t (tapeLeft
        (block b word false ++ (blocks xs ++ block first payload true ++ L)) R) := by
      simpa [blocks,List.append_assoc] using ht
    obtain ⟨u,hu,hurel⟩ := cycle_related width b word
      (blocks xs ++ block first payload true ++ L) R hword t hin
    have hurel' : TapeRel u (tapeLeft (blocks xs ++ block first payload true ++ L)
        ((block b word false).reverse ++ R)) := by
      simpa [block,List.reverse_append,List.reverse_cons,List.append_assoc] using hurel
    obtain ⟨v,hv,hvrel⟩ := ih htail ((block b word false).reverse ++ R) u hurel'
    refine ⟨v,?_,?_⟩
    · rw [show ((b,word)::xs).length * (width+5)+(width+3) =
          (width+5)+(xs.length*(width+5)+(width+3)) by simp; ring,
        run_continue _ _ _ _ _ hu]
      exact hv
    · simpa [blocks,List.reverse_append,List.reverse_cons,List.append_assoc] using hvrel

end Shared.Codes.FiniteProgramProtectedScanLoop
