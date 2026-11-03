import Shared.PNP.Record285.GrammarSuccessor

/-! Exact finite literal dispatch to any producer-grammar leaf. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch

theorem expected_unmarked (edge : Edge) (b : Bool) (row : Row 285)
    (h : expected edge b = some row) : row.beep = false := by
  cases edge with
  | node j =>
    simp only [expected] at h
    split at h <;> simp_all <;> subst row <;> rfl
  | inc j =>
    simp only [expected] at h
    split at h <;> simp_all <;> subst row <;> rfl
  | dec j =>
    simp only [expected] at h
    split at h <;> simp_all <;> subst row <;> rfl
  | half j =>
    simp only [expected] at h
    split at h <;> simp_all <;> subst row <;> rfl
  | beep =>
    simp only [expected,Option.some.injEq] at h
    subst row
    rfl
  | brk j =>
    cases b with
    | false => simp [expected] at h
    | true =>
      simp only [expected,if_true] at h
      cases hj : breakTerminal j with
      | none => simp [hj] at h
      | some q => simp [hj] at h; subst row; rfl
  | cont j =>
    cases b with
    | false => simp [expected] at h
    | true =>
      simp only [expected,if_true] at h
      cases hj : continueTerminal j with
      | none => simp [hj] at h
      | some q => simp [hj] at h; subst row; rfl

/-- Full symbolic destination of a grammar leaf's literal row. -/
def leafDestination (row : Row 285) (pre : List Bool) : SymbolicDispatch.Config :=
  let left := pre.reverse++rootLeft
  match row.move with
  | .left => ⟨row.next,-2,left.tail,left.headD false,[row.write,false]⟩
  | .right => ⟨row.next,0,row.write::left,false,[]⟩

theorem rightWord_append_bit (q : Fin 285) (head : Int) (pre : List Bool)
    (b : Bool) (left : List Bool) :
    rightWord q head (pre++[b]) false left [] = rightWord q head pre b left [false] := by
  cases pre <;> simp [rightWord,List.append_assoc]

/-- The last literal row is executable on the represented tape; no unknown
tail cell is read and its event flag is false. -/
theorem leaf_step (pre : List Bool) (parent : Nat) (bit : Bool) (row : Row 285)
    (hrow : NumericTables.target.table.row (state parent) bit = row)
    (hbeep : row.beep = false) :
    SymbolicDispatch.step ⟨state parent,-1,pre.reverse++rootLeft,bit,[false]⟩ =
      some (leafDestination row pre) := by
  cases row with
  | mk write move next beep =>
    simp only at hbeep
    subst beep
    cases move with
    | right => simp [SymbolicDispatch.step,hrow,leafDestination]
    | left =>
      cases hl : pre.reverse++rootLeft with
      | nil =>
        have hn : pre.reverse++rootLeft ≠ [] := by simp [rootLeft]
        contradiction
      | cons x xs =>
        simp [SymbolicDispatch.step,hrow,leafDestination,hl]

/-- Any complete producer-grammar path is followed in exactly its bit length,
including its final literal row. The complete resulting symbolic tape is
returned; unknown tape tails remain untouched. -/
theorem root_leaf_symbolic (code : List Bool) (e : Edge)
    (hwalk : walk rootIndex code = some e) :
    ∃ pre bit row, code = pre++[bit] ∧ expected e bit = some row ∧
      run code.length (rightWord treeRoot (-(code.length:Int)) code false rootLeft []) =
        some (leafDestination row pre) := by
  obtain ⟨pre,bit,parent,row,hcode,hroute,_,hexpected,hrow⟩ :=
    root_final_edge code e (by simpa only [rootIndex] using hwalk)
  have hnum : NumericTables.target.table.row (state parent) bit = row := by
    rw [← ArtifactEndpoint.literal_rows]
    exact hrow
  have hflag := expected_unmarked e bit row hexpected
  have hs := route_scan pre treeRoot (state parent) hroute (-(code.length:Int)) bit rootLeft [false]
  have hhead : -(code.length:Int)+(pre.length:Int) = -1 := by
    rw [hcode]
    simp only [List.length_append,List.length_singleton,Int.natCast_add,Int.natCast_one]
    omega
  rw [hhead] at hs
  have hlast := leaf_step pre parent bit row hnum hflag
  refine ⟨pre,bit,row,hcode,hexpected,?_⟩
  rw [hcode,rightWord_append_bit]
  have hlen : (pre++[bit]).length = pre.length+1 := by simp
  rw [hcode,hlen] at hs
  rw [hlen,run_add,hs]
  simp only [Option.bind_some,run,hlast,Option.bind_some]

/-- Full physical-tape, event-free execution through the final row for any
producer-grammar leaf. This does not prove a primitive's subsequent behavior. -/
theorem root_leaf_physical (code : List Bool) (e : Edge)
    (hwalk : walk rootIndex code = some e) (head : Int) (leftTail rightTail : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail rightTail) physical) :
    ∃ pre bit row, code = pre++[bit] ∧ expected e bit = some row ∧
      Rel (denote (leafDestination row pre) head leftTail rightTail)
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run code.length) ∧
      (∀ t, t < code.length →
        ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < code.length := by
  obtain ⟨pre,bit,row,hcode,hexpected,hs⟩ := root_leaf_symbolic code e hwalk
  have hn := run_sound code.length _ _ hs head leftTail rightTail
  have hp := silent_physical Record285.machine _ physical hrel _ _ hn
  refine ⟨pre,bit,row,hcode,hexpected,hp.1,hp.2,?_⟩
  rw [hcode]
  simp

/-- Exact producer bytes and the physical dispatch contract for any leaf,
combined without a separate text-binding premise. -/
theorem bound_root_leaf_physical (code : List Bool) (e : Edge)
    (hwalk : walk rootIndex code = some e) (head : Int) (leftTail rightTail : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail rightTail) physical) :
    literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) ∧
    ∃ pre bit row, code = pre++[bit] ∧ expected e bit = some row ∧
      Rel (denote (leafDestination row pre) head leftTail rightTail)
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run code.length) ∧
      (∀ t, t < code.length →
        ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < code.length :=
  ⟨literal_typed_serialization,root_leaf_physical code e hwalk head leftTail rightTail physical hrel⟩

theorem window_length (input : Nat → Bool) (pos len : Nat) : (window input pos len).length = len := by
  induction len generalizing pos with
  | zero => rfl
  | succ len ih => simp only [window,List.length_cons,ih]

/-- For any infinite bit stream, the grammar supplies a leaf path of length
at most 163. Whenever the physical tape has the stated clean layout for
that path, the literal machine executes its full dispatcher segment silently. -/
theorem root_stream_dispatch (input : Nat → Bool) (pos : Nat) (head : Int) (leftTail rightTail : Nat) :
    ∃ e len, 0 < len ∧ len ≤ 163 ∧ (window input pos len).length = len ∧ isLeaf e = true ∧
      walk rootIndex (window input pos len) = some e ∧
      ∀ physical : Shared.Beeping.Machines.Config 285,
        Rel (rootEntry (window input pos len) head leftTail rightTail) physical →
        ∃ pre bit row, window input pos len = pre++[bit] ∧ expected e bit = some row ∧
          Rel (denote (leafDestination row pre) head leftTail rightTail)
            ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run (window input pos len).length) ∧
          (∀ t, t < (window input pos len).length →
            ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
          0 < (window input pos len).length := by
  obtain ⟨e,len,hpos,hbound,hleaf,hwalk⟩ := root_walk_terminates input pos
  have hw : walk rootIndex (window input pos len) = some e := by simpa only [rootIndex] using hwalk
  refine ⟨e,len,hpos,hbound,window_length input pos len,hleaf,hw,?_⟩
  intro physical hrel
  exact root_leaf_physical (window input pos len) e hw head leftTail rightTail physical hrel

end Shared.PNP.Record285.Grammar
