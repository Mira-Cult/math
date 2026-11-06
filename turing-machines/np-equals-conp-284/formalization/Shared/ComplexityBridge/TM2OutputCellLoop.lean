import Shared.Codes.FiniteProgramWriteBackLoop
import Shared.ComplexityBridge.TM2OutputCellRouter

/-! A physical cyclic table classifies unmarked output cells, writes each
decoded bit into the last bit of the cell just traversed, and restarts. The
marked first cell and compaction of these sparse bits are separate phases. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputCellLoop
open Turing
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2OutputCellClassify
open Shared.ComplexityBridge.TM2OutputCellRouter
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed)
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def program (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program :=
  let p := routed tm enc out false
  let base := (core tm enc out false).length
  Shared.Codes.FiniteProgramWriteBackLoop.program p (exit base (some false)) (exit base (some true))

def endExit (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := exit (core tm enc out false).length none

/-- The last physical bit of a traversed code cell is replaced by its
decoded value; all earlier bits of that cell remain in the left tape. -/
def markedLeft (word : List Bool) (b : Bool) (L : List Bool) : List Bool :=
  b :: (word.reverse.tail ++ L)

theorem program_valid (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : valid (program tm enc out) = true := by
  apply Shared.Codes.FiniteProgramWriteBackLoop.program_valid
  exact routed_valid tm enc out false

theorem program_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : (program tm enc out).length = 4*(width+1)+8 := by
  simp [program,routed_length]

private theorem exit_bounds (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) :
    exit (core tm enc out false).length (some false) < (routed tm enc out false).length ∧
    exit (core tm enc out false).length (some true) < (routed tm enc out false).length ∧
    endExit tm enc out < (routed tm enc out false).length := by
  simp [routed,exit,endExit]

private theorem preserved_scan (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (value : Option Bool) (L suffix : List Bool) :
    let actual := code tm enc out false value
    let after := tapeAt (consumed L actual) suffix
    run (program tm enc out) (0,tapeAt L (actual++suffix)) (width+2) =
      some (.inr (exit (core tm enc out false).length value,
        Shared.Codes.FiniteProgramThreeExit.bounce after)) := by
  let p := routed tm enc out false
  let base := (core tm enc out false).length
  let a := exit base (some false)
  let b := exit base (some true)
  let actual := code tm enc out false value
  let after := tapeAt (consumed L actual) suffix
  have hstopa : ∃ r, ∀ t, step p (a,t) = some (.inl r) :=
    ⟨false,fun t => continuation_placeholder tm enc out false (some false) t⟩
  have hstopb : ∃ r, ∀ t, step p (b,t) = some (.inl r) :=
    ⟨false,fun t => continuation_placeholder tm enc out false (some true) t⟩
  have hrun : run p (0,tapeAt L (actual++suffix)) (width+2) =
      some (.inr (exit base value,Shared.Codes.FiniteProgramThreeExit.bounce after)) :=
    classify_and_route tm enc dec hdec out false value L suffix
  change run (Shared.Codes.FiniteProgramWriteBackLoop.program p a b) _ _ = _
  apply Shared.Codes.FiniteProgramWriteBackLoop.first_entry p a b _ _ _
    (routed_valid tm enc out false) (by have h := (exit_bounds tm enc out).1; change a < p.length at h; omega)
    hstopa hstopb hrun

/-- One decoded cell is marked and control returns to the next cell in
`width+4` transitions. This is an exact finite-table execution. -/
theorem cycle (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (L suffix : List Bool) :
    let actual := code tm enc out false (some b)
    let after := tapeAt (consumed L actual) suffix
    run (program tm enc out) (0,tapeAt L (actual++suffix)) (width+4) =
      some (.inr (0,Shared.Codes.FiniteProgramWriteBackLoop.writePrevious b
        (Shared.Codes.FiniteProgramThreeExit.bounce after))) := by
  let p := routed tm enc out false
  let base := (core tm enc out false).length
  let a := exit base (some false)
  let d := exit base (some true)
  let actual := code tm enc out false (some b)
  let after := tapeAt (consumed L actual) suffix
  have hscan := preserved_scan tm enc dec hdec out (some b) L suffix
  change run (Shared.Codes.FiniteProgramWriteBackLoop.program p a d)
    (0,tapeAt L (actual++suffix)) (width+2) =
      some (.inr (exit base (some b),Shared.Codes.FiniteProgramThreeExit.bounce after)) at hscan
  change run (Shared.Codes.FiniteProgramWriteBackLoop.program p a d) _ (width+4) = _
  rw [show width+4 = (width+2)+2 by omega,run_continue _ _ _ _ _ hscan]
  have hb := exit_bounds tm enc out
  change a < p.length ∧ d < p.length ∧ _ at hb
  have hne : a ≠ d := by simp [a,d,exit]
  cases b with
  | false =>
    exact Shared.Codes.FiniteProgramWriteBackLoop.write_false p a d hb.1 hne _
  | true =>
    exact Shared.Codes.FiniteProgramWriteBackLoop.write_true p a d hb.2.1 _

/-- At the unmarked end cell, the cyclic table reaches its untouched end
continuation after the classifier and router steps. -/
theorem finish (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (L suffix : List Bool) :
    let actual := code tm enc out false none
    let after := tapeAt (consumed L actual) suffix
    run (program tm enc out) (0,tapeAt L (actual++suffix)) (width+2) =
      some (.inr (endExit tm enc out,Shared.Codes.FiniteProgramThreeExit.bounce after)) := by
  exact preserved_scan tm enc dec hdec out none L suffix

/-- The exact cycle marks the last cell bit while preserving all other tape
contents, modulo the list-tape blank convention. -/
theorem cycle_marked (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (L suffix : List Bool) :
    let actual := code tm enc out false (some b)
    ∃ t', run (program tm enc out) (0,tapeAt L (actual++suffix)) (width+4) = some (.inr (0,t')) ∧
      TapeRel t' (tapeAt (markedLeft actual b L) suffix) := by
  let actual := code tm enc out false (some b)
  let after := tapeAt (consumed L actual) suffix
  let target := Shared.Codes.FiniteProgramWriteBackLoop.writePrevious b
    (Shared.Codes.FiniteProgramThreeExit.bounce after)
  refine ⟨target,cycle tm enc dec hdec out b L suffix,?_⟩
  have hw := Shared.ComplexityBridge.TM2BinaryFiniteProgram.width_positive tm enc dec hdec
  have hne : actual.reverse ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp only [List.length_reverse,List.length_nil] at hl
    have hc : actual.length = width := code_length tm enc out false (some b)
    omega
  cases hrev : actual.reverse with
  | nil => exact False.elim (hne hrev)
  | cons last rest =>
    have hshape : Shared.Codes.FiniteProgramWriteBackLoop.writePrevious b after =
        tapeAt (markedLeft actual b L) suffix := by
      simp [after,consumed,hrev,markedLeft,Shared.Codes.FiniteProgramWriteBackLoop.writePrevious_shape]
    have hrel := Shared.Codes.FiniteProgramWriteBackLoop.writePrevious_related b
      (Shared.Codes.FiniteProgramThreeExit.bounce after) after
      (Shared.Codes.FiniteProgramThreeExit.bounce_related after)
    rw [hshape] at hrel
    exact hrel

/-- One cycle has the same behavior for any blank-equivalent input tape. -/
theorem cycle_related (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (L suffix : List Bool) (t : Tape)
    (ht : TapeRel t (tapeAt L (code tm enc out false (some b)++suffix))) :
    ∃ t', run (program tm enc out) (0,t) (width+4) = some (.inr (0,t')) ∧
      TapeRel t' (tapeAt (markedLeft (code tm enc out false (some b)) b L) suffix) := by
  obtain ⟨u,hu,hout⟩ := cycle_marked tm enc dec hdec out b L suffix
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program tm enc out) (0,t)
    (0,tapeAt L (code tm enc out false (some b)++suffix)) rfl ht (width+4)
  rw [hu] at h
  cases hr : run (program tm enc out) (0,t) (width+4) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = 0 ∧ TapeRel t' u at h
      refine ⟨t',?_,h.2.trans hout⟩
      rw [h.1]

/-- The end-cell continuation remains a terminal placeholder for the later
compaction phase. -/
theorem end_placeholder (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape) :
    step (program tm enc out) (endExit tm enc out,t) = some (.inl false) := by
  let p := routed tm enc out false
  let base := (core tm enc out false).length
  let a := exit base (some false)
  let b := exit base (some true)
  let e := endExit tm enc out
  have hb := exit_bounds tm enc out
  change a < p.length ∧ b < p.length ∧ e < p.length at hb
  have ha : e ≠ a := by simp [e,a,endExit,base,exit]
  have hc : e ≠ b := by simp [e,b,endExit,base,exit]
  have h := Shared.Codes.FiniteProgramWriteBackLoop.source_other p a b (e,t) hb.2.2 ha hc
  change step p (e,t) = step (program tm enc out) (e,t) at h
  rw [← h]
  exact continuation_placeholder tm enc out false none t

def stream (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) : List Bool :=
  bits.flatMap (fun b => code tm enc out false (some b))

def markedCells (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : List Bool → List Bool → List Bool
  | [], L => L
  | b::bs, L => markedCells tm enc out bs (markedLeft (code tm enc out false (some b)) b L)

def markedBlock (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (b : Bool) : List Bool :=
  b :: (code tm enc out false (some b)).reverse.tail

theorem markedCells_layout (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits L : List Bool) :
    markedCells tm enc out bits L = bits.reverse.flatMap (markedBlock tm enc out) ++ L := by
  induction bits generalizing L with
  | nil => rfl
  | cons b bs ih =>
    simp [markedCells,markedLeft,markedBlock,ih,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem markedBlock_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (hw : 0 < width) (b : Bool) :
    (markedBlock tm enc out b).length = width := by
  simp [markedBlock,code_length]
  omega

/-- Read the leading bit of each fixed-width sparse block. -/
def readSparse (width : Nat) : Nat → List Bool → List Bool
  | 0, _ => []
  | n+1, xs => xs.head?.getD false :: readSparse width n (xs.drop width)

theorem readSparse_blocks (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (hw : 0 < width) (bits L : List Bool) :
    readSparse width bits.length (bits.flatMap (markedBlock tm enc out) ++ L) = bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    have hb := markedBlock_length tm enc out hw b
    have hdrop : ((markedBlock tm enc out b) ++ (bs.flatMap (markedBlock tm enc out) ++ L)).drop width =
        bs.flatMap (markedBlock tm enc out) ++ L := by
      simp [List.drop_append,hb]
    have hhead : ((markedBlock tm enc out b) ++ (bs.flatMap (markedBlock tm enc out) ++ L)).head?.getD false = b := by
      simp [markedBlock]
    simp only [List.flatMap_cons,List.length_cons,readSparse,List.append_assoc,hhead,hdrop,ih]

/-- The sparse tape contains the written bits in reverse processing order. -/
theorem readSparse_markedCells (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (bits L : List Bool) :
    readSparse width bits.length (markedCells tm enc out bits L) = bits.reverse := by
  rw [markedCells_layout]
  have hw := Shared.ComplexityBridge.TM2BinaryFiniteProgram.width_positive tm enc dec hdec
  simpa using readSparse_blocks tm enc out hw bits.reverse L

/-- The cyclic table processes any finite list of unmarked cells. The
left-tape invariant records each decoded bit in its traversed cell. -/
theorem run_cells (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (bits L suffix : List Bool) (t : Tape) (ht : TapeRel t (tapeAt L (stream tm enc out bits ++ suffix))) :
    ∃ t', run (program tm enc out) (0,t) (bits.length*(width+4)) = some (.inr (0,t')) ∧
      TapeRel t' (tapeAt (markedCells tm enc out bits L) suffix) := by
  induction bits generalizing L t with
  | nil => exact ⟨t,by simp [run],by simpa [stream,markedCells] using ht⟩
  | cons b bs ih =>
    have ht' : TapeRel t (tapeAt L (code tm enc out false (some b) ++ (stream tm enc out bs ++ suffix))) := by
      simpa [stream,List.append_assoc] using ht
    obtain ⟨u,hu,hurel⟩ := cycle_related tm enc dec hdec out b L (stream tm enc out bs ++ suffix) t ht'
    obtain ⟨v,hv,hvrel⟩ := ih (markedLeft (code tm enc out false (some b)) b L) u hurel
    refine ⟨v,?_,by simpa [markedCells] using hvrel⟩
    rw [show (b::bs).length*(width+4) = (width+4)+bs.length*(width+4) by simp [Nat.add_mul,Nat.add_comm],
      run_continue _ _ _ _ _ hu]
    exact hv

/-- The terminating cell is recognized on any blank-equivalent tape. -/
theorem finish_related (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (L suffix : List Bool) (t : Tape) (ht : TapeRel t (tapeAt L (code tm enc out false none++suffix))) :
    ∃ t', run (program tm enc out) (0,t) (width+2) = some (.inr (endExit tm enc out,t')) ∧
      TapeRel t' (tapeAt (consumed L (code tm enc out false none)) suffix) := by
  let after := tapeAt (consumed L (code tm enc out false none)) suffix
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program tm enc out) (0,t)
    (0,tapeAt L (code tm enc out false none++suffix)) rfl ht (width+2)
  rw [finish tm enc dec hdec out L suffix] at h
  cases hr : run (program tm enc out) (0,t) (width+2) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = endExit tm enc out ∧ TapeRel t' (Shared.Codes.FiniteProgramThreeExit.bounce after) at h
      refine ⟨t',?_,h.2.trans (Shared.Codes.FiniteProgramThreeExit.bounce_related after)⟩
      rw [h.1]

/-- The actual cyclic table processes every supplied cell and reaches the
end continuation, with the total transition count charged explicitly. -/
theorem run_to_end (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (bits L suffix : List Bool) (t : Tape)
    (ht : TapeRel t (tapeAt L (stream tm enc out bits ++ code tm enc out false none ++ suffix))) :
    ∃ t', run (program tm enc out) (0,t) (bits.length*(width+4)+(width+2)) =
      some (.inr (endExit tm enc out,t')) ∧
      TapeRel t' (tapeAt (consumed (markedCells tm enc out bits L) (code tm enc out false none)) suffix) := by
  obtain ⟨u,hu,hurel⟩ := run_cells tm enc dec hdec out bits L (code tm enc out false none ++ suffix) t
    (by simpa [List.append_assoc] using ht)
  obtain ⟨v,hv,hvrel⟩ := finish_related tm enc dec hdec out (markedCells tm enc out bits L) suffix u hurel
  refine ⟨v,?_,hvrel⟩
  rw [run_continue _ _ _ _ _ hu]
  exact hv

end Shared.ComplexityBridge.TM2OutputCellLoop
