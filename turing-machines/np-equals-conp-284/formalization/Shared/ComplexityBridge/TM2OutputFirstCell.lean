import Shared.Codes.FiniteProgramWriteBackHandoff
import Shared.Codes.FiniteProgramTaggedLoop
import Shared.ComplexityBridge.TM2OutputCellLoop

/-! A marked first output cell enters the actual unmarked-cell loop after a
charged physical write. This does not yet compact the sparse bits or replace
the terminal placeholder with a final output routine. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputFirstCell
open Turing
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2OutputCellClassify
open Shared.ComplexityBridge.TM2OutputCellRouter
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed)
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)

def source (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program := routed tm enc out true

def offset (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := (source tm enc out).length+2

def firstExit (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (v : Option Bool) : Nat := exit (core tm enc out true).length v

def program (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program :=
  Shared.Codes.FiniteProgramWriteBackHandoff.program (source tm enc out)
    (firstExit tm enc out (some false)) (firstExit tm enc out (some true))
    (Shared.ComplexityBridge.TM2OutputCellLoop.program tm enc out)

theorem program_valid (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : valid (program tm enc out) = true := by
  apply Shared.Codes.FiniteProgramWriteBackHandoff.program_valid
  · exact routed_valid tm enc out true
  · exact Shared.ComplexityBridge.TM2OutputCellLoop.program_valid tm enc out

theorem program_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : (program tm enc out).length = 8*(width+1)+16 := by
  simp [program,source,routed_length,Shared.ComplexityBridge.TM2OutputCellLoop.program_length]
  omega

private theorem exit_bounds (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) :
    firstExit tm enc out (some false) < (source tm enc out).length ∧
    firstExit tm enc out (some true) < (source tm enc out).length ∧
    firstExit tm enc out none < (source tm enc out).length := by
  simp [source,firstExit,routed,exit]

private theorem scan (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (v : Option Bool) (L suffix : List Bool) :
    let actual := code tm enc out true v
    let after := tapeAt (consumed L actual) suffix
    run (program tm enc out) (0,tapeAt L (actual++suffix)) (width+2) =
      some (.inr (firstExit tm enc out v,Shared.Codes.FiniteProgramThreeExit.bounce after)) := by
  let p := source tm enc out
  let a := firstExit tm enc out (some false)
  let b := firstExit tm enc out (some true)
  let q := Shared.ComplexityBridge.TM2OutputCellLoop.program tm enc out
  let actual := code tm enc out true v
  let after := tapeAt (consumed L actual) suffix
  have ha : ∃ r, ∀ t, step p (a,t) = some (.inl r) :=
    ⟨false, fun t => continuation_placeholder tm enc out true (some false) t⟩
  have hb : ∃ r, ∀ t, step p (b,t) = some (.inl r) :=
    ⟨false, fun t => continuation_placeholder tm enc out true (some true) t⟩
  have hr : run p (0,tapeAt L (actual++suffix)) (width+2) =
      some (.inr (firstExit tm enc out v,Shared.Codes.FiniteProgramThreeExit.bounce after)) :=
    classify_and_route tm enc dec hdec out true v L suffix
  change run (Shared.Codes.FiniteProgramWriteBackHandoff.program p a b q) _ _ = _
  apply Shared.Codes.FiniteProgramWriteBackHandoff.first_entry p a b q _ _ _
    (routed_valid tm enc out true) (by have h := (exit_bounds tm enc out).1; change a < p.length at h; omega)
    ha hb hr

/-- The marked cell is physically classified, its bit is written, and the
unmarked-loop state zero is entered after exactly `width+4` transitions. -/
theorem first_marked (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (L suffix : List Bool) :
    ∃ t', run (program tm enc out) (0,tapeAt L (code tm enc out true (some b)++suffix)) (width+4) =
        some (.inr (offset tm enc out,t')) ∧
      TapeRel t' (tapeAt (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
        (code tm enc out true (some b)) b L) suffix) := by
  let p := source tm enc out
  let a := firstExit tm enc out (some false)
  let d := firstExit tm enc out (some true)
  let q := Shared.ComplexityBridge.TM2OutputCellLoop.program tm enc out
  let actual := code tm enc out true (some b)
  let after := tapeAt (consumed L actual) suffix
  let t' := Shared.Codes.FiniteProgramWriteBackLoop.writePrevious b
    (Shared.Codes.FiniteProgramThreeExit.bounce after)
  have hr := scan tm enc dec hdec out (some b) L suffix
  have hb := exit_bounds tm enc out
  change a < p.length ∧ d < p.length ∧ _ at hb
  have hne : a ≠ d := by simp [a,d,firstExit,exit]
  have hhandoff := Shared.Codes.FiniteProgramWriteBackHandoff.handoff p a d q b
    (Shared.Codes.FiniteProgramThreeExit.bounce after) hb.1 hb.2.1 hne
  have hrun : run (program tm enc out) (0,tapeAt L (actual++suffix)) (width+4) =
      some (.inr (offset tm enc out,t')) := by
    rw [show width+4 = (width+2)+2 by omega,run_continue _ _ _ _ _ hr]
    cases b <;> simpa [program,p,a,d,q,offset,t',after,actual] using hhandoff
  refine ⟨t',hrun,?_⟩
  have hw := Shared.ComplexityBridge.TM2BinaryFiniteProgram.width_positive tm enc dec hdec
  have hne' : actual.reverse ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp only [List.length_reverse,List.length_nil] at hl
    have hc : actual.length = width := code_length tm enc out true (some b)
    omega
  cases hrev : actual.reverse with
  | nil => exact False.elim (hne' hrev)
  | cons last rest =>
    have hshape : Shared.Codes.FiniteProgramWriteBackLoop.writePrevious b after =
        tapeAt (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft actual b L) suffix := by
      simp [after,consumed,hrev,Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft,
        Shared.Codes.FiniteProgramWriteBackLoop.writePrevious_shape]
    have hrel := Shared.Codes.FiniteProgramWriteBackLoop.writePrevious_related b
      (Shared.Codes.FiniteProgramThreeExit.bounce after) after
      (Shared.Codes.FiniteProgramThreeExit.bounce_related after)
    rw [hshape] at hrel
    exact hrel

/-- The marked-first pass also works from any blank-equivalent physical tape. -/
theorem first_related (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (L suffix : List Bool) (t : Tape)
    (ht : TapeRel t (tapeAt L (code tm enc out true (some b)++suffix))) :
    ∃ t', run (program tm enc out) (0,t) (width+4) = some (.inr (offset tm enc out,t')) ∧
      TapeRel t' (tapeAt (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
        (code tm enc out true (some b)) b L) suffix) := by
  obtain ⟨u,hu,hurel⟩ := first_marked tm enc dec hdec out b L suffix
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program tm enc out) (0,t)
    (0,tapeAt L (code tm enc out true (some b)++suffix)) rfl ht (width+4)
  rw [hu] at h
  cases hr : run (program tm enc out) (0,t) (width+4) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = offset tm enc out ∧ TapeRel t' u at h
      refine ⟨t',?_,h.2.trans hurel⟩
      rw [h.1]

/-- A marked nonempty first cell and all following canonical unmarked cells
execute in one valid finite program, reaching the relocated end placeholder. -/
theorem run_nonempty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (b : Bool) (bs L suffix : List Bool) (t : Tape)
    (ht : TapeRel t (tapeAt L (code tm enc out true (some b) ++
      Shared.ComplexityBridge.TM2OutputCellLoop.stream tm enc out bs ++
        code tm enc out false none ++ suffix))) :
    ∃ t', run (program tm enc out) (0,t)
        ((width+4) + (bs.length*(width+4)+(width+2))) =
      some (.inr (offset tm enc out + Shared.ComplexityBridge.TM2OutputCellLoop.endExit tm enc out,t')) ∧
      TapeRel t' (tapeAt (consumed
        (Shared.ComplexityBridge.TM2OutputCellLoop.markedCells tm enc out bs
          (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft (code tm enc out true (some b)) b L))
        (code tm enc out false none)) suffix) := by
  let q := Shared.ComplexityBridge.TM2OutputCellLoop.program tm enc out
  let p := source tm enc out
  let a := firstExit tm enc out (some false)
  let d := firstExit tm enc out (some true)
  let left := Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft (code tm enc out true (some b)) b L
  obtain ⟨u,hu,hurel⟩ := first_related tm enc dec hdec out b L
    (Shared.ComplexityBridge.TM2OutputCellLoop.stream tm enc out bs ++ code tm enc out false none ++ suffix) t
    (by simpa only [List.append_assoc] using ht)
  obtain ⟨v,hv,hvrel⟩ := Shared.ComplexityBridge.TM2OutputCellLoop.run_to_end tm enc dec hdec out
    bs left suffix u hurel
  have hqvalid : valid q = true := Shared.ComplexityBridge.TM2OutputCellLoop.program_valid tm enc out
  have hqpos : 0 < q.length := Shared.Codes.FiniteProgramLink.valid_nonempty q hqvalid
  have hshift := Shared.Codes.FiniteProgramWriteBackHandoff.continuation p a d q hqvalid (0,u) hqpos
    (bs.length*(width+4)+(width+2))
  rw [hv] at hshift
  refine ⟨v,?_,hvrel⟩
  rw [run_continue _ _ _ _ _ hu]
  simpa [program,p,a,d,q,offset,shiftConfig,shiftStatus] using hshift

/-- An empty output reaches the distinct marked-empty continuation; it is not
silently treated as an unmarked output cell. -/
theorem run_empty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (L suffix : List Bool) :
    run (program tm enc out) (0,tapeAt L (code tm enc out true none ++ suffix)) (width+2) =
      some (.inr (firstExit tm enc out none,
        Shared.Codes.FiniteProgramThreeExit.bounce (tapeAt (consumed L (code tm enc out true none)) suffix))) :=
  scan tm enc dec hdec out none L suffix

/-- The genuine nonempty halted-stack serialization has one marked cell,
then exactly the unmarked stream consumed by `run_nonempty`. -/
theorem outputBits_nonempty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool)
    (bits : List Bool) (b : Bool) (bs : List Bool) (h : bits.reverse = b::bs) :
    Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm enc (bits.map out.symm) =
      code tm enc out true (some b) ++ Shared.ComplexityBridge.TM2OutputCellLoop.stream tm enc out bs := by
  rw [Shared.ComplexityBridge.TM2OutputCellCompare.outputBits_eq_cells]
  simp [Shared.ComplexityBridge.TM2OutputCellCompare.outputCells,h,
    Shared.ComplexityBridge.TM2OutputCellLoop.stream,code,symbol,List.flatMap_map]

/-- The genuine empty halted stack has precisely the marked empty cell. -/
theorem outputBits_empty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) :
    Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm enc ([] : List (tm.Γ tm.k₁)) =
      code tm enc out true none := by
  have h := Shared.ComplexityBridge.TM2OutputCellCompare.outputBits_eq_cells tm enc out []
  simpa [Shared.ComplexityBridge.TM2OutputCellCompare.outputCells,code,symbol] using h

/-- A finite number of explicit blank cells does not change the physical tape. -/
theorem append_blanks (L R : List Bool) (b : Bool) (n : Nat) :
    TapeRel (tapeAt L (b::R)) (tapeAt L (b::(R ++ List.replicate n false))) := by
  induction n with
  | zero => simp [TapeRel]
  | succ n ih =>
    have h := Shared.Codes.FiniteProgramTaggedLoop.tapeAt_append_blank L
      (R ++ List.replicate n false) b
    have hrep : List.replicate (n+1) false = List.replicate n false ++ [false] := by
      rw [List.replicate_add]
      simp
    simpa only [TapeRel,hrep,List.append_assoc] using ih.trans h

/-- The unmarked end code is one physical blank cell of the fixed width. -/
theorem end_code_blank (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool)
    (enc0 : enc default = List.Vector.replicate width false) :
    code tm enc out false none = List.replicate width false := by
  change (enc default).toList = List.replicate width false
  rw [enc0]
  rfl

/-- Starting with the actual translated halted output tape, the nonempty
case reaches the loop's end continuation in the stated number of steps. -/
theorem run_actual_nonempty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (enc0 : enc default = List.Vector.replicate width false)
    (bits : List Bool) (b : Bool) (bs : List Bool) (hrev : bits.reverse = b::bs) (t : Tape)
    (ht : Shared.ComplexityBridge.TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm enc (bits.map out.symm))) :
    ∃ t', run (program tm enc out) (0,t)
        ((width+4) + (bs.length*(width+4)+(width+2))) =
      some (.inr (offset tm enc out + Shared.ComplexityBridge.TM2OutputCellLoop.endExit tm enc out,t')) ∧
      TapeRel t' (tapeAt (consumed
        (Shared.ComplexityBridge.TM2OutputCellLoop.markedCells tm enc out bs
          (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft (code tm enc out true (some b)) b []))
        (code tm enc out false none)) []) := by
  let raw := Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm enc (bits.map out.symm)
  have hraw : raw = code tm enc out true (some b) ++
      Shared.ComplexityBridge.TM2OutputCellLoop.stream tm enc out bs :=
    outputBits_nonempty tm enc out bits b bs hrev
  have hw := Shared.ComplexityBridge.TM2BinaryFiniteProgram.width_positive tm enc dec hdec
  have hne : raw ≠ [] := by
    intro he
    have hl := congrArg List.length hraw
    simp only [he,List.length_nil,List.length_append,code_length] at hl
    omega
  have hbase : TapeRel t (tapeAt [] raw) := by
    change Shared.ComplexityBridge.TM0FiniteProgram.tape t =
      Shared.ComplexityBridge.TM0FiniteProgram.tape (initial raw).2
    rw [Shared.ComplexityBridge.TM0FiniteProgram.tape_initial]
    exact ht
  have hpad : TapeRel (tapeAt [] raw) (tapeAt [] (raw ++ List.replicate width false)) := by
    cases he : raw with
    | nil => exact False.elim (hne he)
    | cons x xs => simpa only [he,List.cons_append] using append_blanks [] xs x width
  have hinput := hbase.trans hpad
  have hblank := end_code_blank tm enc out enc0
  apply run_nonempty tm enc dec hdec out b bs [] [] t
  simpa only [TapeRel,hraw,hblank,List.append_nil,List.append_assoc] using hinput

/-- The marked-empty continuation remains a terminal placeholder to be
replaced by a later output phase. -/
theorem empty_placeholder (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape) :
    step (program tm enc out) (firstExit tm enc out none,t) = some (.inl false) := by
  let p := source tm enc out
  let a := firstExit tm enc out (some false)
  let b := firstExit tm enc out (some true)
  let q := Shared.ComplexityBridge.TM2OutputCellLoop.program tm enc out
  let e := firstExit tm enc out none
  have hb := exit_bounds tm enc out
  change a < p.length ∧ b < p.length ∧ e < p.length at hb
  have ha : e ≠ a := by simp [e,a,firstExit,exit]
  have hd : e ≠ b := by simp [e,b,firstExit,exit]
  have h := Shared.Codes.FiniteProgramWriteBackHandoff.source_other p a b q (e,t) hb.2.2 ha hd
  change step p (e,t) = step (program tm enc out) (e,t) at h
  rw [← h]
  exact continuation_placeholder tm enc out true none t

/-- The actual empty halted-output tape follows the marked-empty path, even
when its physical list representation contains additional blank cells. -/
theorem run_actual_empty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape)
    (ht : Shared.ComplexityBridge.TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm enc ([] : List (tm.Γ tm.k₁)))) :
    ∃ t', run (program tm enc out) (0,t) (width+2) =
        some (.inr (firstExit tm enc out none,t')) ∧
      TapeRel t' (tapeAt (consumed [] (code tm enc out true none)) []) := by
  let raw := code tm enc out true none
  let after := tapeAt (consumed [] raw) []
  have hraw : TapeRel t (tapeAt [] raw) := by
    change Shared.ComplexityBridge.TM0FiniteProgram.tape t =
      Shared.ComplexityBridge.TM0FiniteProgram.tape (initial raw).2
    rw [Shared.ComplexityBridge.TM0FiniteProgram.tape_initial]
    simpa [raw,outputBits_empty tm enc out] using ht
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program tm enc out) (0,t)
    (0,tapeAt [] raw) rfl hraw (width+2)
  have hexact := run_empty tm enc dec hdec out [] []
  simp only [List.append_nil] at hexact
  change run (program tm enc out) (0,tapeAt [] raw) (width+2) =
    some (.inr (firstExit tm enc out none,Shared.Codes.FiniteProgramThreeExit.bounce after)) at hexact
  rw [hexact] at h
  cases hr : run (program tm enc out) (0,t) (width+2) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨state,t'⟩
      rw [hr] at h
      change state = firstExit tm enc out none ∧
        TapeRel t' (Shared.Codes.FiniteProgramThreeExit.bounce after) at h
      refine ⟨t',?_,h.2.trans (Shared.Codes.FiniteProgramThreeExit.bounce_related after)⟩
      rw [h.1]

/-- The first marked cell can follow any number of ordinary sparse blocks;
the list-level reader recovers both the ordinary bits and the first bit. -/
theorem read_sparse_with_first (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (bs : List Bool) (b : Bool) (L : List Bool) :
    Shared.ComplexityBridge.TM2OutputCellLoop.readSparse width (bs.length+1)
      (bs.flatMap (Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm enc out) ++
        Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft (code tm enc out true (some b)) b L) =
      bs ++ [b] := by
  have hw := Shared.ComplexityBridge.TM2BinaryFiniteProgram.width_positive tm enc dec hdec
  induction bs with
  | nil => simp [Shared.ComplexityBridge.TM2OutputCellLoop.readSparse,
      Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft]
  | cons x xs ih =>
    have hb := Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock_length tm enc out hw x
    have hdrop : ((Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm enc out x) ++
        (xs.flatMap (Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm enc out) ++
          Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft (code tm enc out true (some b)) b L)).drop width =
        xs.flatMap (Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm enc out) ++
          Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft (code tm enc out true (some b)) b L := by
      simp [hb]
    have hhead : ((Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm enc out x) ++
        (xs.flatMap (Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm enc out) ++
          Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft (code tm enc out true (some b)) b L)).head?.getD false = x := by
      simp [Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock]
    simp only [List.flatMap_cons,List.length_cons,
      Shared.ComplexityBridge.TM2OutputCellLoop.readSparse,List.append_assoc,hhead,hdrop,ih,List.cons_append]

/-- After discarding the traversed blank cell, the abstract sparse view of
the physically written bits is the original output, including trailing false
bits. This is not a physical compaction algorithm. -/
theorem sparse_view_actual (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (bits : List Bool) (b : Bool) (bs L : List Bool) (hrev : bits.reverse = b::bs) :
    Shared.ComplexityBridge.TM2OutputCellLoop.readSparse width bits.length
      ((consumed (Shared.ComplexityBridge.TM2OutputCellLoop.markedCells tm enc out bs
        (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft (code tm enc out true (some b)) b L))
        (code tm enc out false none)).drop width) = bits := by
  have hlen : bits.length = bs.reverse.length+1 := by
    have h := congrArg List.length hrev
    simpa using h
  have hbits : bs.reverse ++ [b] = bits := by
    have h := congrArg List.reverse hrev
    simpa using h.symm
  have hdrop : (code tm enc out false none).reverse.drop width = [] := by
    apply List.drop_eq_nil_of_le
    simp [code_length]
  rw [hlen]
  simp only [consumed,List.drop_append,code_length,List.length_reverse,Nat.sub_self,
    hdrop,List.nil_append,List.drop_zero]
  rw [Shared.ComplexityBridge.TM2OutputCellLoop.markedCells_layout]
  simpa [hbits] using read_sparse_with_first tm enc dec hdec out bs.reverse b L

end Shared.ComplexityBridge.TM2OutputFirstCell
