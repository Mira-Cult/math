import Shared.Codes.FiniteProgramOneExit
import Shared.ComplexityBridge.TM2OutputProtectedScan

/-! Link the protected output writer's nonempty endpoint to the first physical
protected-block scan. The scan's four exits and the separate empty output
endpoint remain placeholders; this is not a complete output compactor. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputProtectedPipeline
open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramTwoWordClassify (mask)
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2OutputProtectedCodec
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM2OutputCellCompare (cell)

def source (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program :=
  Shared.ComplexityBridge.TM2OutputFirstCell.program tm (encode tm enc) out

def stop (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat :=
  Shared.ComplexityBridge.TM2OutputFirstCell.offset tm (encode tm enc) out +
    Shared.ComplexityBridge.TM2OutputCellLoop.endExit tm (encode tm enc) out

def program (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program :=
  Shared.Codes.FiniteProgramOneExit.program (source tm enc out)
    (Shared.ComplexityBridge.TM2OutputProtectedScan.positioned width) (stop tm enc out)

def offset (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := Shared.Codes.FiniteProgramOneExit.offset (source tm enc out)

/-- The source's nonempty continuation is an actual in-range table row. -/
theorem stop_bound (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : stop tm enc out < (source tm enc out).length := by
  simp [stop,source,Shared.ComplexityBridge.TM2OutputFirstCell.offset,
    Shared.ComplexityBridge.TM2OutputFirstCell.source,
    Shared.ComplexityBridge.TM2OutputCellRouter.routed_length,
    Shared.ComplexityBridge.TM2OutputCellLoop.endExit,
    Shared.ComplexityBridge.TM2OutputCellRouter.exit,
    Shared.ComplexityBridge.TM2OutputCellRouter.core,
    Shared.ComplexityBridge.TM2OutputFirstCell.program_length]
  omega

/-- Before replacement, this source row really is a terminal placeholder for
all tapes. -/
theorem source_stop (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape) : step (source tm enc out) (stop tm enc out,t) = some (.inl false) := by
  let first := Shared.ComplexityBridge.TM2OutputFirstCell.source tm (encode tm enc) out
  let a := Shared.ComplexityBridge.TM2OutputFirstCell.firstExit tm (encode tm enc) out (some false)
  let b := Shared.ComplexityBridge.TM2OutputFirstCell.firstExit tm (encode tm enc) out (some true)
  let q := Shared.ComplexityBridge.TM2OutputCellLoop.program tm (encode tm enc) out
  let e := Shared.ComplexityBridge.TM2OutputCellLoop.endExit tm (encode tm enc) out
  have hq : valid q = true := Shared.ComplexityBridge.TM2OutputCellLoop.program_valid tm (encode tm enc) out
  have he : e < q.length := by
    simp [e,q,Shared.ComplexityBridge.TM2OutputCellLoop.program_length,
      Shared.ComplexityBridge.TM2OutputCellLoop.endExit,Shared.ComplexityBridge.TM2OutputCellRouter.exit,
      Shared.ComplexityBridge.TM2OutputCellRouter.core]
  have h := Shared.Codes.FiniteProgramWriteBackHandoff.continuation first a b q hq (e,t) he 1
  have hs := Shared.ComplexityBridge.TM2OutputCellLoop.end_placeholder tm (encode tm enc) out t
  have hqrun : run q (e,t) 1 = some (.inl false) := by simpa [run,advance] using hs
  rw [hqrun] at h
  simpa [source,stop,first,a,b,q,e,Shared.ComplexityBridge.TM2OutputFirstCell.program,
    Shared.ComplexityBridge.TM2OutputFirstCell.offset,Shared.Codes.FiniteProgramWriteBackHandoff.prefix_length,
    shiftConfig,shiftStatus,run,advance] using h

/-- The linked writer and positioned scanner are one valid finite binary table. -/
theorem program_valid (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : valid (program tm enc out) = true := by
  apply Shared.Codes.FiniteProgramOneExit.program_valid
  · exact Shared.ComplexityBridge.TM2OutputFirstCell.program_valid tm (encode tm enc) out
  · exact Shared.ComplexityBridge.TM2OutputProtectedScan.positioned_valid width
  · exact stop_bound tm enc out

/-- The combined table has a fixed linear state cost in the underlying
alphabet-code width. -/
theorem program_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : (program tm enc out).length = 13*width+70 := by
  simp [program,source,Shared.Codes.FiniteProgramOneExit.program_length,
    Shared.Codes.FiniteProgramOneExit.offset,
    Shared.ComplexityBridge.TM2OutputFirstCell.program_length,
    Shared.ComplexityBridge.TM2OutputProtectedScan.positioned_length]
  omega

/-- A nonempty output's written sparse layout begins with the original
output's first bit; the retained marker says whether it is the only block. -/
theorem sparse_head (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool)
    (bits : List Bool) (first : Bool) (bs : List Bool) (hrev : bits.reverse = first::bs) :
    ∃ b marked L, bits.head? = some b ∧ marked = (bits.length == 1) ∧
      Shared.ComplexityBridge.TM2OutputCellLoop.markedCells tm (encode tm enc) out bs
        (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
          (Shared.ComplexityBridge.TM2OutputCellClassify.code tm (encode tm enc) out true (some first)) first []) =
      dataBlock tm enc out marked b ++ L := by
  have hbits : bs.reverse ++ [first] = bits := by
    have h := congrArg List.reverse hrev
    simpa using h.symm
  have hblock (b : Bool) : Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm (encode tm enc) out b =
      dataBlock tm enc out false b := by
    simp [dataBlock,Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock,
      Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft]
  rw [Shared.ComplexityBridge.TM2OutputCellLoop.markedCells_layout]
  cases h : bs.reverse with
  | nil =>
    refine ⟨first,true,[],?_,?_,?_⟩
    · rw [← hbits,h]; rfl
    · rw [← hbits,h]; rfl
    · simp [h,dataBlock]
  | cons b rest =>
    refine ⟨b,false,rest.flatMap (Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm (encode tm enc) out) ++
      dataBlock tm enc out true first,?_,?_,?_⟩
    · rw [← hbits,h]; rfl
    · rw [← hbits,h]
      simp
    · simp [h,hblock,dataBlock,List.append_assoc]

def writerCost (width count : Nat) : Nat :=
  ((width+3)+4) + (count*((width+3)+4)+((width+3)+2))

def scannerCost (width : Nat) : Nat := (width+4)+(width+3)

/-- The complete writer, handoff, and first scan use a polynomial number of
physical transitions in the code width and the number of output bits. -/
theorem combined_cost (width count : Nat) :
    writerCost width count + (2+scannerCost width) = (count+1)*(width+7)+3*width+14 := by
  simp [writerCost,scannerCost]
  ring

theorem cost_from_output_length (width : Nat) (bits : List Bool) (first : Bool) (bs : List Bool)
    (hrev : bits.reverse = first::bs) :
    writerCost width bs.length + (2+scannerCost width) = bits.length*(width+7)+3*width+14 := by
  have hl : bits.length = bs.length+1 := by
    have h := congrArg List.length hrev
    simpa using h
  rw [combined_cost,hl]

def emptyStop (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat :=
  Shared.ComplexityBridge.TM2OutputFirstCell.firstExit tm (encode tm enc) out none

theorem emptyStop_bound (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : emptyStop tm enc out < (source tm enc out).length := by
  simp [emptyStop,source,Shared.ComplexityBridge.TM2OutputFirstCell.firstExit,
    Shared.ComplexityBridge.TM2OutputCellRouter.exit,Shared.ComplexityBridge.TM2OutputCellRouter.core,
    Shared.ComplexityBridge.TM2OutputFirstCell.program_length]
  omega

/-- The empty path is not redirected to the nonempty scanner. -/
theorem empty_placeholder (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape) :
    step (program tm enc out) (emptyStop tm enc out,t) = some (.inl false) := by
  let p := source tm enc out
  let q := Shared.ComplexityBridge.TM2OutputProtectedScan.positioned width
  let e := stop tm enc out
  let z := emptyStop tm enc out
  have hz : z < p.length := emptyStop_bound tm enc out
  have hne : z ≠ e := empty_nonempty_state_ne tm enc out
  have h := Shared.Codes.FiniteProgramTwoExit.source_other p q e e (z,t) hz hne hne
  change step p (z,t) = step (program tm enc out) (z,t) at h
  rw [← h]
  exact Shared.ComplexityBridge.TM2OutputFirstCell.empty_placeholder tm (encode tm enc) out t

/-- Empty halted output still reaches its own unmodified placeholder. -/
theorem run_empty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape)
    (ht : Shared.ComplexityBridge.TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm (encode tm enc) ([] : List (tm.Γ tm.k₁)))) :
    ∃ t', run (program tm enc out) (0,t) ((width+3)+2) =
        some (.inr (emptyStop tm enc out,t')) ∧
      TapeRel t' (tapeAt (consumed []
        (Shared.ComplexityBridge.TM2OutputCellClassify.code tm (encode tm enc) out true none)) []) := by
  let p := source tm enc out
  let q := Shared.ComplexityBridge.TM2OutputProtectedScan.positioned width
  let e := stop tm enc out
  have hp : valid p = true := Shared.ComplexityBridge.TM2OutputFirstCell.program_valid tm (encode tm enc) out
  have hp0 : 0 < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  obtain ⟨u,hu,hurel⟩ := Shared.ComplexityBridge.TM2OutputFirstCell.run_actual_empty
    tm (encode tm enc) (decode tm dec) (decode_encode tm enc dec hdec) out t ht
  have hpre := Shared.Codes.FiniteProgramOneExit.first_entry p q e (0,t)
    (emptyStop tm enc out,u) ((width+3)+2) hp hp0 (source_stop tm enc out) hu
  exact ⟨u,hpre,hurel⟩

/-- A single finite table starts at the actual protected halted TM2 output
tape, writes its nonempty output cells, crosses the paid handoff, and scans
the first output bit. The four scan exits remain explicit placeholders. -/
theorem run_nonempty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) (first : Bool) (bs : List Bool)
    (hrev : bits.reverse = first::bs) (t : Tape)
    (ht : Shared.ComplexityBridge.TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm (encode tm enc) (bits.map out.symm))) :
    ∃ b marked L t', bits.head? = some b ∧ marked = (bits.length == 1) ∧
      run (program tm enc out) (0,t) (writerCost width bs.length + (2+scannerCost width)) =
        some (.inr (offset tm enc out + ((width+4) +
          Shared.Codes.FiniteProgramProtectedScan.state (width+3) (mask b marked)),t')) ∧
      TapeRel t' (tapeLeft L (true::marked::((enc (cell tm out marked b)).toList ++
        b::(List.replicate (width+3) false ++ [false])))) := by
  let p := source tm enc out
  let q := Shared.ComplexityBridge.TM2OutputProtectedScan.positioned width
  let e := stop tm enc out
  have hp : valid p = true := Shared.ComplexityBridge.TM2OutputFirstCell.program_valid tm (encode tm enc) out
  have hq : valid q = true := Shared.ComplexityBridge.TM2OutputProtectedScan.positioned_valid width
  have hp0 : 0 < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  have hq0 : 0 < q.length := Shared.Codes.FiniteProgramLink.valid_nonempty q hq
  have he : e < p.length := stop_bound tm enc out
  have hstop : ∀ tape, step p (e,tape) = some (.inl false) := source_stop tm enc out
  obtain ⟨b,marked,L,hhead,hmark,hsparse⟩ := sparse_head tm enc out bits first bs hrev
  have hdec' := decode_encode tm enc dec hdec
  have henc0 := encode_blank tm enc enc0
  obtain ⟨u,hu,hurel⟩ := Shared.ComplexityBridge.TM2OutputFirstCell.run_actual_nonempty
    tm (encode tm enc) (decode tm dec) hdec' out henc0 bits first bs hrev t ht
  change run p (0,t) (writerCost width bs.length) = some (.inr (e,u)) at hu
  have hpre := Shared.Codes.FiniteProgramOneExit.first_entry p q e (0,t) (e,u)
    (writerCost width bs.length) hp hp0 hstop hu
  have hblank := Shared.ComplexityBridge.TM2OutputFirstCell.end_code_blank tm (encode tm enc) out henc0
  have hcanon : TapeRel u (tapeAt (List.replicate (width+3) false ++ dataBlock tm enc out marked b ++ L) []) := by
    simpa [consumed,hblank,hsparse,List.append_assoc] using hurel
  have hbounce : TapeRel (Shared.Codes.FiniteProgramThreeExit.bounce u)
      (tapeAt (List.replicate (width+3) false ++ dataBlock tm enc out marked b ++ L) []) :=
    (Shared.Codes.FiniteProgramThreeExit.bounce_related u).trans hcanon
  obtain ⟨v,hscan,hv⟩ := Shared.ComplexityBridge.TM2OutputProtectedScan.positioned_scan_related
    tm enc dec hdec enc0 out b marked L (Shared.Codes.FiniteProgramThreeExit.bounce u) hbounce
  have hhand := Shared.Codes.FiniteProgramOneExit.handoff p q e he u
  have hshift := Shared.Codes.FiniteProgramOneExit.continuation p q e hq
    (0,Shared.Codes.FiniteProgramThreeExit.bounce u) hq0 (scannerCost width)
  change run q (0,Shared.Codes.FiniteProgramThreeExit.bounce u) (scannerCost width) = _ at hscan
  rw [hscan] at hshift
  refine ⟨b,marked,L,v,hhead,hmark,?_,hv⟩
  change run (Shared.Codes.FiniteProgramOneExit.program p q e) _ _ = _
  rw [run_continue _ _ _ _ _ hpre,run_continue _ _ _ _ _ hhand]
  simpa [source,program,offset,p,q,e,shiftConfig,shiftStatus] using hshift

end Shared.ComplexityBridge.TM2OutputProtectedPipeline
