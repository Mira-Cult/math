import Shared.Codes.FiniteProgramOneExit
import Shared.ComplexityBridge.TM2OutputProtectedLoop
import Shared.ComplexityBridge.TM2OutputProtectedPipeline

/-! One finite table writes the protected halted-output cells and then scans
all of them until the retained marked first cell. The final two states and
empty-output state remain placeholders: output compaction is not implemented. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputProtectedAllScan
open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramProtectedScanLoop (block blocks terminal)
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2OutputProtectedCodec
open Shared.ComplexityBridge.TM2OutputCellCompare (cell)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def payload (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) : List Bool :=
  (enc (cell tm out marked b)).toList.reverse

def cells (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (xs : List Bool) : List (Bool × List Bool) :=
  xs.map (fun b => (b,payload tm enc out false b))

@[simp] theorem payload_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) : (payload tm enc out marked b).length = width := by
  simp [payload]

theorem cells_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (xs : List Bool) :
    ∀ x ∈ cells tm enc out xs, x.2.length = width := by
  intro x hx
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
  exact payload_length tm enc out false b

/-- The reverse stack traversal after write-back is exactly the loop's
unmarked sequence followed by its marked terminal block. -/
theorem sparse_layout (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (first : Bool) (bs : List Bool) :
    Shared.ComplexityBridge.TM2OutputCellLoop.markedCells tm (encode tm enc) out bs
      (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
        (Shared.ComplexityBridge.TM2OutputCellClassify.code tm (encode tm enc) out true (some first)) first []) =
    blocks (cells tm enc out bs.reverse) ++ block first (payload tm enc out true first) true := by
  have hblock (marked b : Bool) : dataBlock tm enc out marked b =
      block b (payload tm enc out marked b) marked := by
    simpa [dataBlock,block,payload] using written_block tm enc dec hdec enc0 out marked b
  have hfn : Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm (encode tm enc) out =
      (fun b => block b (payload tm enc out false b) false) := by
    funext b
    simpa [dataBlock,Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock,
      Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft] using hblock false b
  rw [Shared.ComplexityBridge.TM2OutputCellLoop.markedCells_layout,hfn]
  change _ ++ dataBlock tm enc out true first = _
  rw [hblock true first]
  simp [blocks,cells,← List.map_reverse,List.flatMap_map]

def source (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program := Shared.ComplexityBridge.TM2OutputProtectedPipeline.source tm enc out

def stop (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := Shared.ComplexityBridge.TM2OutputProtectedPipeline.stop tm enc out

def program (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program :=
  Shared.Codes.FiniteProgramOneExit.program (source tm enc out)
    (Shared.ComplexityBridge.TM2OutputProtectedLoop.program width) (stop tm enc out)

def offset (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := Shared.Codes.FiniteProgramOneExit.offset (source tm enc out)

def emptyStop (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := Shared.ComplexityBridge.TM2OutputProtectedPipeline.emptyStop tm enc out

theorem program_valid (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : valid (program tm enc out) = true := by
  apply Shared.Codes.FiniteProgramOneExit.program_valid
  · exact Shared.ComplexityBridge.TM2OutputFirstCell.program_valid tm (encode tm enc) out
  · exact Shared.ComplexityBridge.TM2OutputProtectedLoop.program_valid width
  · exact Shared.ComplexityBridge.TM2OutputProtectedPipeline.stop_bound tm enc out

theorem program_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : (program tm enc out).length = 13*width+72 := by
  simp [program,source,Shared.Codes.FiniteProgramOneExit.program_length,
    Shared.Codes.FiniteProgramOneExit.offset,Shared.ComplexityBridge.TM2OutputProtectedPipeline.source,
    Shared.ComplexityBridge.TM2OutputFirstCell.program_length,
    Shared.ComplexityBridge.TM2OutputProtectedLoop.program_length]
  omega

def cost (width count : Nat) : Nat :=
  Shared.ComplexityBridge.TM2OutputProtectedPipeline.writerCost width count +
    (2+((width+4)+(count*(width+5)+(width+3))))

theorem cost_from_output_length (width : Nat) (bits : List Bool) (first : Bool) (bs : List Bool)
    (hrev : bits.reverse = first::bs) :
    cost width bs.length = bits.length*(2*width+12)+2*width+9 := by
  have hl : bits.length = bs.length+1 := by
    have h := congrArg List.length hrev
    simpa using h
  rw [hl]
  simp [cost,Shared.ComplexityBridge.TM2OutputProtectedPipeline.writerCost]
  ring

/-- Empty output is not redirected into the nonempty scan. -/
theorem empty_placeholder (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape) :
    step (program tm enc out) (emptyStop tm enc out,t) = some (.inl false) := by
  let p := source tm enc out
  let q := Shared.ComplexityBridge.TM2OutputProtectedLoop.program width
  let e := stop tm enc out
  let z := emptyStop tm enc out
  have hz : z < p.length := Shared.ComplexityBridge.TM2OutputProtectedPipeline.emptyStop_bound tm enc out
  have hne : z ≠ e := empty_nonempty_state_ne tm enc out
  have h := Shared.Codes.FiniteProgramTwoExit.source_other p q e e (z,t) hz hne hne
  change step p (z,t) = step (program tm enc out) (z,t) at h
  rw [← h]
  exact Shared.ComplexityBridge.TM2OutputFirstCell.empty_placeholder tm (encode tm enc) out t

/-- The actual empty halted-output tape reaches its own placeholder, even
after the nonempty all-block scanner is attached. -/
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
  let q := Shared.ComplexityBridge.TM2OutputProtectedLoop.program width
  let e := stop tm enc out
  have hp : valid p = true := Shared.ComplexityBridge.TM2OutputFirstCell.program_valid tm (encode tm enc) out
  have hp0 : 0 < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  obtain ⟨u,hu,hurel⟩ := Shared.ComplexityBridge.TM2OutputFirstCell.run_actual_empty
    tm (encode tm enc) (decode tm dec) (decode_encode tm enc dec hdec) out t ht
  have hpre := Shared.Codes.FiniteProgramOneExit.first_entry p q e (0,t)
    (emptyStop tm enc out,u) ((width+3)+2) hp hp0
      (Shared.ComplexityBridge.TM2OutputProtectedPipeline.source_stop tm enc out) hu
  exact ⟨u,hpre,hurel⟩

/-- From the actual protected halted output tape, this one valid table
processes every output cell and reaches the retained marked block after the
explicit charged number of steps. It does not physically compact the output. -/
theorem run_nonempty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) (first : Bool) (bs : List Bool)
    (hrev : bits.reverse = first::bs) (t : Tape)
    (ht : Shared.ComplexityBridge.TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm (encode tm enc) (bits.map out.symm))) :
    ∃ t', run (program tm enc out) (0,t) (cost width bs.length) =
        some (.inr (offset tm enc out + ((width+4)+terminal width first true),t')) ∧
      TapeRel t' (tapeLeft [] ((block first (payload tm enc out true first) true).reverse ++
        (blocks (cells tm enc out bs.reverse)).reverse ++ List.replicate (width+3) false ++ [false])) := by
  let p := source tm enc out
  let q := Shared.ComplexityBridge.TM2OutputProtectedLoop.program width
  let e := stop tm enc out
  let xs := cells tm enc out bs.reverse
  let lastPayload := payload tm enc out true first
  have hp : valid p = true := Shared.ComplexityBridge.TM2OutputFirstCell.program_valid tm (encode tm enc) out
  have hq : valid q = true := Shared.ComplexityBridge.TM2OutputProtectedLoop.program_valid width
  have hp0 : 0 < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  have hq0 : 0 < q.length := Shared.Codes.FiniteProgramLink.valid_nonempty q hq
  have he : e < p.length := Shared.ComplexityBridge.TM2OutputProtectedPipeline.stop_bound tm enc out
  have hstop : ∀ tape, step p (e,tape) = some (.inl false) :=
    Shared.ComplexityBridge.TM2OutputProtectedPipeline.source_stop tm enc out
  have hdec' := decode_encode tm enc dec hdec
  have henc0 := encode_blank tm enc enc0
  obtain ⟨u,hu,hurel⟩ := Shared.ComplexityBridge.TM2OutputFirstCell.run_actual_nonempty
    tm (encode tm enc) (decode tm dec) hdec' out henc0 bits first bs hrev t ht
  change run p (0,t) (Shared.ComplexityBridge.TM2OutputProtectedPipeline.writerCost width bs.length) =
    some (.inr (e,u)) at hu
  have hpre := Shared.Codes.FiniteProgramOneExit.first_entry p q e (0,t) (e,u)
    (Shared.ComplexityBridge.TM2OutputProtectedPipeline.writerCost width bs.length) hp hp0 hstop hu
  have hblank := Shared.ComplexityBridge.TM2OutputFirstCell.end_code_blank tm (encode tm enc) out henc0
  have hshape := sparse_layout tm enc dec hdec enc0 out first bs
  have hcanon : TapeRel u (tapeAt (List.replicate (width+3) false ++ blocks xs ++
      block first lastPayload true ++ []) []) := by
    simpa [consumed,hblank,hshape,xs,lastPayload,List.append_assoc] using hurel
  have hbounce : TapeRel (Shared.Codes.FiniteProgramThreeExit.bounce u)
      (tapeAt (List.replicate (width+3) false ++ blocks xs ++ block first lastPayload true ++ []) []) :=
    (Shared.Codes.FiniteProgramThreeExit.bounce_related u).trans hcanon
  obtain ⟨v,hscan,hv⟩ := Shared.ComplexityBridge.TM2OutputProtectedLoop.run_to_marked
    width xs (cells_length tm enc out bs.reverse) first lastPayload []
    (payload_length tm enc out true first) (Shared.Codes.FiniteProgramThreeExit.bounce u) hbounce
  have hhand := Shared.Codes.FiniteProgramOneExit.handoff p q e he u
  have hshift := Shared.Codes.FiniteProgramOneExit.continuation p q e hq
    (0,Shared.Codes.FiniteProgramThreeExit.bounce u) hq0
    ((width+4)+(xs.length*(width+5)+(width+3)))
  rw [hscan] at hshift
  refine ⟨v,?_,?_⟩
  · change run (Shared.Codes.FiniteProgramOneExit.program p q e) _ _ = _
    change run _ _ (Shared.ComplexityBridge.TM2OutputProtectedPipeline.writerCost width bs.length +
      (2+((width+4)+(bs.length*(width+5)+(width+3))))) = _
    rw [run_continue _ _ _ _ _ hpre,run_continue _ _ _ _ _ hhand]
    simpa [program,source,stop,offset,p,q,e,xs,cells,shiftConfig,shiftStatus] using hshift
  · simpa [xs,lastPayload,List.append_assoc] using hv

end Shared.ComplexityBridge.TM2OutputProtectedAllScan
