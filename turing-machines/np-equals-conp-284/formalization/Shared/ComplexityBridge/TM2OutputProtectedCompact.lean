import Shared.ComplexityBridge.TM2OutputProtectedAllScan
import Shared.Codes.FiniteProgramProtectedCompressLoop
import Shared.Codes.FiniteProgramRelink

/-! Link the protected halted-output writer to the finite protected-block
compactor. This reaches a tagged output buffer; final untagging, head
positioning, and replacing the empty and marked placeholders remain separate. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputProtectedCompact
open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramWriteWord (rewind rewind_word left_run)
open Shared.Codes.FiniteProgramProtectedScanLoop (block blocks)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramTaggedLoop (canonical)
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2OutputProtectedCodec
open Shared.ComplexityBridge.TM2OutputProtectedAllScan (payload cells payload_length cells_length sparse_layout)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def positioned (width : Nat) : Program :=
  link (Shared.ComplexityBridge.TM2OutputProtectedScan.positioning width)
    (Shared.Codes.FiniteProgramProtectedCompressLoop.program width) []

@[simp] theorem positioned_length (width : Nat) : (positioned width).length = 39*width+166 := by
  simp [positioned,link]
  omega

theorem positioned_valid (width : Nat) : valid (positioned width) = true := by
  apply Shared.Codes.FiniteProgramRelink.valid_relink
    (Shared.ComplexityBridge.TM2OutputProtectedScan.positioning width)
    (Shared.Codes.FiniteProgramProtectedScan.program width)
  · exact Shared.ComplexityBridge.TM2OutputProtectedScan.positioned_valid width
  · exact Shared.Codes.FiniteProgramProtectedCompressLoop.program_valid width
  · simp
    omega

/-- Explicit all-blank suffix lengths describe the same physical tape. -/
theorem blank_suffix (b : Bool) (L : List Bool) (n m : Nat) :
    TapeRel (tapeLeft (b::L) (List.replicate n false))
      (tapeLeft (b::L) (List.replicate m false)) := by
  have hn := Shared.ComplexityBridge.TM2OutputFirstCell.append_blanks L [] b n
  have hm := Shared.ComplexityBridge.TM2OutputFirstCell.append_blanks L [] b m
  simpa [tapeLeft,tapeAt,TapeRel] using hn.symm.trans hm

/-- One extra blank at the far left is only list padding, not tape content. -/
theorem left_append_blank (L R : List Bool) :
    TapeRel (tapeAt L R) (tapeAt (L++[false]) R) := by
  unfold TapeRel
  change (⟨R.head?.getD false,Turing.ListBlank.mk L,Turing.ListBlank.mk R.tail⟩ : Turing.Tape Bool) =
    ⟨R.head?.getD false,Turing.ListBlank.mk (L++[false]),Turing.ListBlank.mk R.tail⟩
  have h : Turing.ListBlank.mk L = Turing.ListBlank.mk (L++[false]) := by
    apply Quotient.sound
    exact Or.inl ⟨1,by simp⟩
  rw [h]

/-- The fixed positioning prefix crosses the blank terminator in `width+4`
physical transitions and enters the relocated compactor. -/
theorem position (width : Nat) (b : Bool) (L : List Bool) :
    run (positioned width) (0,tapeAt (List.replicate (width+3) false ++ b::L) []) (width+4) =
      some (.inr (width+4,tapeLeft (b::L) (List.replicate (width+3) false ++ [false]))) := by
  let blanks := List.replicate (width+3) false
  let traversed := b::blanks
  have hre := rewind_word traversed L false []
  have hpos : rewind (width+4) (tapeAt (blanks ++ b::L) []) =
      tapeLeft (b::L) (blanks ++ [false]) := by
    simpa [traversed,blanks,tapeAt,tapeLeft,List.reverse_cons,List.reverse_append,List.append_assoc] using hre
  have h := left_run []
    ((Shared.Codes.FiniteProgramProtectedCompressLoop.program width).map (shiftPair (width+4))) (width+4)
    (tapeAt (blanks ++ b::L) [])
  have hp : run (positioned width) (0,tapeAt (blanks ++ b::L) []) (width+4) =
      some (.inr (width+4,rewind (width+4) (tapeAt (blanks ++ b::L) []))) := by
    simpa [positioned,link,Shared.ComplexityBridge.TM2OutputProtectedScan.positioning,
      Shared.Codes.FiniteProgramWriteWord.leftRows_length] using h
  rw [hpos] at hp
  exact hp

theorem position_related (width : Nat) (b : Bool) (L : List Bool) (t : Tape)
    (ht : TapeRel t (tapeAt (List.replicate (width+3) false ++ b::L) [])) :
    ∃ u, run (positioned width) (0,t) (width+4) = some (.inr (width+4,u)) ∧
      TapeRel u (tapeLeft (b::L) (List.replicate (width+3) false ++ [false])) := by
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (positioned width) (0,t)
    (0,tapeAt (List.replicate (width+3) false ++ b::L) []) rfl ht (width+4)
  rw [position width b L] at h
  cases hr : run (positioned width) (0,t) (width+4) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨q,u⟩
      rw [hr] at h
      change q = width+4 ∧ _ at h
      refine ⟨u,?_,h.2⟩
      rw [h.1]

/-- Position, then physically compact all supplied protected blocks. The
extra `next` cell is a known part of the represented tape, not a detector. -/
theorem positioned_run (width : Nat) (before : List (Bool × List Bool))
    (hbefore : ∀ x ∈ before, x.2.length = width)
    (last next : Bool) (lastPayload L : List Bool) (hlast : lastPayload.length = width)
    (t : Tape) (ht : TapeRel t (tapeAt (List.replicate (width+3) false ++
      blocks before ++ block last lastPayload true ++ next::L) [])) :
    ∃ u, run (positioned width) (0,t)
        ((width+4)+Shared.Codes.FiniteProgramProtectedCompressLoop.totalCost width before []) =
        some (.inr ((width+4)+Shared.Codes.FiniteProgramProtectedCompressLoop.finish width true,u)) ∧
      TapeRel u (canonical L next (before.map Prod.fst ++ [last])).2 := by
  let sparse := blocks before ++ block last lastPayload true ++ next::L
  obtain ⟨b,rest,hsparse⟩ : ∃ b rest, sparse = b::rest := by
    cases before with
    | nil => exact ⟨last,lastPayload ++ [true,true] ++ next::L,by simp [sparse,blocks,block]⟩
    | cons x xs =>
      rcases x with ⟨b,word⟩
      exact ⟨b,word ++ [false,true] ++ blocks xs ++ block last lastPayload true ++ next::L,
        by simp [sparse,blocks,block,List.append_assoc]⟩
  have ht' : TapeRel t (tapeAt (List.replicate (width+3) false ++ b::rest) []) := by
    simpa [sparse,hsparse] using ht
  obtain ⟨u,hu,hurel⟩ := position_related width b rest t ht'
  have hpad : TapeRel (tapeLeft (b::rest) (List.replicate (width+3) false ++ [false]))
      (tapeLeft (b::rest) (false::tagged ([] : List Bool) ++ [false,false,false])) := by
    have h := blank_suffix b rest (width+4) 4
    have he : List.replicate (width+3) false ++ [false] = List.replicate (width+4) false := by
      simpa only [List.replicate_one,show width+3+1 = width+4 by omega] using
        (List.replicate_add (width+3) 1 false).symm
    simpa [he,tagged,TapeRel] using h
  have hloopinput : TapeRel u (tapeLeft (blocks before ++ block last lastPayload true ++ next::L)
      (false::tagged ([] : List Bool) ++ [false,false,false])) := by
    simpa [sparse,hsparse,TapeRel] using hurel.trans hpad
  obtain ⟨v,hv,hvrel⟩ := Shared.Codes.FiniteProgramProtectedCompressLoop.run_to_marked
    width before hbefore last next lastPayload L [] hlast u hloopinput
  have hshift := run_shift (Shared.ComplexityBridge.TM2OutputProtectedScan.positioning width)
    (Shared.Codes.FiniteProgramProtectedCompressLoop.program width) []
    (Shared.Codes.FiniteProgramProtectedCompressLoop.program_valid width) (0,u)
    (by simp) (Shared.Codes.FiniteProgramProtectedCompressLoop.totalCost width before [])
  rw [hv] at hshift
  refine ⟨v,?_,?_⟩
  · rw [run_continue _ _ _ _ _ hu]
    simpa [positioned,shiftConfig,shiftStatus] using hshift
  · simpa using hvrel

def source (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program := Shared.ComplexityBridge.TM2OutputProtectedPipeline.source tm enc out
def stop (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := Shared.ComplexityBridge.TM2OutputProtectedPipeline.stop tm enc out
def emptyStop (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := Shared.ComplexityBridge.TM2OutputProtectedPipeline.emptyStop tm enc out
def offset (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat := Shared.Codes.FiniteProgramOneExit.offset (source tm enc out)
def program (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Program :=
  Shared.Codes.FiniteProgramOneExit.program (source tm enc out) (positioned width) (stop tm enc out)
def finalStop (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : Nat :=
  offset tm enc out + ((width+4)+Shared.Codes.FiniteProgramProtectedCompressLoop.finish width true)

theorem program_valid (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : valid (program tm enc out) = true := by
  apply Shared.Codes.FiniteProgramOneExit.program_valid
  · exact Shared.ComplexityBridge.TM2OutputFirstCell.program_valid tm (encode tm enc) out
  · exact positioned_valid width
  · exact Shared.ComplexityBridge.TM2OutputProtectedPipeline.stop_bound tm enc out

theorem program_length (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) : (program tm enc out).length = 47*width+216 := by
  simp [program,source,Shared.Codes.FiniteProgramOneExit.offset,
    Shared.ComplexityBridge.TM2OutputProtectedPipeline.source,
    Shared.ComplexityBridge.TM2OutputFirstCell.program_length]
  omega

/-- The empty-output source placeholder is distinct from the relocated
marked-output placeholder; neither is an alias for the other path. -/
theorem empty_final_distinct (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) :
    emptyStop tm enc out ≠ finalStop tm enc out := by
  have h : emptyStop tm enc out < (source tm enc out).length :=
    Shared.ComplexityBridge.TM2OutputProtectedPipeline.emptyStop_bound tm enc out
  dsimp [finalStop,offset,Shared.Codes.FiniteProgramOneExit.offset]
  omega

def cost (width : Nat) (before : List (Bool × List Bool)) : Nat :=
  Shared.ComplexityBridge.TM2OutputProtectedPipeline.writerCost width before.length +
    (2+((width+4)+Shared.Codes.FiniteProgramProtectedCompressLoop.totalCost width before []))

theorem cost_bound (width : Nat) (before : List (Bool × List Bool)) :
    cost width before ≤ Shared.ComplexityBridge.TM2OutputProtectedPipeline.writerCost width before.length +
      (2+((width+4)+((before.length+1)*((10*width+36)*before.length+19*width+69)+2*before.length))) := by
  have h := Shared.Codes.FiniteProgramProtectedCompressLoop.totalCost_bound width before []
  simp only [List.length_nil,Nat.zero_add] at h
  dsimp [cost]
  omega

/-- Empty output remains a separate source placeholder. -/
theorem empty_placeholder (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape) :
    step (program tm enc out) (emptyStop tm enc out,t) = some (.inl false) := by
  let p := source tm enc out
  let q := positioned width
  let e := stop tm enc out
  let z := emptyStop tm enc out
  have hz : z < p.length := Shared.ComplexityBridge.TM2OutputProtectedPipeline.emptyStop_bound tm enc out
  have hne : z ≠ e := empty_nonempty_state_ne tm enc out
  have h := Shared.Codes.FiniteProgramTwoExit.source_other p q e e (z,t) hz hne hne
  change step p (z,t) = step (program tm enc out) (z,t) at h
  rw [← h]
  exact Shared.ComplexityBridge.TM2OutputFirstCell.empty_placeholder tm (encode tm enc) out t

/-- The nonempty path ends at an actual terminal placeholder in the linked
table. A later compiler must replace this row by final output cleanup. -/
theorem final_placeholder (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) (t : Tape) :
    step (program tm enc out) (finalStop tm enc out,t) = some (.inl false) := by
  let p := source tm enc out
  let q := positioned width
  let e := stop tm enc out
  let s := Shared.Codes.FiniteProgramProtectedCompressLoop.program width
  let f := Shared.Codes.FiniteProgramProtectedCompressLoop.finish width true
  have hs : valid s = true := Shared.Codes.FiniteProgramProtectedCompressLoop.program_valid width
  have hf : f < s.length := by
    have h := Shared.Codes.FiniteProgramProtectedCompressLoop.finish_bound width true
    dsimp [f,s,Shared.Codes.FiniteProgramProtectedCompressLoop.source,
      Shared.Codes.FiniteProgramProtectedCompressLoop.program] at *
    simp at *
    omega
  have hsource : run s (f,t) 1 = some (.inl false) := by
    simpa [s,f,run,advance] using Shared.Codes.FiniteProgramProtectedCompressLoop.marked_placeholder width t
  have hinner := run_shift (Shared.ComplexityBridge.TM2OutputProtectedScan.positioning width)
    s [] hs (f,t) hf 1
  rw [hsource] at hinner
  have hqrun : run q ((width+4)+f,t) 1 = some (.inl false) := by
    simpa [q,positioned,shiftConfig,shiftStatus] using hinner
  have hqbound : (width+4)+f < q.length := by
    dsimp [q,positioned,link]
    simp
    simpa [s] using hf
  have houter := Shared.Codes.FiniteProgramOneExit.continuation p q e (positioned_valid width)
    ((width+4)+f,t) hqbound 1
  rw [hqrun] at houter
  simpa [program,finalStop,offset,p,q,e,f,run,advance,shiftConfig,shiftStatus] using houter

/-- The actual empty halted-output tape reaches its separate placeholder. -/
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
  let q := positioned width
  let e := stop tm enc out
  have hp : valid p = true := Shared.ComplexityBridge.TM2OutputFirstCell.program_valid tm (encode tm enc) out
  have hp0 : 0 < p.length := Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  obtain ⟨u,hu,hurel⟩ := Shared.ComplexityBridge.TM2OutputFirstCell.run_actual_empty
    tm (encode tm enc) (decode tm dec) (decode_encode tm enc dec hdec) out t ht
  have hpre := Shared.Codes.FiniteProgramOneExit.first_entry p q e (0,t)
    (emptyStop tm enc out,u) ((width+3)+2) hp hp0
      (Shared.ComplexityBridge.TM2OutputProtectedPipeline.source_stop tm enc out) hu
  exact ⟨u,hpre,hurel⟩

/-- The protected writer and compactor form one valid table: on an actual
nonempty halted output, they reach the marked placeholder with the output bits
in a tagged buffer, charging both setup and every compaction transition. -/
theorem run_nonempty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) (first : Bool) (bs : List Bool)
    (hrev : bits.reverse = first::bs) (t : Tape)
    (ht : Shared.ComplexityBridge.TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm (encode tm enc) (bits.map out.symm))) :
    ∃ t', run (program tm enc out) (0,t) (cost width (cells tm enc out bs.reverse)) =
        some (.inr (finalStop tm enc out,t')) ∧
      TapeRel t' (canonical [] false bits).2 := by
  let p := source tm enc out
  let q := positioned width
  let e := stop tm enc out
  let xs := cells tm enc out bs.reverse
  let lastPayload := payload tm enc out true first
  have hp : valid p = true := Shared.ComplexityBridge.TM2OutputFirstCell.program_valid tm (encode tm enc) out
  have hq : valid q = true := positioned_valid width
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
  have hpad := left_append_blank (List.replicate (width+3) false ++ blocks xs ++ block first lastPayload true) []
  have hbounce : TapeRel (Shared.Codes.FiniteProgramThreeExit.bounce u)
      (tapeAt (List.replicate (width+3) false ++ blocks xs ++ block first lastPayload true ++ false::[]) []) := by
    exact (Shared.Codes.FiniteProgramThreeExit.bounce_related u).trans
      (hcanon.trans (by simpa [List.append_assoc,TapeRel] using hpad))
  obtain ⟨v,hcompact,hv⟩ := positioned_run width xs (cells_length tm enc out bs.reverse)
    first false lastPayload [] (payload_length tm enc out true first)
    (Shared.Codes.FiniteProgramThreeExit.bounce u) hbounce
  have hhand := Shared.Codes.FiniteProgramOneExit.handoff p q e he u
  have hshift := Shared.Codes.FiniteProgramOneExit.continuation p q e hq
    (0,Shared.Codes.FiniteProgramThreeExit.bounce u) hq0
    ((width+4)+Shared.Codes.FiniteProgramProtectedCompressLoop.totalCost width xs [])
  rw [hcompact] at hshift
  have hbits : bs.reverse ++ [first] = bits := by
    have h := congrArg List.reverse hrev
    simpa using h.symm
  have hxs : xs.length = bs.length := by simp [xs,cells]
  have hmap : xs.map Prod.fst = bs.reverse := by simp [xs,cells,List.map_map,Function.comp_def]
  refine ⟨v,?_,?_⟩
  · change run (Shared.Codes.FiniteProgramOneExit.program p q e) _ _ = _
    change run _ _ (Shared.ComplexityBridge.TM2OutputProtectedPipeline.writerCost width xs.length +
      (2+((width+4)+Shared.Codes.FiniteProgramProtectedCompressLoop.totalCost width xs []))) = _
    rw [hxs]
    rw [run_continue _ _ _ _ _ hpre,run_continue _ _ _ _ _ hhand]
    simpa [program,source,stop,finalStop,offset,p,q,e,xs,cells,shiftConfig,shiftStatus] using hshift
  · rw [hmap,hbits] at hv
    exact hv

end Shared.ComplexityBridge.TM2OutputProtectedCompact
