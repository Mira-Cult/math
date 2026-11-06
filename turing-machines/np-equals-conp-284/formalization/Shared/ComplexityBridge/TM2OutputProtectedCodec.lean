import Shared.ComplexityBridge.TM2OutputFirstCell

/-! A strengthened finite fixed-width codec with two protected bits and a
separate final bit reserved for the output writer. Occupied and marked tags
remain intact after write-back. It is an alternate codec, not a proof of the
physical compactor or of the corresponding input wrapper. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2OutputProtectedCodec
open Turing
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2OutputCellCompare
open Shared.ComplexityBridge.TM2OutputCellClassify

/-- The occupancy flag is computed from the finite encoded word. -/
def occupied (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (a : Alphabet tm) : Bool := (enc a).toList != List.replicate width false

def word (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (a : Alphabet tm) : List Bool := occupied tm enc a :: a.1 :: ((enc a).toList ++ [false])

/-- Payload bits remain unchanged; the last false bit is reserved for
write-back, and the first two bits are occupancy and the original marker. -/
def encode (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (a : Alphabet tm) : List.Vector Bool (width+3) :=
  ⟨word tm enc a, by simp [word]⟩

/-- The decoder reads the old finite payload and ignores the two tags and the
reserved bit. It is total even on malformed words. -/
def decode (tm : FinTM2) {width : Nat} (dec : List.Vector Bool width → Alphabet tm)
    (v : List.Vector Bool (width+3)) : Alphabet tm :=
  dec ⟨(v.toList.drop 2).take width, by
    have hv : v.toList.length = width+3 := List.Vector.toList_length v
    simp only [List.length_take,List.length_drop,hv]
    omega⟩

theorem decode_encode (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (a : Alphabet tm) :
    decode tm dec (encode tm enc a) = a := by
  have hword : ((word tm enc a).drop 2).take width = (enc a).toList := by
    simp [word]
  have hv : (⟨((encode tm enc a).toList.drop 2).take width, by
      have h : (encode tm enc a).toList.length = width+3 := List.Vector.toList_length _
      simp only [List.length_take,List.length_drop,h]; omega⟩ : List.Vector Bool width) = enc a := by
    apply Subtype.ext
    exact hword
  change dec _ = a
  rw [hv]
  exact hdec a

theorem encode_blank (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width)
    (enc0 : enc default = List.Vector.replicate width false) :
    encode tm enc default = List.Vector.replicate (width+3) false := by
  have hocc : occupied tm enc default = false := by
    unfold occupied
    rw [enc0]
    change (List.replicate width false != List.replicate width false) = false
    simp
  apply List.Vector.toList_injective
  change word tm enc default = List.replicate (width+3) false
  unfold word
  rw [hocc,enc0]
  change (false :: false :: (List.replicate width false ++ [false])) =
    List.replicate (width+3) false
  rw [show width+3 = 2+(width+1) by omega,List.replicate_add]
  simp [List.replicate_succ]
  have hrep (n : Nat) : List.replicate n false ++ [false] = false :: List.replicate n false := by
    induction n with
    | zero => rfl
    | succ k ih => simpa [List.replicate_succ] using congrArg (List.cons false) ih
  exact hrep width

/-- Every actual nonblank alphabet symbol has an occupied tag. -/
theorem occupied_of_ne_blank (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (a : Alphabet tm) (ha : a ≠ default) : occupied tm enc a = true := by
  have hn : (enc a).toList ≠ List.replicate width false := by
    intro h
    apply ha
    apply Shared.ComplexityBridge.TM2OutputCellCompare.encoded_injective tm enc dec hdec
    change (enc a).toList = (enc default).toList
    rw [enc0]
    exact h
  simp [occupied,hn]

/-- A data cell's two protected bits survive independently of its Boolean value. -/
theorem occupied_cell (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    occupied tm enc (cell tm out marked b) = true :=
  occupied_of_ne_blank tm enc dec hdec enc0 _ (cell_ne_blank tm out marked b)

/-- In nearest-first tape order, the written data bit is followed by the
original payload and finally the unchanged marker and occupied tags. -/
theorem written_block (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
      (code tm (encode tm enc) out marked (some b)) b [] =
      b :: ((enc (cell tm out marked b)).toList.reverse ++ [marked,true]) := by
  have ho := occupied_cell tm enc dec hdec enc0 out marked b
  change b :: ((occupied tm enc (cell tm out marked b) :: (cell tm out marked b).1 ::
    ((enc (cell tm out marked b)).toList ++ [false])).reverse.tail ++ []) = _
  rw [ho]
  simp [cell,List.reverse_append]

/-- Both boundary bits are still present after the destructive write. -/
theorem written_tags (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
      (code tm (encode tm enc) out marked (some b)) b []).drop (width+1) = [marked,true] := by
  rw [written_block tm enc dec hdec enc0 out marked b]
  simp [List.Vector.toList_length]

/-- A marked first block cannot be confused with an unmarked block after
write-back, even when their data bits or payloads agree. -/
theorem written_marked_ne_unmarked (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (b c : Bool) :
    Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
        (code tm (encode tm enc) out true (some b)) b [] ≠
      Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
        (code tm (encode tm enc) out false (some c)) c [] := by
  intro h
  have hh := congrArg (List.drop (width+1)) h
  rw [written_tags tm enc dec hdec enc0 out true b,
    written_tags tm enc dec hdec enc0 out false c] at hh
  contradiction

/-- A written block cannot disappear into an all-blank tape. -/
theorem written_ne_blank (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
        (code tm (encode tm enc) out marked (some b)) b [] ≠ List.replicate (width+3) false := by
  intro h
  have hh := congrArg (List.drop (width+1)) h
  rw [written_tags tm enc dec hdec enc0 out marked b] at hh
  have hzero : (List.replicate (width+3) false).drop (width+1) = [false,false] := by
    simp
  rw [hzero] at hh
  cases marked <;> contradiction

/-- Read one protected sparse block at a time, stopping only at its retained
first-cell marker. The fuel counts blocks; absent tags or exhausted fuel fail.
It does not validate the payload or the ignored suffix. -/
def recover (width : Nat) : Nat → List Bool → Option (List Bool)
  | 0, _ => none
  | fuel+1, xs =>
    match xs with
    | [] => none
    | bit::tail =>
      match tail.drop width with
      | marked::true::rest =>
        if marked then some [bit]
        else (recover width fuel rest).map (fun bits => bit::bits)
      | _ => none

theorem recover_one (width fuel : Nat) (b marked : Bool) (payload suffix : List Bool)
    (hlen : payload.length = width) :
    recover width (fuel+1) ((b::(payload ++ [marked,true])) ++ suffix) =
      if marked then some [b] else (recover width fuel suffix).map (fun bits => b::bits) := by
  have hd : (payload ++ ([marked,true] ++ suffix)).drop width = [marked,true] ++ suffix := by
    simp [hlen]
  simp only [List.cons_append,List.append_assoc,recover,List.nil_append] at *
  rw [hd]

def dataBlock (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) : List Bool :=
  Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
    (code tm (encode tm enc) out marked (some b)) b []

/-- The executable finite-word reader needs only one unit of fuel per block;
it does not receive the answer's length as semantic information. -/
theorem recover_blocks (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (xs : List Bool) (first : Bool) (L : List Bool)
    (fuel : Nat) (hfuel : xs.length+1 ≤ fuel) :
    recover width fuel (xs.flatMap (dataBlock tm enc out false) ++ dataBlock tm enc out true first ++ L) =
      some (xs ++ [first]) := by
  induction xs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      simp only [List.flatMap_nil,List.nil_append]
      rw [show dataBlock tm enc out true first =
          first :: ((enc (cell tm out true first)).toList.reverse ++ [true,true]) from
        written_block tm enc dec hdec enc0 out true first]
      rw [recover_one width fuel first true _ L (by simp)]
      rfl
  | cons x xs ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      have hf : xs.length+1 ≤ fuel := by simp at hfuel; omega
      simp only [List.flatMap_cons,List.cons_append]
      rw [show dataBlock tm enc out false x =
          x :: ((enc (cell tm out false x)).toList.reverse ++ [false,true]) from
        written_block tm enc dec hdec enc0 out false x]
      have hs := recover_one width fuel x false (enc (cell tm out false x)).toList.reverse
        (xs.flatMap (dataBlock tm enc out false) ++ dataBlock tm enc out true first ++ L) (by simp)
      simp only [Bool.false_eq_true,if_false,ih fuel hf,Option.map_some,List.cons_append] at hs
      simpa only [List.append_assoc,List.cons_append] using hs

/-- The length of each written protected block is fixed and positive. -/
theorem dataBlock_length (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (marked b : Bool) :
    (dataBlock tm enc out marked b).length = width+3 := by
  rw [dataBlock,written_block tm enc dec hdec enc0 out marked b]
  simp

/-- List length is a computable sufficient fuel bound; no witness for the
number of output bits is supplied to the reader. -/
theorem recover_blocks_length_fuel (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (xs : List Bool) (first : Bool) (L : List Bool) :
    let raw := xs.flatMap (dataBlock tm enc out false) ++ dataBlock tm enc out true first ++ L
    recover width raw.length raw = some (xs ++ [first]) := by
  let raw := xs.flatMap (dataBlock tm enc out false) ++ dataBlock tm enc out true first ++ L
  have hxs : xs.length ≤ (xs.flatMap (dataBlock tm enc out false)).length := by
    induction xs with
    | nil => simp
    | cons b bs ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,
        dataBlock_length tm enc dec hdec enc0 out false b]
      omega
  have hfirst := dataBlock_length tm enc dec hdec enc0 out true first
  have hfuel : xs.length+1 ≤ raw.length := by
    dsimp only [raw]
    simp only [List.length_append,hfirst]
    omega
  exact recover_blocks tm enc dec hdec enc0 out xs first L raw.length hfuel

/-- Recovery is unchanged by the finite tape's trailing-blank quotient. The
final occupied bit prevents the only marked block from being truncated. -/
theorem recover_blocks_blankRel (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (xs : List Bool) (first : Bool) (raw : List Bool)
    (hrel : Turing.BlankRel raw
      (xs.flatMap (dataBlock tm enc out false) ++ dataBlock tm enc out true first)) :
    recover width raw.length raw = some (xs ++ [first]) := by
  let ideal := xs.flatMap (dataBlock tm enc out false) ++ dataBlock tm enc out true first
  have hlast : ideal.reverse.head? = some true := by
    dsimp [ideal,dataBlock]
    rw [written_block tm enc dec hdec enc0 out true first]
    simp [List.reverse_append]
  change Turing.BlankRel raw ideal at hrel
  rcases hrel with ⟨n,hn⟩ | ⟨n,hn⟩
  · change ideal = raw ++ List.replicate n false at hn
    cases n with
    | zero =>
      simp only [List.replicate_zero,List.append_nil] at hn
      subst raw
      simpa [ideal] using recover_blocks_length_fuel tm enc dec hdec enc0 out xs first []
    | succ n =>
      rw [hn] at hlast
      simp [List.reverse_append,List.replicate_succ] at hlast
      cases n <;> simp [List.replicate_succ] at hlast
  · change raw = ideal ++ List.replicate n false at hn
    subst raw
    simpa [ideal,List.append_assoc] using
      recover_blocks_length_fuel tm enc dec hdec enc0 out xs first (List.replicate n false)

/-- The exact post-run sparse layout is recoverable without supplying the
output length: its own finite list length supplies the reader's fuel. This
theorem concerns a finite list representation, not a compiled physical reader. -/
theorem recover_actual_layout (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) (first : Bool) (bs L : List Bool)
    (hrev : bits.reverse = first::bs) :
    let raw := (Shared.ComplexityBridge.PairMarkedScanner.consumed
      (Shared.ComplexityBridge.TM2OutputCellLoop.markedCells tm (encode tm enc) out bs
        (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
          (code tm (encode tm enc) out true (some first)) first L))
      (code tm (encode tm enc) out false none)).drop (width+3)
    recover width raw.length raw = some bits := by
  have hbits : bs.reverse ++ [first] = bits := by
    have h := congrArg List.reverse hrev
    simpa using h.symm
  have hdrop : (code tm (encode tm enc) out false none).reverse.drop (width+3) = [] := by
    apply List.drop_eq_nil_of_le
    simp [code_length]
  dsimp only
  simp only [Shared.ComplexityBridge.PairMarkedScanner.consumed,List.drop_append,
    code_length,List.length_reverse,Nat.sub_self,hdrop,List.nil_append,List.drop_zero]
  rw [Shared.ComplexityBridge.TM2OutputCellLoop.markedCells_layout]
  have h := recover_blocks_length_fuel tm enc dec hdec enc0 out bs.reverse first L
  have hblocks : dataBlock tm enc out false =
      Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm (encode tm enc) out := by
    funext b
    simp [dataBlock,Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock,
      Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft]
  rw [hblocks] at h
  simpa [dataBlock,Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock,
    Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft,hbits] using h

/-- Dropping a fixed prefix respects the finite-tape blank quotient. -/
theorem blankRel_drop {xs ys : List Bool} (h : Turing.BlankRel xs ys) (n : Nat) :
    Turing.BlankRel (xs.drop n) (ys.drop n) := by
  induction n generalizing xs ys with
  | zero => simpa using h
  | succ n ih =>
    have hq : Turing.ListBlank.mk xs = Turing.ListBlank.mk ys := Quotient.sound h
    have ht := congrArg Turing.ListBlank.tail hq
    have htq : Turing.ListBlank.mk xs.tail = Turing.ListBlank.mk ys.tail := by
      simpa only [Turing.ListBlank.tail_mk] using ht
    have htail : Turing.BlankRel xs.tail ys.tail := Quotient.exact htq
    have hdrop (zs : List Bool) : zs.drop (n+1) = zs.tail.drop n := by
      cases zs <;> simp
    simpa only [hdrop] using ih htail

/-- On any physical list tape related to the completed sparse layout, the
executable list reader recovers the original nonempty output. -/
theorem recover_related_tape (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) (first : Bool) (bs : List Bool)
    (hrev : bits.reverse = first::bs) (t : Shared.Codes.FinitePrograms.Tape)
    (ht : Shared.Codes.FiniteProgramTapeEquiv.TapeRel t
      (Shared.ComplexityBridge.PairMarkedScanner.tapeAt
        (Shared.ComplexityBridge.PairMarkedScanner.consumed
          (Shared.ComplexityBridge.TM2OutputCellLoop.markedCells tm (encode tm enc) out bs
            (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
              (code tm (encode tm enc) out true (some first)) first []))
          (code tm (encode tm enc) out false none)) [])) :
    recover width (t.1.drop (width+3)).length (t.1.drop (width+3)) = some bits := by
  let sparse := Shared.ComplexityBridge.TM2OutputCellLoop.markedCells tm (encode tm enc) out bs
    (Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft
      (code tm (encode tm enc) out true (some first)) first [])
  let full := Shared.ComplexityBridge.PairMarkedScanner.consumed sparse (code tm (encode tm enc) out false none)
  have hq : Turing.ListBlank.mk t.1 = Turing.ListBlank.mk full := by
    have h := congrArg Turing.Tape.left ht
    exact h
  have hrel : Turing.BlankRel t.1 full := Quotient.exact hq
  have hdrop := blankRel_drop hrel (width+3)
  have hblank : (code tm (encode tm enc) out false none).reverse.drop (width+3) = [] := by
    apply List.drop_eq_nil_of_le
    simp [code_length]
  have hfull : full.drop (width+3) = sparse := by
    simp only [full,Shared.ComplexityBridge.PairMarkedScanner.consumed,List.drop_append,
      code_length,List.length_reverse,Nat.sub_self,hblank,List.nil_append,List.drop_zero]
  rw [hfull] at hdrop
  have hblocks : dataBlock tm enc out false =
      Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock tm (encode tm enc) out := by
    funext b
    simp [dataBlock,Shared.ComplexityBridge.TM2OutputCellLoop.markedBlock,
      Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft]
  have hsparse : sparse = bs.reverse.flatMap (dataBlock tm enc out false) ++ dataBlock tm enc out true first := by
    simp [sparse,Shared.ComplexityBridge.TM2OutputCellLoop.markedCells_layout,
      hblocks,dataBlock,Shared.ComplexityBridge.TM2OutputCellLoop.markedLeft]
  rw [hsparse] at hdrop
  have hbits : bs.reverse ++ [first] = bits := by
    have h := congrArg List.reverse hrev
    simpa using h.symm
  simpa [hbits] using recover_blocks_blankRel tm enc dec hdec enc0 out bs.reverse first
    (t.1.drop (width+3)) hdrop

/-- A real finite-table run starting at the protected halted output tape
leaves a physical list tape from which the total reader recovers all bits.
Compiling the reader and positioning the head remain separate obligations. -/
theorem physical_run_nonempty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (enc0 : enc default = List.Vector.replicate width false)
    (out : tm.Γ tm.k₁ ≃ Bool) (bits : List Bool) (first : Bool) (bs : List Bool)
    (hrev : bits.reverse = first::bs) (t : Shared.Codes.FinitePrograms.Tape)
    (ht : Shared.ComplexityBridge.TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm (encode tm enc) (bits.map out.symm))) :
    ∃ t', Shared.Codes.FinitePrograms.run
        (Shared.ComplexityBridge.TM2OutputFirstCell.program tm (encode tm enc) out) (0,t)
        (((width+3)+4) + (bs.length*((width+3)+4)+((width+3)+2))) =
      some (.inr (Shared.ComplexityBridge.TM2OutputFirstCell.offset tm (encode tm enc) out +
        Shared.ComplexityBridge.TM2OutputCellLoop.endExit tm (encode tm enc) out,t')) ∧
      recover width (t'.1.drop (width+3)).length (t'.1.drop (width+3)) = some bits := by
  have hdec' := decode_encode tm enc dec hdec
  have henc0 := encode_blank tm enc enc0
  obtain ⟨t',hr,hrel⟩ := Shared.ComplexityBridge.TM2OutputFirstCell.run_actual_nonempty
    tm (encode tm enc) (decode tm dec) hdec' out henc0 bits first bs hrev t ht
  exact ⟨t',hr,recover_related_tape tm enc dec hdec enc0 out bits first bs hrev t' hrel⟩

/-- The empty stack follows the separate marked-empty path with the protected
codec; its endpoint remains a placeholder for the later output phase. -/
theorem physical_run_empty (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (dec : List.Vector Bool width → Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (out : tm.Γ tm.k₁ ≃ Bool)
    (t : Shared.Codes.FinitePrograms.Tape)
    (ht : Shared.ComplexityBridge.TM0FiniteProgram.tape t = Turing.Tape.mk₁
      (Shared.ComplexityBridge.TM2BinaryOutputShape.outputBits tm (encode tm enc) ([] : List (tm.Γ tm.k₁)))) :
    ∃ t', Shared.Codes.FinitePrograms.run
        (Shared.ComplexityBridge.TM2OutputFirstCell.program tm (encode tm enc) out) (0,t)
        ((width+3)+2) =
      some (.inr (Shared.ComplexityBridge.TM2OutputFirstCell.firstExit tm (encode tm enc) out none,t')) ∧
      Shared.Codes.FiniteProgramTapeEquiv.TapeRel t'
        (Shared.ComplexityBridge.PairMarkedScanner.tapeAt
          (Shared.ComplexityBridge.PairMarkedScanner.consumed [] (code tm (encode tm enc) out true none)) []) :=
  Shared.ComplexityBridge.TM2OutputFirstCell.run_actual_empty tm (encode tm enc) (decode tm dec)
    (decode_encode tm enc dec hdec) out t ht

/-- Empty and nonempty runs reach different continuation states. -/
theorem empty_nonempty_state_ne (tm : FinTM2) {width : Nat}
    (enc : Alphabet tm → List.Vector Bool width) (out : tm.Γ tm.k₁ ≃ Bool) :
    Shared.ComplexityBridge.TM2OutputFirstCell.firstExit tm (encode tm enc) out none ≠
      Shared.ComplexityBridge.TM2OutputFirstCell.offset tm (encode tm enc) out +
        Shared.ComplexityBridge.TM2OutputCellLoop.endExit tm (encode tm enc) out := by
  have h : Shared.ComplexityBridge.TM2OutputFirstCell.firstExit tm (encode tm enc) out none <
      (Shared.ComplexityBridge.TM2OutputFirstCell.source tm (encode tm enc) out).length := by
    simp [Shared.ComplexityBridge.TM2OutputFirstCell.firstExit,
      Shared.ComplexityBridge.TM2OutputFirstCell.source,
      Shared.ComplexityBridge.TM2OutputCellRouter.routed,Shared.ComplexityBridge.TM2OutputCellRouter.exit]
  unfold Shared.ComplexityBridge.TM2OutputFirstCell.offset
  omega

end Shared.ComplexityBridge.TM2OutputProtectedCodec
