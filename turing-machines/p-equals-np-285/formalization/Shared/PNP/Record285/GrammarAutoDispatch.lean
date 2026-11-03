import Shared.PNP.Record285.GrammarLeafDispatch

/-! Dispatch directly from an arbitrary finite numeric tape at the root.
The grammar consumes a positive, bounded prefix, preserving both tails. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar
open Shared.Beeping.Machines
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch

def leafDestinationAny (row : Row 285) (pre : List Bool) (marker : Bool) :
    SymbolicDispatch.Config :=
  let left := pre.reverse ++ rootLeft
  match row.move with
  | .left => ⟨row.next,-2,left.tail,left.headD false,[row.write,marker]⟩
  | .right => ⟨row.next,0,row.write::left,marker,[]⟩

theorem append_bit_any (q : Fin 285) (head : Int) (pre : List Bool)
    (b marker : Bool) (left : List Bool) :
    rightWord q head (pre++[b]) marker left [] = rightWord q head pre b left [marker] := by
  cases pre <;> simp [rightWord,List.append_assoc]

theorem leaf_step_any (pre : List Bool) (parent : Nat) (bit marker : Bool) (row : Row 285)
    (hrow : NumericTables.target.table.row (state parent) bit = row)
    (hbeep : row.beep = false) :
    SymbolicDispatch.step ⟨state parent,-1,pre.reverse++rootLeft,bit,[marker]⟩ =
      some (leafDestinationAny row pre marker) := by
  cases row with
  | mk write move next beep =>
    simp only at hbeep
    subst beep
    cases move with
    | right => simp [SymbolicDispatch.step,hrow,leafDestinationAny]
    | left =>
      cases hl : pre.reverse++rootLeft with
      | nil =>
        have hn : pre.reverse++rootLeft ≠ [] := by simp [rootLeft]
        contradiction
      | cons x xs => simp [SymbolicDispatch.step,hrow,leafDestinationAny,hl]

theorem root_leaf_symbolic_any (code : List Bool) (marker : Bool) (e : Edge)
    (hwalk : walk rootIndex code = some e) :
    ∃ pre bit row, code = pre++[bit] ∧ expected e bit = some row ∧
      run code.length (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) =
        some (leafDestinationAny row pre marker) := by
  obtain ⟨pre,bit,parent,row,hcode,hroute,_,hexpected,hrow⟩ :=
    root_final_edge code e (by simpa only [rootIndex] using hwalk)
  have hnum : NumericTables.target.table.row (state parent) bit = row := by
    rw [← ArtifactEndpoint.literal_rows]
    exact hrow
  have hs := route_scan pre treeRoot (state parent) hroute (-(code.length:Int)) bit rootLeft [marker]
  have hhead : -(code.length:Int)+(pre.length:Int) = -1 := by
    rw [hcode]
    simp only [List.length_append,List.length_singleton,Int.natCast_add,Int.natCast_one]
    omega
  rw [hhead] at hs
  have hlast := leaf_step_any pre parent bit marker row hnum (expected_unmarked e bit row hexpected)
  refine ⟨pre,bit,row,hcode,hexpected,?_⟩
  rw [hcode,append_bit_any]
  have hlen : (pre++[bit]).length = pre.length+1 := by simp
  rw [hcode,hlen] at hs
  rw [hlen,run_add,hs]
  simp only [Option.bind_some,run,hlast,Option.bind_some]

/-- The actual successive low bits and the retained suffix of a numeric tape. -/
def dropTape : Nat → Nat → Nat
  | 0,w => w
  | n+1,w => dropTape n (w/2)

def tapeStream (w : Nat) (pos : Nat) : Bool := (dropTape pos w).testBit 0

theorem dropTape_add (a b w : Nat) : dropTape (a+b) w = dropTape b (dropTape a w) := by
  induction a generalizing w with
  | zero => simp [dropTape]
  | succ a ih => simpa only [Nat.succ_add,dropTape] using ih (w/2)

theorem window_tape_shift (w pos n : Nat) :
    window (tapeStream w) (pos+1) n = window (tapeStream (w/2)) pos n := by
  induction n generalizing pos with
  | zero => rfl
  | succ n ih =>
    simp only [window,tapeStream,dropTape]
    congr 1
    simpa only [Nat.add_assoc] using ih (pos+1)

theorem tape_decompose (n w : Nat) :
    bits (window (tapeStream w) 0 n) (dropTape n w) = w := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    have hwindow : window (tapeStream w) 1 n = window (tapeStream (w/2)) 0 n := by
      simpa using window_tape_shift w 0 n
    simp only [window,hwindow,dropTape,bits,ih,tapeStream]
    rw [Nat.testBit_zero]
    by_cases hm : w % 2 = 1 <;> simp [hm,bitVal] <;> omega

theorem bits_append (a b : List Bool) (tail : Nat) :
    bits (a++b) tail = bits a (bits b tail) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [bits,ih]

theorem tape_decompose_marker (n w : Nat) :
    w = bits (window (tapeStream w) 0 n)
      (bitVal (tapeStream w n) + 2 * dropTape (n+1) w) := by
  have hd : dropTape (n+1) w = dropTape n w / 2 := by
    rw [dropTape_add]
    rfl
  have hbit : bitVal (tapeStream w n) + 2 * (dropTape n w / 2) = dropTape n w := by
    simp only [tapeStream,Nat.testBit_zero]
    by_cases hm : dropTape n w % 2 = 1 <;> simp [hm,bitVal] <;> omega
  rw [hd,hbit]
  exact (tape_decompose n w).symm

theorem root_tape_repr (code : List Bool) (marker : Bool) (w : Nat)
    (head : Int) (leftTail suffix : Nat) (hne : code ≠ [])
    (hw : w = bits code (bitVal marker + 2 * suffix)) :
    (⟨treeRoot,head,bits rootLeft leftTail,w.testBit 0,w/2⟩ : PhysicalNumeric.Config 285) =
      denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft [])
        (head+code.length) leftTail suffix := by
  cases code with
  | nil => contradiction
  | cons b bs =>
    have hread : w.testBit 0 = b := by
      rw [hw]
      exact bits_read b bs (bitVal marker + 2 * suffix)
    have hright : w/2 = bits (bs++[marker]) suffix := by
      rw [hw]
      rw [bits_drop,bits_append]
      rfl
    simp only [rightWord,denote,List.length_cons,Int.natCast_succ,hread,hright]
    congr 1 <;> omega

/-- The root representation produced by preceding instruction contracts has
the numeric layout required by `root_actual_tape_dispatch`, even for an
empty explicit word and either marker bit. -/
theorem root_word_repr (word : List Bool) (marker : Bool) (head : Int)
    (leftTail suffix : Nat) :
    let w := bits (word++[marker]) suffix
    (⟨treeRoot,head,bits rootLeft leftTail,w.testBit 0,w/2⟩ : PhysicalNumeric.Config 285) =
      denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [])
        (head+word.length) leftTail suffix := by
  dsimp only
  cases word with
  | nil =>
    cases marker <;>
      simp [rightWord,denote,bits,bitVal,Nat.testBit_zero] <;> omega
  | cons b bs =>
    apply root_tape_repr (b::bs) marker (bits ((b::bs)++[marker]) suffix)
      head leftTail suffix (by simp)
    rw [bits_append]
    rfl

/-- From any numeric tape at the clean root, the actual bits select a grammar
leaf and the literal machine reaches it after 1–163 unmarked steps. The
destination includes the entire preserved tape, including its high suffix. -/
theorem root_actual_tape_dispatch (w : Nat) (head : Int) (leftTail : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel ⟨treeRoot,head,bits rootLeft leftTail,w.testBit 0,w/2⟩ physical) :
    ∃ e len pre bit row, 0 < len ∧ len ≤ 163 ∧ isLeaf e = true ∧
      window (tapeStream w) 0 len = pre++[bit] ∧ expected e bit = some row ∧
      Rel (denote (leafDestinationAny row pre (tapeStream w len)) (head+len)
        leftTail (dropTape (len+1) w))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run len) ∧
      (∀ t, t < len →
        ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) := by
  obtain ⟨e,len,hpos,hbound,hleaf,hwalk⟩ := root_walk_terminates (tapeStream w) 0
  let code := window (tapeStream w) 0 len
  have hlen : code.length = len := window_length (tapeStream w) 0 len
  have hne : code ≠ [] := by intro h; simp [h] at hlen; omega
  have hw : w = bits code (bitVal (tapeStream w len) + 2 * dropTape (len+1) w) :=
    tape_decompose_marker len w
  have hrepr := root_tape_repr code (tapeStream w len) w head leftTail (dropTape (len+1) w) hne hw
  have hwalk' : walk rootIndex code = some e := by simpa only [rootIndex] using hwalk
  obtain ⟨pre,bit,row,hcode,hexpected,hs⟩ := root_leaf_symbolic_any code (tapeStream w len) e hwalk'
  have hn := run_sound code.length _ _ hs (head+len) leftTail (dropTape (len+1) w)
  have hrel'' : Rel (denote (rightWord treeRoot (-(code.length:Int)) code (tapeStream w len) rootLeft [])
      (head+code.length) leftTail (dropTape (len+1) w)) physical := hrepr ▸ hrel
  have hrel' : Rel (denote (rightWord treeRoot (-(code.length:Int)) code (tapeStream w len) rootLeft [])
      (head+len) leftTail (dropTape (len+1) w)) physical := by
    simpa only [hlen] using hrel''
  have hp := silent_physical Record285.machine _ physical hrel' _ _ hn
  exact ⟨e,len,pre,bit,row,hpos,hbound,hleaf,hcode,hexpected,by simpa [hlen] using hp.1,
    by simpa [hlen] using hp.2⟩

/-- Explicit right-hand cells can be absorbed into the numeric suffix without
changing any cell of the represented tape. -/
theorem root_word_tail (word : List Bool) (marker : Bool) (right : List Bool)
    (origin : Int) (leftTail suffix : Nat) :
    denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft right)
      origin leftTail suffix =
    denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [])
      origin leftTail (bits right suffix) := by
  cases word <;> simp [rightWord,denote,bits_append,bits]

/-- The same progress result applies directly to a returned symbolic root,
with either marker, any explicit right cells and arbitrary retained suffix. -/
theorem root_word_dispatch (word : List Bool) (marker : Bool) (head : Int)
    (right : List Bool) (leftTail suffix : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft right)
      (head+word.length) leftTail suffix) physical) :
    let w := bits (word++[marker]) (bits right suffix)
    ∃ e len pre bit row, 0 < len ∧ len ≤ 163 ∧ isLeaf e = true ∧
      window (tapeStream w) 0 len = pre++[bit] ∧ expected e bit = some row ∧
      Rel (denote (leafDestinationAny row pre (tapeStream w len)) (head+len)
        leftTail (dropTape (len+1) w))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run len) ∧
      (∀ t, t < len →
        ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) := by
  dsimp only
  apply root_actual_tape_dispatch
  rw [root_word_repr]
  rw [root_word_tail word marker right (head+word.length) leftTail suffix] at hrel
  exact hrel

end Shared.PNP.Record285.Grammar
