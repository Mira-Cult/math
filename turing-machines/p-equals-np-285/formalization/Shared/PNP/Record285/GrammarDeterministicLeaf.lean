import Shared.PNP.Record285.GrammarExactDeterminism
import Shared.PNP.Record285.GrammarOperationalRun

/-! The chosen exact-action duration and bank update are deterministic. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarExact
open Shared.Beeping
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarReady
open Shared.PNP.Record285.GrammarOperationalRun

theorem tape_stream_bit (w pos : Nat) : tapeStream w pos = w.testBit pos := by
  induction pos generalizing w with
  | zero => rfl
  | succ pos ih =>
    change tapeStream (w/2) pos = w.testBit (pos+1)
    rw [ih,Nat.testBit_add_one]

theorem encoded_window (code : List Bool) (tail : Nat) :
    window (tapeStream (bits code tail)) 0 code.length = code := by
  induction code with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons,window]
    have hs := window_tape_shift (bits (b::bs) tail) 0 bs.length
    simp only [Nat.zero_add,bits_drop] at hs
    rw [hs,ih]
    simp only [tapeStream,dropTape,bits_read]

/-- A walk matching a finite input window is the result of the bounded
acyclic-grammar descent on that same stream. -/
theorem walk_descend (fuel n pos len : Nat) (input : Nat → Bool) (e : Edge)
    (hn : n < 163) (hf : n < fuel)
    (hw : walk n (window input pos len) = some e) :
    descend fuel n input pos = some (e,pos+len) := by
  induction fuel generalizing n pos len with
  | zero => omega
  | succ fuel ih =>
    cases len with
    | zero => simp [window,walk] at hw
    | succ len =>
      cases hnedge : nodeEdge n (input pos) with
      | none => simp [window,walk,hnedge] at hw
      | some found =>
        cases found with
        | node j =>
          have hj := node_edge_decreases n (input pos) j hn hnedge
          have hsub : walk j (window input (pos+1) len) = some e := by
            simpa only [window,walk,hnedge] using hw
          have hd := ih j (pos+1) len (by omega) (by omega) hsub
          have he : pos+1+len = pos+(len+1) := by omega
          simpa only [descend,hnedge,he] using hd
        | inc j =>
          cases len with
          | zero => simpa [window,walk,descend,hnedge] using hw
          | succ len => simp [window,walk,hnedge] at hw

        | dec j =>
          cases len with
          | zero => simpa [window,walk,descend,hnedge] using hw
          | succ len => simp [window,walk,hnedge] at hw
        | half j =>
          cases len with
          | zero => simpa [window,walk,descend,hnedge] using hw
          | succ len => simp [window,walk,hnedge] at hw
        | beep =>
          cases len with
          | zero => simpa [window,walk,descend,hnedge] using hw
          | succ len => simp [window,walk,hnedge] at hw
        | brk j =>
          cases len with
          | zero => simpa [window,walk,descend,hnedge] using hw
          | succ len => simp [window,walk,hnedge] at hw
        | cont j =>
          cases len with
          | zero => simpa [window,walk,descend,hnedge] using hw
          | succ len => simp [window,walk,hnedge] at hw


/-- Read the real physical cells starting at the fixed dispatcher root. -/
def physicalBits (rootHead : Int) (physical : Shared.Beeping.Machines.Config 285) (i : Nat) : Bool :=
  physical.tape (rootHead+i)

theorem zero_leaf_physical_bits (fields : List Nat) (rootHead anchor : Int) (e : Edge)
    (code : List Bool) (head : Int) (leftTail gap : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (h : ZeroLeaf fields rootHead anchor e code head leftTail gap physical) :
    physicalBits rootHead physical =
      tapeStream (bits (code++[false])
        (2*PhysicalSweeps.runPattern false gap true (2*IncrementSelector.blocksBits fields 0))) := by
  obtain ⟨_,hhead,_,hrel⟩ := h
  let tail := 2*PhysicalSweeps.runPattern false gap true (2*IncrementSelector.blocksBits fields 0)
  let w := bits (code++[false]) tail
  have hrepr := root_word_repr code false rootHead leftTail tail
  have hh : rootHead+code.length = head := by omega
  rw [hh] at hrepr
  have hn : Rel ⟨treeRoot,rootHead,bits rootLeft leftTail,w.testBit 0,w/2⟩ physical := by
    rw [hrepr]
    exact hrel
  have hp : physical.head = rootHead := hn.2.1.symm
  funext i
  cases i with
  | zero =>
    have ht := hn.2.2.1
    simpa [physicalBits,tape_stream_bit,hp] using ht
  | succ i =>
    have ht := hn.2.2.2.2 i
    change physical.tape (physical.head+(i:Int)+1) = (w/2).testBit i at ht
    simpa [physicalBits,tape_stream_bit,Nat.testBit_add_one,hp,Int.natCast_succ,Int.add_assoc] using ht

theorem zero_leaf_window (fields : List Nat) (rootHead anchor : Int) (e : Edge)
    (code : List Bool) (head : Int) (leftTail gap : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (h : ZeroLeaf fields rootHead anchor e code head leftTail gap physical) :
    window (physicalBits rootHead physical) 0 code.length = code := by
  rw [zero_leaf_physical_bits fields rootHead anchor e code head leftTail gap physical h]
  rw [bits_append]
  exact encoded_window code _

/-- The literal full tape uniquely determines the current grammar edge and
the length of its code, independently of the choice of a proof witness. -/
theorem zero_leaf_decodes (fields : List Nat) (rootHead anchor : Int) (e : Edge)
    (code : List Bool) (head : Int) (leftTail gap : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (h : ZeroLeaf fields rootHead anchor e code head leftTail gap physical) :
    descend 163 rootIndex (physicalBits rootHead physical) 0 = some (e,code.length) := by
  have hw : walk rootIndex (window (physicalBits rootHead physical) 0 code.length) = some e := by
    rw [zero_leaf_window fields rootHead anchor e code head leftTail gap physical h]
    exact h.1
  simpa only [rootIndex,Nat.zero_add] using
    walk_descend 163 162 0 code.length (physicalBits rootHead physical) e (by decide) (by decide) hw

theorem zero_leaf_unique (fields : List Nat) (rootHead anchor : Int)
    (e e' : Edge) (code code' : List Bool) (head head' : Int) (leftTail leftTail' gap gap' : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (h : ZeroLeaf fields rootHead anchor e code head leftTail gap physical)
    (h' : ZeroLeaf fields rootHead anchor e' code' head' leftTail' gap' physical) :
    e = e' ∧ code = code' ∧ head = head' ∧ gap = gap' := by
  have hd := zero_leaf_decodes fields rootHead anchor e code head leftTail gap physical h
  have hd' := zero_leaf_decodes fields rootHead anchor e' code' head' leftTail' gap' physical h'
  rw [hd] at hd'
  have he : e = e' ∧ code.length = code'.length := by
    simpa only [Option.some.injEq,Prod.mk.injEq] using hd'
  have hc := zero_leaf_window fields rootHead anchor e code head leftTail gap physical h
  have hc' := zero_leaf_window fields rootHead anchor e' code' head' leftTail' gap' physical h'
  rw [he.2] at hc
  have hcode : code = code' := hc.symm.trans hc'
  have hhead : head = head' := by
    have h₁ := h.2.1
    have h₂ := h'.2.1
    rw [hcode] at h₁
    omega
  have hgap : gap = gap' := by
    have h₁ := h.2.2.1
    have h₂ := h'.2.2.1
    rw [hhead] at h₁
    omega
  exact ⟨he.1,hcode,hhead,hgap⟩

/-- Classical witness selection does not change the literal edge, code,
exact duration or resulting bank of an operation. -/
theorem step_witness_unique (s : State) (a b : StepWitness s) :
    a.edge = b.edge ∧ a.code = b.code ∧ a.head = b.head ∧ a.gap = b.gap ∧
      a.duration = b.duration ∧ a.fields = b.fields := by
  obtain ⟨he,hcode,hhead,hgap⟩ := zero_leaf_unique s.fields (-3818) 3
    a.edge b.edge a.code b.code a.head b.head a.leftTail b.leftTail a.gap b.gap s.physical a.leaf b.leaf
  have hd := a.exactDuration
  rw [he,hcode,hgap] at hd
  have htime : a.duration = b.duration := duration_unique b.edge s.fields b.code b.gap
    a.duration b.duration hd b.exactDuration
  have hu := a.update
  rw [he] at hu
  have hfields : a.fields = b.fields := update_unique b.edge s.fields a.fields b.fields hu b.update
  exact ⟨he,hcode,hhead,hgap,htime,hfields⟩

/-- The actual tape selects the leaf; its bank update and duration can be
calculated without inspecting the chosen proof witness. -/
theorem operation_step_computable_data (n : Nat) :
    let s := operationSystem.run n
    let w := chooseStep s
    descend 163 rootIndex (physicalBits (-3818) s.physical) 0 = some (w.edge,w.code.length) ∧
    w.duration = durationFor w.edge s.fields w.code w.gap ∧
    (operationSystem.run (n+1)).fields = applyUpdate w.edge s.fields := by
  dsimp only
  let s := operationSystem.run n
  let w := chooseStep s
  have hl := zero_leaf_decodes s.fields (-3818) 3 w.edge w.code w.head w.leftTail w.gap s.physical w.leaf
  have hd := duration_sound w.edge s.fields w.code w.gap w.duration w.exactDuration
  have hu := update_sound w.edge s.fields w.fields w.update
  exact ⟨hl,hd.symm,hu.symm⟩

/-- At every selected boundary, the gap is fixed by the code length and
the certified absolute root and anchor coordinates. -/
theorem operation_step_gap (n : Nat) :
    let s := operationSystem.run n
    let w := chooseStep s
    w.code.length+w.gap = 3819 := by
  dsimp only
  let w := chooseStep (operationSystem.run n)
  have hh := w.leaf.2.1
  have ha := w.leaf.2.2.1
  change w.code.length+w.gap = 3819
  omega

theorem operation_step_code_from_tape (n : Nat) :
    let s := operationSystem.run n
    let w := chooseStep s
    window (physicalBits (-3818) s.physical) 0 w.code.length = w.code := by
  dsimp only
  let s := operationSystem.run n
  let w := chooseStep s
  exact zero_leaf_window s.fields (-3818) 3 w.edge w.code w.head w.leftTail w.gap s.physical w.leaf

end Shared.PNP.Record285.GrammarExact
