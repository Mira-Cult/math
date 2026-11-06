import Shared.Beeping.NPcoNP.Source284WitnessScanner
import Shared.Beeping.NPcoNP.Source284LoaderAlgebra
import Shared.Beeping.NPcoNP.Source284TransferInvolution

/-! A finite, unrolled source-relative table that visits exactly `width`
certificate cells, reverses and returns to the initial boundary. The table
preserves every scanned bit, the arbitrary high certificate tail, and the
empty opposite tape half. The final state is a continuing handoff; this is
not yet a syntax validator, a verifier wrapper, or a polynomial compiler. -/
namespace Shared.Beeping.NPcoNP.Source284WindowRewind

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (transfer)
open Shared.Beeping.NPcoNP.Source284WitnessScanner (lowbit_value)
open Shared.Beeping.NPcoNP.Source284TransferInvolution
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack transfer_stack pushed_eq_stack)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)

def handoff (width : Nat) : Nat := 2*width+3
def states (width : Nat) : Nat := handoff width + 1

/-- All scan steps preserve the read bit. Three designated control states
turn; after the handoff the table continues in the handoff state. -/
def table (width q : Nat) (b : Bool) : Row :=
  if q < handoff width then
    ⟨b, decide (q = 0 ∨ q = width+1 ∨ q = 2*width+2), some (q+1)⟩
  else ⟨b, false, some (handoff width)⟩

def straight (width q : Nat) : Prop :=
  q < handoff width ∧ q ≠ 0 ∧ q ≠ width+1 ∧ q ≠ 2*width+2

theorem table_closed (width : Nat) : Closed (states width) (table width) := by
  intro q hq b q' hnext
  unfold table at hnext
  split_ifs at hnext with h
  · simp only [Option.some.injEq] at hnext
    subst q'
    dsimp [states]
    omega
  · simp only [Option.some.injEq] at hnext
    subst q'
    simp [states]

theorem run_add (width : Nat) (c : Config) (a b : Nat) :
    run (table width) c (a+b) = run (table width) (run (table width) c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
      change step (table width) (run (table width) c (a+b)) =
        step (table width) (run (table width) (run (table width) c a) b)
      rw [ih]

theorem turn_step (width q left right : Nat) (hq : q < handoff width)
    (ht : q = 0 ∨ q = width+1 ∨ q = 2*width+2) :
    step (table width) ⟨left,right,some q⟩ = ⟨right,left,some (q+1)⟩ := by
  simp only [step, table, hq, ↓reduceIte, decide_eq_true_eq, ht]
  rw [lowbit_value]
  congr 1 <;> omega

theorem straight_step (width q left right : Nat) (h : straight width q) :
    step (table width) ⟨left,right,some q⟩ =
      ⟨2*left+right%2,right/2,some (q+1)⟩ := by
  rcases h with ⟨hq,h0,h1,h2⟩
  have ht : ¬ (q = 0 ∨ q = width+1 ∨ q = 2*width+2) := by tauto
  simp only [step, table, hq, ↓reduceIte, decide_eq_true_eq, ht]
  rw [lowbit_value]

theorem scan (width q count left right : Nat)
    (h : ∀ i < count, straight width (q+i)) :
    run (table width) ⟨left,right,some q⟩ count =
      ⟨(transfer count left right).1, (transfer count left right).2, some (q+count)⟩ := by
  induction count generalizing q left right with
  | zero => simp [run, transfer]
  | succ count ih =>
      have h0 : straight width q := by simpa using h 0 (by omega)
      have hn : ∀ i < count, straight width ((q+1)+i) := by
        intro i hi
        have := h (i+1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have hs := ih (q+1) (2*left+right%2) (right/2) hn
      have he : count+1 = 1+count := by omega
      rw [he, run_add]
      simp only [run]
      rw [straight_step width q left right h0]
      simpa [transfer, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

theorem forward_scan (width left right : Nat) :
    run (table width) ⟨left,right,some 1⟩ width =
      ⟨(transfer width left right).1,(transfer width left right).2,some (width+1)⟩ := by
  have h := scan width 1 width left right (by
    intro i hi
    dsimp [straight, handoff]
    omega)
  simpa [Nat.add_comm] using h

theorem backward_scan (width left right : Nat) :
    run (table width) ⟨left,right,some (width+2)⟩ width =
      ⟨(transfer width left right).1,(transfer width left right).2,
        some (2*width+2)⟩ := by
  have h := scan width (width+2) width left right (by
    intro i hi
    dsimp [straight, handoff]
    omega)
  have he : width+2+width = 2*width+2 := by omega
  simpa only [he] using h

/-- Generic preserving turn for a supplied finite-table row. -/
theorem generic_turn (t : Nat → Bool → Row) (q q' left right : Nat)
    (h : ∀ b, t q b = ⟨b,true,some q'⟩) :
    step t ⟨left,right,some q⟩ = ⟨right,left,some q'⟩ := by
  simp only [step, h, ↓reduceIte]
  rw [lowbit_value]
  congr 1 <;> omega

/-- Generic preserving scan row for a supplied finite table. -/
theorem generic_straight (t : Nat → Bool → Row) (q q' left right : Nat)
    (h : ∀ b, t q b = ⟨b,false,some q'⟩) :
    step t ⟨left,right,some q⟩ = ⟨2*left+right%2,right/2,some q'⟩ := by
  simp only [step, h, Bool.false_eq_true, ↓reduceIte]
  rw [lowbit_value]

theorem run_add_generic (t : Nat → Bool → Row) (c : Config) (a b : Nat) :
    run t c (a+b) = run t (run t c a) b := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
      change step t (run t c (a+b)) = step t (run t (run t c a) b)
      rw [ih]

/-- Exact preserving scan for any supplied consecutive rows satisfying the
stated row identities. No closure or code-generation hypothesis is hidden. -/
theorem generic_scan (t : Nat → Bool → Row) (q count left right : Nat)
    (h : ∀ i < count, ∀ b, t (q+i) b = ⟨b,false,some (q+i+1)⟩) :
    run t ⟨left,right,some q⟩ count =
      ⟨(transfer count left right).1,(transfer count left right).2,some (q+count)⟩ := by
  induction count generalizing q left right with
  | zero => simp [run, transfer]
  | succ count ih =>
      have h0 : ∀ b, t q b = ⟨b,false,some (q+1)⟩ := by
        intro b
        simpa using h 0 (by omega) b
      have hn : ∀ i < count, ∀ b,
          t ((q+1)+i) b = ⟨b,false,some ((q+1)+i+1)⟩ := by
        intro i hi b
        have hh := h (i+1) (by omega) b
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      have hs := ih (q+1) (2*left+right%2) (right/2) hn
      have he : count+1 = 1+count := by omega
      rw [he, run_add_generic]
      simp only [run]
      rw [generic_straight t q (q+1) left right h0]
      simpa [transfer, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

/-- Transfer a preserved reversed prefix back over an arbitrary unread high
tail. This includes prefixes ending in zeroes and an empty prefix. -/
theorem transfer_rewind (bits : List Bool) (tail : Nat) :
    transfer bits.length tail (payloadFold 0 bits) = (stack bits tail, 0) := by
  simpa [pushed_eq_stack] using transfer_stack bits.reverse tail 0

/-- A compositional boundary adapter: after a prior forward scan has pushed
`bits` onto the left half, a preserving turn, exactly `bits.length` scan
steps, and a second turn restore the entire certificate. The row identities
are explicit, so a later validator may instantiate them at its own offset. -/
theorem rewind_from_scanned (t : Nat → Bool → Row) (q tail : Nat) (bits : List Bool)
    (hfirst : ∀ b, t q b = ⟨b,true,some (q+1)⟩)
    (hscan : ∀ i < bits.length, ∀ b,
      t (q+1+i) b = ⟨b,false,some (q+1+i+1)⟩)
    (hlast : ∀ b, t (q+1+bits.length) b = ⟨b,true,some (q+1+bits.length+1)⟩) :
    run t ⟨payloadFold 0 bits,tail,some q⟩ (bits.length+2) =
      ⟨0,stack bits tail,some (q+bits.length+2)⟩ := by
  have hscan' := generic_scan t (q+1) bits.length tail (payloadFold 0 bits) hscan
  rw [transfer_rewind] at hscan'
  have hfirst' : run t ⟨payloadFold 0 bits,tail,some q⟩ 1 =
      ⟨tail,payloadFold 0 bits,some (q+1)⟩ := by
    simpa [run] using generic_turn t q (q+1) (payloadFold 0 bits) tail hfirst
  have hlast' : run t ⟨stack bits tail,0,some (q+1+bits.length)⟩ 1 =
      ⟨0,stack bits tail,some (q+1+bits.length+1)⟩ := by
    simpa [run] using generic_turn t _ _ _ _ hlast
  have ht : bits.length+2 = 1+bits.length+1 := by omega
  rw [ht, run_add_generic, run_add_generic, hfirst']
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    congrArg (fun c => run t c 1) hscan' |>.trans hlast'

/-- The first turn may dispatch to any scan-chain start, allowing several
accepted validator boundary states to share one rewind chain. -/
theorem rewind_from_scanned_jump (t : Nat → Bool → Row)
    (q start tail : Nat) (bits : List Bool)
    (hfirst : ∀ b, t q b = ⟨b,true,some start⟩)
    (hscan : ∀ i < bits.length, ∀ b,
      t (start+i) b = ⟨b,false,some (start+i+1)⟩)
    (hlast : ∀ b, t (start+bits.length) b = ⟨b,true,some (start+bits.length+1)⟩) :
    run t ⟨payloadFold 0 bits,tail,some q⟩ (bits.length+2) =
      ⟨0,stack bits tail,some (start+bits.length+1)⟩ := by
  have hscan' := generic_scan t start bits.length tail (payloadFold 0 bits) hscan
  rw [transfer_rewind] at hscan'
  have hfirst' : run t ⟨payloadFold 0 bits,tail,some q⟩ 1 =
      ⟨tail,payloadFold 0 bits,some start⟩ := by
    simpa [run] using generic_turn t q start (payloadFold 0 bits) tail hfirst
  have hlast' : run t ⟨stack bits tail,0,some (start+bits.length)⟩ 1 =
      ⟨0,stack bits tail,some (start+bits.length+1)⟩ := by
    simpa [run] using generic_turn t _ _ _ _ hlast
  have ht : bits.length+2 = 1+bits.length+1 := by omega
  rw [ht, run_add_generic, run_add_generic, hfirst']
  exact (congrArg (fun c => run t c 1) hscan').trans hlast'

/-- Starting with the entire certificate on the opposite tape half, the
unrolled table visits `width` cells and restores the complete certificate
as the positive half after exactly `2*width+3` source steps. -/
theorem rewind_run (width certificate : Nat) :
    run (table width) ⟨certificate,0,some 0⟩ (2*width+3) =
      ⟨0,certificate,some (handoff width)⟩ := by
  let p := transfer width 0 certificate
  have h1 : run (table width) ⟨certificate,0,some 0⟩ 1 = ⟨0,certificate,some 1⟩ := by
    simpa [run] using turn_step width 0 certificate 0 (by simp [handoff]) (by simp)
  have h2 : run (table width) ⟨0,certificate,some 1⟩ width =
      ⟨p.1,p.2,some (width+1)⟩ := by simpa [p] using forward_scan width 0 certificate
  have h3 : run (table width) ⟨p.1,p.2,some (width+1)⟩ 1 =
      ⟨p.2,p.1,some (width+2)⟩ := by
    simpa [run, Nat.add_assoc] using
      turn_step width (width+1) p.1 p.2 (by simp [handoff]; omega) (by simp)
  have hp : transfer width p.2 p.1 = (certificate,0) := by
    simpa [p] using transfer_involution width 0 certificate
  have h4 : run (table width) ⟨p.2,p.1,some (width+2)⟩ width =
      ⟨certificate,0,some (2*width+2)⟩ := by
    simpa [hp] using backward_scan width p.2 p.1
  have h5 : run (table width) ⟨certificate,0,some (2*width+2)⟩ 1 =
      ⟨0,certificate,some (handoff width)⟩ := by
    simpa [run, handoff] using
      turn_step width (2*width+2) certificate 0 (by simp [handoff]) (by simp)
  have ht : 2*width+3 = 1+width+1+width+1 := by omega
  rw [ht, run_add, run_add, run_add, run_add, h1, h2, h3, h4, h5]

/-- The encoded finite source table has the same exact run, for arbitrary
high table-code tail and arbitrary certificate. -/
theorem source_rewind_run (width certificate tail : Nat) :
    Source284Relative.run (encode (states width) (table width) tail)
      (Source284Relative.initial 0 certificate) (2*width+3) =
        ⟨0,certificate,active (handoff width)⟩ := by
  have hv : Valid (states width) ⟨certificate,0,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    simp [states, handoff]
  have hr := run_toSource (states width) (table width) tail
    ⟨certificate,0,some 0⟩ (table_closed width) hv (2*width+3)
  change Source284Relative.run (encode (states width) (table width) tail)
    (Source284Relative.initial 0 certificate) _ = _ at hr
  rw [hr, rewind_run]
  rfl

end Shared.Beeping.NPcoNP.Source284WindowRewind
