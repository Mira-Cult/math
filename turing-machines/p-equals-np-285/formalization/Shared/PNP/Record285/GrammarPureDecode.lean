import Shared.PNP.Record285.GrammarExactControlEffect

/-! Reading a bounded grammar prefix from the actual tape agrees with reading
the returned control word followed by virtual zeros, provided the actual tape
contains the proved blank margin before its bank anchor. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarPure
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarReady
open Shared.PNP.Record285.GrammarExact

def pureBits (control : List Bool) : Nat → Bool := tapeStream (bits control 0)

theorem window_take (input : Nat → Bool) (pos m n : Nat) (h : n ≤ m) :
    (window input pos m).take n = window input pos n := by
  induction n generalizing pos m with
  | zero => simp [window]
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [window,List.take_succ_cons]
      rw [ih (pos+1) m (by omega)]

/-- All first 163 grammar reads agree with the actual finite zero margin;
no virtual zero is used before establishing that those physical cells are zero. -/
theorem zero_margin_window (control : List Bool) (gap tail : Nat) (hgap : 163 ≤ gap) :
    window (tapeStream (bits control (2*runPattern false gap true tail))) 0 163 =
      window (pureBits control) 0 163 := by
  let rest := gap-163
  let suffix := 2*runPattern false rest true tail
  let common := control++List.replicate 163 false
  have heq : gap = 163+rest := by dsimp [rest]; omega
  have htail : 2*runPattern false gap true tail = bits (List.replicate 163 false) suffix := by
    rw [zeros_bits,heq,zeros_pattern]
    dsimp [suffix]
    ac_rfl
  have hw1 : bits control (2*runPattern false gap true tail) = bits common suffix := by
    rw [htail]
    exact (bits_append control (List.replicate 163 false) suffix).symm
  have hw2 : bits control 0 = bits common 0 := by
    change bits control 0 = bits (control++List.replicate 163 false) 0
    rw [bits_append]
    have hz := zeros_bits 163 0
    simp only [Nat.mul_zero] at hz
    rw [hz]
  have hlen : 163 ≤ common.length := by simp [common]
  have h1 := encoded_window common suffix
  have h2 := encoded_window common 0
  have ht1 := congrArg (List.take 163) h1
  have ht2 := congrArg (List.take 163) h2
  rw [window_take _ _ _ _ hlen] at ht1 ht2
  dsimp only [pureBits]
  rw [hw1,hw2]
  exact ht1.trans ht2.symm

/-- Every represented full numeric tape has the expected physical read stream. -/
theorem numeric_physical_stream (rootHead : Int) (q : Fin 285) (left w : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (h : Rel ⟨q,rootHead,left,w.testBit 0,w/2⟩ physical) :
    physicalBits rootHead physical = tapeStream w := by
  have hp : physical.head = rootHead := h.2.1.symm
  funext i
  cases i with
  | zero =>
    have ht := h.2.2.1
    simpa [physicalBits,tape_stream_bit,hp] using ht
  | succ i =>
    have ht := h.2.2.2.2 i
    change physical.tape (physical.head+(i:Int)+1) = (w/2).testBit i at ht
    simpa [physicalBits,tape_stream_bit,Nat.testBit_add_one,hp,Int.natCast_succ,Int.add_assoc] using ht

/-- A represented control prefix with a real blank margin has the same first
163 physical bits as its pure zero-padded encoding. -/
theorem represented_window (word : List Bool) (marker : Bool) (origin : Int)
    (leftTail gap bank : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hgap : 163 ≤ gap)
    (hrel : Rel (denote (rightWord treeRoot (-(word.length:Int)) word marker rootLeft [false])
      origin leftTail (runPattern false gap true (2*bank))) physical) :
    window (physicalBits physical.head physical) 0 163 = window (pureBits (word++[marker])) 0 163 := by
  let rootHead := origin-word.length
  let tail := bits [false] (runPattern false gap true (2*bank))
  let w := bits (word++[marker]) tail
  have hh : rootHead+word.length = origin := by dsimp [rootHead]; omega
  have hrepr := root_word_repr word marker rootHead leftTail tail
  rw [hh,← root_word_tail word marker [false]] at hrepr
  have hn : Rel ⟨treeRoot,rootHead,bits rootLeft leftTail,w.testBit 0,w/2⟩ physical := by
    rw [hrepr]
    exact hrel
  have hhead : physical.head = rootHead := hn.2.1.symm
  have hs := numeric_physical_stream rootHead treeRoot (bits rootLeft leftTail) w physical hn
  rw [hhead,hs]
  simpa [w,tail,bits,bitVal] using zero_margin_window (word++[marker]) gap (2*bank) hgap

/-- If two streams agree throughout the 163-cell dispatch window, the
checked terminating grammar descent returns exactly the same leaf and length. -/
theorem descend_window_congr (a b : Nat → Bool)
    (h : window a 0 163 = window b 0 163) :
    descend 163 rootIndex a 0 = descend 163 rootIndex b 0 := by
  obtain ⟨e,stop,hd,_,_,_⟩ := root_descend_terminates a 0
  obtain ⟨len,_,hlen,hstop,hwalk⟩ := descend_trace 163 162 a 0 e stop hd
  have htake := congrArg (List.take len) h
  rw [window_take a 0 163 len hlen,window_take b 0 163 len hlen] at htake
  rw [htake] at hwalk
  have hd' := walk_descend 163 162 0 len b e (by decide) (by decide) hwalk
  rw [hstop] at hd
  simpa only [rootIndex] using hd.trans hd'.symm

/-- Returned control determines the next actual physical leaf and its length. -/
theorem atControl_descend (control : List Bool) (fields : List Nat)
    (physical : Shared.Beeping.Machines.Config 285) (h : AtControl control fields physical) :
    descend 163 rootIndex (physicalBits physical.head physical) 0 =
      descend 163 rootIndex (pureBits control) 0 := by
  obtain ⟨word,origin,leftTail,gap,hcontrol,hgap,hrel⟩ := h
  subst control
  apply descend_window_congr
  exact represented_window word true origin leftTail gap (IncrementSelector.blocksBits fields 0)
    physical (by omega) hrel

end Shared.PNP.Record285.GrammarPure
