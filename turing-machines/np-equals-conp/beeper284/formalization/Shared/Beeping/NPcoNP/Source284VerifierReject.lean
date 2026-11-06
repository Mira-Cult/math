import Shared.Beeping.NPcoNP.Source284VerifierHandoff
import Shared.Beeping.NPcoNP.Source284DispatchWindow

/-! Rejection in the combined validator/verifier table. These lemmas still
start already facing the certificate. They do not establish a physical
machine refinement or a polynomial-time table generator. -/
namespace Shared.Beeping.NPcoNP.Source284VerifierReject

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (run_front)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284CertificatePrefix (stack_append)
open Shared.Beeping.NPcoNP.Source284CertificateGrammar (next next_lt scanState)
open Shared.Beeping.NPcoNP.Source284CertificateGrammarClock (state)
open Shared.Beeping.NPcoNP.Source284CertificateValidator (run_add boundary)
open Shared.Beeping.NPcoNP.Source284CertificateDispatch (handoff sink allocated rewindStart width)
open Shared.Beeping.NPcoNP.Source284VerifierHandoff (table validator_step)

theorem prefix_step (expected : List Bool) (clock q left tail : Nat)
    (verifier : Nat → Bool → Row) (hq : q < expected.length) (b : Bool) (rest : List Bool) :
    step (table expected clock verifier) ⟨left,stack (b::rest) tail,some q⟩ =
      ⟨2*left+(if b then 1 else 0),stack rest tail,
       some (if b = (expected[q]?).getD false then q+1 else sink expected clock)⟩ := by
  have hv : Valid (allocated expected clock) ⟨left,stack (b::rest) tail,some q⟩ := by
    intro r hr
    simp only [Option.some.injEq] at hr
    subst r
    simp [allocated,sink,handoff,rewindStart,width] at *
    omega
  have hn : (⟨left,stack (b::rest) tail,some q⟩ : Config).state ≠
      some (handoff expected clock) := by
    simp [handoff,rewindStart,width] at *
    omega
  rw [validator_step expected clock verifier _ hv hn]
  exact Source284CertificateDispatch.prefix_step expected clock q left tail hq b rest

theorem prefix_part (before part after : List Bool) (clock left tail : Nat)
    (verifier : Nat → Bool → Row) :
    run (table (before++part++after) clock verifier)
      ⟨left,stack part tail,some before.length⟩ part.length =
      ⟨payloadFold left part,tail,some (before.length+part.length)⟩ := by
  induction part generalizing before left with
  | nil => simp [run,payloadFold,stack]
  | cons b bs ih =>
    have hq : before.length < (before++(b::bs)++after).length := by simp
    have hbit : (((before++(b::bs)++after)[before.length]?).getD false) = b := by
      rw [show before++(b::bs)++after = before++((b::bs)++after) by simp [List.append_assoc]]
      rw [List.getElem?_append_right (by omega)]
      simp
    have hs := prefix_step (before++(b::bs)++after) clock before.length left tail verifier hq b bs
    rw [hbit] at hs
    simp only [↓reduceIte] at hs
    have hn := ih (before++[b]) (2*left+if b then 1 else 0)
    simp only [List.length_append,List.length_singleton] at hn
    rw [List.length_cons,run_front,hs]
    simpa [List.append_assoc,payloadFold,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn

theorem grammar_step (expected : List Bool) (clock i mode left tail : Nat)
    (verifier : Nat → Bool → Row) (hi : i < clock) (hm : mode < 5)
    (b : Bool) (rest : List Bool) :
    step (table expected clock verifier)
      ⟨left,stack (b::rest) tail,some (expected.length+state i mode)⟩ =
      ⟨2*left+(if b then 1 else 0),stack rest tail,
       some (expected.length+state (i+1) (next mode b))⟩ := by
  have hq : expected.length+state i mode < expected.length+5*clock := by
    have h := Source284CertificateGrammarClock.state_lt clock i mode hi hm
    omega
  have hv : Valid (allocated expected clock)
      ⟨left,stack (b::rest) tail,some (expected.length+state i mode)⟩ := by
    intro r hr
    simp only [Option.some.injEq] at hr
    subst r
    simp [allocated,sink,handoff,rewindStart,width] at *
    omega
  have hn : (⟨left,stack (b::rest) tail,some (expected.length+state i mode)⟩ : Config).state ≠
      some (handoff expected clock) := by
    simp [handoff,rewindStart,width] at *
    omega
  rw [validator_step expected clock verifier _ hv hn]
  exact Source284CertificateDispatch.grammar_step expected clock i mode left tail hi hm b rest

theorem grammar_scan (expected : List Bool) (clock i mode : Nat) (bits : List Bool)
    (left tail : Nat) (verifier : Nat → Bool → Row)
    (hb : i+bits.length ≤ clock) (hm : mode < 5) :
    run (table expected clock verifier)
      ⟨left,stack bits tail,some (expected.length+state i mode)⟩ bits.length =
      ⟨payloadFold left bits,tail,
        some (expected.length+state (i+bits.length) (scanState mode bits))⟩ := by
  induction bits generalizing i mode left with
  | nil => simp [run,payloadFold,stack,scanState]
  | cons b bs ih =>
    have hi : i < clock := by simp at hb; omega
    have hb' : i+1+bs.length ≤ clock := by simp at hb; omega
    rw [List.length_cons,run_front,grammar_step expected clock i mode left tail verifier hi hm b bs]
    have hh := ih (i+1) (next mode b) (2*left+if b then 1 else 0) hb' (next_lt mode b)
    simpa [payloadFold,scanState,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem matching_scan (expected bits : List Bool) (left tail : Nat)
    (verifier : Nat → Bool → Row) :
    run (table expected bits.length verifier)
      ⟨left,stack (expected++bits) tail,some 0⟩ (expected.length+bits.length) =
      ⟨payloadFold (payloadFold left expected) bits,tail,
        some (boundary expected bits.length (scanState 0 bits))⟩ := by
  have hp := prefix_part [] expected [] bits.length left (stack bits tail) verifier
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hp
  rw [stack_append,run_add,hp]
  have h := grammar_scan expected bits.length 0 0 bits (payloadFold left expected) tail verifier
    (by omega) (by omega)
  simpa [state,boundary] using h

theorem sink_row (expected : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (b : Bool) :
    table expected clock verifier (sink expected clock) b =
      ⟨b,false,some (sink expected clock)⟩ := by
  have hb : sink expected clock < allocated expected clock := by simp [allocated]
  have hn : sink expected clock ≠ handoff expected clock := by simp [sink]
  rw [Source284VerifierHandoff.validator_row expected clock verifier _ _ hb hn]
  exact Source284CertificateDispatch.sink_row expected clock b

theorem sink_forever (expected : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (c : Config) (k : Nat)
    (h : c.state = some (sink expected clock)) :
    (run (table expected clock verifier) c k).state = some (sink expected clock) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    cases hc : run (table expected clock verifier) c k with
    | mk left right state =>
      have hs : state = some (sink expected clock) := by simpa [hc] using ih
      subst state
      simp [run,hc,step,sink_row]

theorem first_mismatch (before after observed : List Bool) (clock : Nat)
    (verifier : Nat → Bool → Row) (want actual : Bool) (hbad : actual ≠ want)
    (left tail : Nat) :
    (run (table (before++want::after) clock verifier)
      ⟨left,stack (before++actual::observed) tail,some 0⟩ (before.length+1)).state =
        some (sink (before++want::after) clock) := by
  have hs := prefix_part [] before (want::after) clock left (stack (actual::observed) tail) verifier
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hs
  rw [stack_append,run,hs]
  have hq : before.length < (before++want::after).length := by simp
  have hbit : (((before++want::after)[before.length]?).getD false) = want := by
    rw [List.getElem?_append_right (by omega)]
    simp
  rw [prefix_step _ _ _ _ _ verifier hq actual observed,hbit]
  simp [hbad]

theorem rejected_after_scan (expected bits : List Bool) (left tail : Nat)
    (verifier : Nat → Bool → Row) (hm : scanState 0 bits < 5)
    (h0 : scanState 0 bits ≠ 0) (h3 : scanState 0 bits ≠ 3) :
    (run (table expected bits.length verifier)
      ⟨left,stack (expected++bits) tail,some 0⟩ (expected.length+bits.length+1)).state =
        some (sink expected bits.length) := by
  rw [run,matching_scan]
  have hb : boundary expected bits.length (scanState 0 bits) < allocated expected bits.length := by
    simp [boundary,state,allocated,sink,handoff,rewindStart,width] at *
    omega
  have hn : boundary expected bits.length (scanState 0 bits) ≠ handoff expected bits.length := by
    simp [boundary,state,handoff,rewindStart,width] at *
    omega
  simp [step,Source284VerifierHandoff.validator_row expected bits.length verifier _ _ hb hn,
    Source284CertificateDispatch.boundary_reject expected bits.length (scanState 0 bits) hm h0 h3]

open Shared.Beeping.NPcoNP.Source284CanonicalPairWindow (window window_length)
open Shared.Beeping.NPcoNP.Source284PairPrefixLoader (pairPrefix)
open Shared.Beeping.NPcoNP.Source284SATGrammarCharacterization (validWindow)
open Shared.Beeping.NPcoNP.Source284DispatchWindow (stack_window scanState_lt first_difference)

theorem invalid_grammar (x : List Bool) (width certificate extra : Nat)
    (verifier : Nat → Bool → Row)
    (hprefix : (window width certificate).take (pairPrefix x).length = pairPrefix x)
    (h0 : scanState 0 ((window width certificate).drop (pairPrefix x).length) ≠ 0)
    (h3 : scanState 0 ((window width certificate).drop (pairPrefix x).length) ≠ 3) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    (run (table (pairPrefix x) suffix.length verifier) ⟨0,certificate,some 0⟩
      (width+1+extra)).state = some (sink (pairPrefix x) suffix.length) := by
  let suffix := (window width certificate).drop (pairPrefix x).length
  have hsplit : pairPrefix x ++ suffix = window width certificate := by
    rw [← hprefix]
    exact List.take_append_drop _ _
  have hlen : (pairPrefix x).length + suffix.length = width := by
    have h := congrArg List.length hsplit
    simpa [window_length] using h
  have hstack : stack (pairPrefix x ++ suffix) (certificate / 2^width) = certificate := by
    rw [hsplit, stack_window]
  have hr := rejected_after_scan (pairPrefix x) suffix 0 (certificate / 2^width) verifier
    (scanState_lt 0 suffix (by omega)) h0 h3
  rw [hstack, hlen] at hr
  have hs := sink_forever (pairPrefix x) suffix.length verifier
    (run (table (pairPrefix x) suffix.length verifier) ⟨0,certificate,some 0⟩ (width+1)) extra hr
  rw [← run_add] at hs
  exact hs

theorem invalid_prefix (x : List Bool) (width certificate extra : Nat)
    (verifier : Nat → Bool → Row) (hwidth : (pairPrefix x).length ≤ width)
    (hbad : (window width certificate).take (pairPrefix x).length ≠ pairPrefix x) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    (run (table (pairPrefix x) suffix.length verifier) ⟨0,certificate,some 0⟩
      (width+1+extra)).state = some (sink (pairPrefix x) suffix.length) := by
  let pref := (window width certificate).take (pairPrefix x).length
  let suffix := (window width certificate).drop (pairPrefix x).length
  have hl : (pairPrefix x).length = pref.length := by
    simp [pref, window_length, Nat.min_eq_left hwidth]
  obtain ⟨before,after,observed,want,actual,hexp,hobs,hdiff⟩ :=
    first_difference (pairPrefix x) pref hl (Ne.symm hbad)
  have hsplit : pref ++ suffix = window width certificate := List.take_append_drop _ _
  have hstack : stack (before ++ actual :: (observed ++ suffix))
      (certificate / 2^width) = certificate := by
    have ha : before ++ actual :: (observed ++ suffix) = (before ++ actual :: observed) ++ suffix := by
      simp [List.append_assoc]
    rw [ha, ← hobs, hsplit, stack_window]
  have hm := first_mismatch before after (observed ++ suffix) suffix.length verifier
    want actual hdiff 0 (certificate / 2^width)
  rw [← hexp, hstack] at hm
  have hbound : before.length + 1 ≤ width+1+extra := by
    have hh := congrArg List.length hexp
    simp only [List.length_append, List.length_cons] at hh
    omega
  have hr := sink_forever (pairPrefix x) suffix.length verifier
    (run (table (pairPrefix x) suffix.length verifier) ⟨0,certificate,some 0⟩
      (before.length+1)) (width+1+extra-(before.length+1)) hm
  rw [← run_add] at hr
  have ht : before.length+1+(width+1+extra-(before.length+1)) = width+1+extra := by omega
  rwa [ht] at hr

/-- Failed windows enter the permanent sink even after linking an arbitrary
verifier, so malformed certificates cannot reach that continuation. -/
theorem invalid_window (x : List Bool) (width certificate extra : Nat)
    (verifier : Nat → Bool → Row) (hwidth : (pairPrefix x).length ≤ width)
    (hbad : validWindow x width certificate = false) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    (run (table (pairPrefix x) suffix.length verifier) ⟨0,certificate,some 0⟩
      (width+1+extra)).state = some (sink (pairPrefix x) suffix.length) := by
  by_cases hp : (window width certificate).take (pairPrefix x).length = pairPrefix x
  · have hm : ¬ (scanState 0 ((window width certificate).drop (pairPrefix x).length) = 0 ∨
        scanState 0 ((window width certificate).drop (pairPrefix x).length) = 3) := by
      intro hgood
      have ht : validWindow x width certificate = true := by
        unfold validWindow
        exact decide_eq_true ⟨hp,hgood⟩
      rw [hbad] at ht
      contradiction
    exact invalid_grammar x width certificate extra verifier hp
      (fun h => hm (Or.inl h)) (fun h => hm (Or.inr h))
  · exact invalid_prefix x width certificate extra verifier hwidth hp

/-- The linked table's bounded acceptance is precisely the conjunction of
the window predicate and the verifier's bounded acceptance. The verifier is
given a positive number of steps, and all validator steps are charged. -/
theorem combined_acceptance (x : List Bool) (width certificate fuel : Nat)
    (verifier : Nat → Bool → Row) (hwidth : (pairPrefix x).length ≤ width) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    (run (table (pairPrefix x) suffix.length verifier) ⟨0,certificate,some 0⟩
      ((2*width+2)+(fuel+1))).state.isNone =
      (validWindow x width certificate &&
        (run verifier ⟨0,certificate,some 0⟩ (fuel+1)).state.isNone) := by
  let suffix := (window width certificate).drop (pairPrefix x).length
  cases hv : validWindow x width certificate with
  | false =>
      have hr := invalid_window x width certificate (width+1+(fuel+1)) verifier hwidth hv
      have ht : width+1+(width+1+(fuel+1)) = (2*width+2)+(fuel+1) := by omega
      rw [ht] at hr
      change (run (table (pairPrefix x) suffix.length verifier) ⟨0,certificate,some 0⟩
        ((2*width+2)+(fuel+1))).state = some (sink (pairPrefix x) suffix.length) at hr
      change (run (table (pairPrefix x) suffix.length verifier) ⟨0,certificate,some 0⟩
        ((2*width+2)+(fuel+1))).state.isNone = false
      rw [hr]
      rfl
  | true =>
      have hspec : (window width certificate).take (pairPrefix x).length = pairPrefix x ∧
          (scanState 0 suffix = 0 ∨ scanState 0 suffix = 3) := of_decide_eq_true hv
      have hsplit : pairPrefix x ++ suffix = window width certificate := by
        rw [← hspec.1]
        exact List.take_append_drop _ _
      have hlen : (pairPrefix x).length + suffix.length = width := by
        have h := congrArg List.length hsplit
        simpa [window_length] using h
      have hstack : stack (pairPrefix x ++ suffix) (certificate / 2^width) = certificate := by
        rw [hsplit, stack_window]
      have hr := Source284VerifierHandoff.validator_then_verifier (pairPrefix x) suffix
        (certificate / 2^width) verifier fuel hspec.2
      dsimp only at hr
      rw [hstack,hlen] at hr
      dsimp only
      rw [hr]
      simp [hv, Source284HardwireTable.shiftConfig]

end Shared.Beeping.NPcoNP.Source284VerifierReject
