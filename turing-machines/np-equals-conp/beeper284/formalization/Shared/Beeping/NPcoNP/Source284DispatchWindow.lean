import Shared.Beeping.NPcoNP.Source284CertificateDispatch
import Shared.Beeping.NPcoNP.Source284SATGrammarCharacterization

/-! Connect the executable SAT window predicate to the finite source-table
validator. The table begins already facing the certificate; initialization,
verifier handoff, and polynomial construction remain separate. -/
namespace Shared.Beeping.NPcoNP.Source284DispatchWindow

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack stack_value)
open Shared.Beeping.NPcoNP.Source284CanonicalPairWindow (window window_length window_value)
open Shared.Beeping.NPcoNP.Source284PairPrefixLoader (pairPrefix)
open Shared.Beeping.NPcoNP.Source284SATGrammarCharacterization (validWindow)
open Shared.Beeping.NPcoNP.Source284CertificateDispatch
open Shared.Beeping.NPcoNP.Source284CertificateGrammar (scanState next_lt)

/-- The finite window and its remaining high tail reconstruct every numeric
certificate, including virtual zeroes and arbitrary unscanned high bits. -/
theorem stack_window (width certificate : Nat) :
    stack (window width certificate) (certificate / 2^width) = certificate := by
  rw [stack_value, window_length, window_value]
  exact Nat.div_add_mod certificate (2^width)

/-- A certificate passing the actual SAT window predicate is accepted by the
validator, and the timed rewind preserves the whole certificate. -/
theorem valid_window_rewinds (x : List Bool) (width certificate codeTail : Nat)
    (hvalid : validWindow x width certificate = true) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    Shared.Beeping.NPcoNP.Source284Relative.run
      (encode (allocated (pairPrefix x) suffix.length)
        (table (pairPrefix x) suffix.length) codeTail)
      (toSource ⟨0, certificate, some 0⟩)
      (2*width+2) =
      toSource ⟨0, certificate, some (handoff (pairPrefix x) suffix.length)⟩ := by
  have hspec : (window width certificate).take (pairPrefix x).length = pairPrefix x ∧
      (Shared.Beeping.NPcoNP.Source284CertificateGrammar.scanState 0
          ((window width certificate).drop (pairPrefix x).length) = 0 ∨
       Shared.Beeping.NPcoNP.Source284CertificateGrammar.scanState 0
          ((window width certificate).drop (pairPrefix x).length) = 3) := by
    exact of_decide_eq_true hvalid
  let suffix := (window width certificate).drop (pairPrefix x).length
  have hsplit : pairPrefix x ++ suffix = window width certificate := by
    rw [← hspec.1]
    exact List.take_append_drop _ _
  have hlen : (pairPrefix x).length + suffix.length = width := by
    have h := congrArg List.length hsplit
    simpa [window_length] using h
  have hstack : stack (pairPrefix x ++ suffix) (certificate / 2^width) = certificate := by
    rw [hsplit, stack_window]
  have hrun := source_matching_rewind (pairPrefix x) suffix (certificate / 2^width)
    codeTail hspec.2
  rw [hstack] at hrun
  rw [hlen] at hrun
  exact hrun

/-- The grammar always stays within its five defined modes. -/
theorem scanState_lt (q : Nat) (bits : List Bool) (hq : q < 5) :
    scanState q bits < 5 := by
  induction bits generalizing q with
  | nil => simpa [scanState] using hq
  | cons b bs ih => exact ih _ (next_lt q b)

/-- Equal-length unequal prefixes have a first differing bit. -/
theorem first_difference (xs ys : List Bool) (hlen : xs.length = ys.length)
    (hne : xs ≠ ys) :
    ∃ before after observed want actual,
      xs = before ++ want :: after ∧ ys = before ++ actual :: observed ∧ actual ≠ want := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => exact False.elim (hne rfl)
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          by_cases hxy : x = y
          · subst y
            have hl : xs.length = ys.length := by simpa using hlen
            have hn : xs ≠ ys := by intro he; subst ys; exact hne rfl
            obtain ⟨before,after,observed,want,actual,hx,hy,hd⟩ := ih ys hl hn
            refine ⟨x::before,after,observed,want,actual,?_,?_,hd⟩ <;> simp [hx,hy]
          · exact ⟨[],xs,ys,x,y,rfl,rfl,Ne.symm hxy⟩

/-- With a matching prefix, a malformed finite grammar suffix reaches the
permanent nonaccepting sink after at most one further transition. -/
theorem invalid_grammar_rejects (x : List Bool) (width certificate extra : Nat)
    (hprefix : (window width certificate).take (pairPrefix x).length = pairPrefix x)
    (h0 : scanState 0 ((window width certificate).drop (pairPrefix x).length) ≠ 0)
    (h3 : scanState 0 ((window width certificate).drop (pairPrefix x).length) ≠ 3) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    (run (table (pairPrefix x) suffix.length) ⟨0,certificate,some 0⟩
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
  have hr := rejected_after_scan (pairPrefix x) suffix 0 (certificate / 2^width)
    (scanState_lt 0 suffix (by omega)) h0 h3
  rw [hstack, hlen] at hr
  have hs := sink_forever (pairPrefix x) suffix.length
    (run (table (pairPrefix x) suffix.length) ⟨0,certificate,some 0⟩ (width+1)) extra hr
  rw [← Shared.Beeping.NPcoNP.Source284CertificateValidator.run_add] at hs
  exact hs

/-- A mismatched public prefix reaches the same permanent reject sink. -/
theorem invalid_prefix_rejects (x : List Bool) (width certificate extra : Nat)
    (hwidth : (pairPrefix x).length ≤ width)
    (hbad : (window width certificate).take (pairPrefix x).length ≠ pairPrefix x) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    (run (table (pairPrefix x) suffix.length) ⟨0,certificate,some 0⟩
      (width+1+extra)).state = some (sink (pairPrefix x) suffix.length) := by
  let pref := (window width certificate).take (pairPrefix x).length
  let suffix := (window width certificate).drop (pairPrefix x).length
  have hl : (pairPrefix x).length = pref.length := by
    simp [pref, window_length, Nat.min_eq_left hwidth]
  obtain ⟨before,after,observed,want,actual,hexp,hobs,hdiff⟩ :=
    first_difference (pairPrefix x) pref hl (Ne.symm hbad)
  have hsplit : pref ++ suffix = window width certificate :=
    List.take_append_drop _ _
  have hstack : stack (before ++ actual :: (observed ++ suffix))
      (certificate / 2^width) = certificate := by
    have ha : before ++ actual :: (observed ++ suffix) = (before ++ actual :: observed) ++ suffix := by
      simp [List.append_assoc]
    rw [ha]
    rw [← hobs, hsplit, stack_window]
  have hm := first_mismatch before after (observed ++ suffix) suffix.length
    want actual hdiff 0 (certificate / 2^width)
  rw [← hexp, hstack] at hm
  have hbound : before.length + 1 ≤ width+1+extra := by
    have hh := congrArg List.length hexp
    simp only [List.length_append, List.length_cons] at hh
    omega
  have hr := sink_forever (pairPrefix x) suffix.length
    (run (table (pairPrefix x) suffix.length) ⟨0,certificate,some 0⟩
      (before.length+1)) (width+1+extra-(before.length+1)) hm
  rw [← Shared.Beeping.NPcoNP.Source284CertificateValidator.run_add] at hr
  have ht : before.length+1+(width+1+extra-(before.length+1)) = width+1+extra := by omega
  rwa [ht] at hr

/-- Every failed SAT window test reaches the permanent nonaccepting sink.
This uses the same window predicate as the mathematical SAT characterization. -/
theorem invalid_window_rejects (x : List Bool) (width certificate extra : Nat)
    (hwidth : (pairPrefix x).length ≤ width)
    (hbad : validWindow x width certificate = false) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    (run (table (pairPrefix x) suffix.length) ⟨0,certificate,some 0⟩
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
    exact invalid_grammar_rejects x width certificate extra hp
      (fun h => hm (Or.inl h)) (fun h => hm (Or.inr h))
  · exact invalid_prefix_rejects x width certificate extra hwidth hp

/-- The same rejection holds for the encoded source evaluator, including
all steps after it first reaches the reject sink. -/
theorem source_invalid_window_rejects
    (x : List Bool) (width certificate extra codeTail : Nat)
    (hwidth : (pairPrefix x).length ≤ width)
    (hbad : validWindow x width certificate = false) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    (Shared.Beeping.NPcoNP.Source284Relative.run
      (encode (allocated (pairPrefix x) suffix.length)
        (table (pairPrefix x) suffix.length) codeTail)
      (toSource ⟨0,certificate,some 0⟩) (width+1+extra)).state =
        active (sink (pairPrefix x) suffix.length) := by
  let suffix := (window width certificate).drop (pairPrefix x).length
  have hv : Valid (allocated (pairPrefix x) suffix.length) ⟨0,certificate,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    simp [allocated,sink,handoff,rewindStart,Source284CertificateDispatch.width]
  change (Shared.Beeping.NPcoNP.Source284Relative.run
    (encode (allocated (pairPrefix x) suffix.length)
      (table (pairPrefix x) suffix.length) codeTail)
    (toSource ⟨0,certificate,some 0⟩) (width+1+extra)).state =
      active (sink (pairPrefix x) suffix.length)
  rw [run_toSource (allocated (pairPrefix x) suffix.length)
    (table (pairPrefix x) suffix.length) codeTail _ (closed _ _) hv]
  have hr := invalid_window_rejects x width certificate extra hwidth hbad
  change (run (table (pairPrefix x) suffix.length) ⟨0,certificate,some 0⟩
    (width+1+extra)).state = some (sink (pairPrefix x) suffix.length) at hr
  change nextState (run (table (pairPrefix x) suffix.length) ⟨0,certificate,some 0⟩
    (width+1+extra)).state = active (sink (pairPrefix x) suffix.length)
  rw [hr]
  rfl

/-- The finite source table reaches its rewind handoff exactly for the
certificates accepted by the SAT window predicate. -/
theorem source_handoff_iff_valid_window
    (x : List Bool) (width certificate codeTail : Nat)
    (hwidth : (pairPrefix x).length ≤ width) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    (Shared.Beeping.NPcoNP.Source284Relative.run
      (encode (allocated (pairPrefix x) suffix.length)
        (table (pairPrefix x) suffix.length) codeTail)
      (toSource ⟨0,certificate,some 0⟩) (2*width+2)).state =
        active (handoff (pairPrefix x) suffix.length) ↔
      validWindow x width certificate = true := by
  constructor
  · intro hstate
    cases hv : validWindow x width certificate with
    | true => rfl
    | false =>
        have hr := source_invalid_window_rejects x width certificate (width+1) codeTail hwidth hv
        have ht : width+1+(width+1) = 2*width+2 := by omega
        rw [ht] at hr
        dsimp only at hr
        rw [hstate] at hr
        simp only [active, sink] at hr
        omega
  · intro hv
    have hr := valid_window_rewinds x width certificate codeTail hv
    exact congrArg (fun c : Shared.Beeping.NPcoNP.Source284Relative.Config => c.state) hr

end Shared.Beeping.NPcoNP.Source284DispatchWindow
