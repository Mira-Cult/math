import Shared.Beeping.NPcoNP.Source284ScratchWindowExact

/-! Exact amount of ignored input suffix consumed by the fixed paid
workspace passes. This does not provide polynomially many dynamic passes. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284WorkspaceSuffixCost
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284BitWindow
open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284RepeatWorkspace
open Shared.Beeping.NPcoNP.Source284RepeatWorkspaceSource
open Shared.Beeping.NPcoNP.Source284ScratchWindowExact
open Shared.Beeping.NPcoNP.Source284LengthGrowLoop (quarters)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)

theorem quarters_eq (n tail : Nat) : quarters n tail = tail/4^n := by
  induction n generalizing tail with
  | zero => simp [quarters]
  | succ n ih =>
    rw [quarters,ih,Nat.div_div_eq_div_mul,pow_succ]
    congr 1
    ring

theorem halves_eq (n tail : Nat) : halves n tail = tail/2^n := by
  induction n generalizing tail with
  | zero => simp [halves]
  | succ n ih =>
    rw [halves,ih,Nat.div_div_eq_div_mul,pow_succ]
    congr 1
    ring

/-- One paid pass consumes three suffix bits per payload bit, plus three. -/
theorem nextTail_eq (n tail : Nat) : nextTail n tail = tail/2^(3*(n+1)) := by
  rw [nextTail,halves_eq,quarters_eq]
  repeat rw [Nat.div_div_eq_div_mul]
  have hfour : 4^n = 2^(2*n) := by rw [pow_mul]; rfl
  rw [hfour]
  have hexp : 3*(n+1)=3+2*n+n := by ring
  rw [hexp,pow_add,pow_add]
  congr 1
  ring

/-- All `k` passes are compiled into the table; this formula identifies
exactly how many high input-suffix bits those fixed passes consume. -/
theorem iterateTail_eq (k n tail : Nat) :
    iterateTail k n tail = tail/2^(3*k*(n+1)) := by
  induction k generalizing tail with
  | zero => simp [iterateTail]
  | succ k ih =>
    rw [iterateTail,ih,nextTail_eq,Nat.div_div_eq_div_mul,← pow_add]
    congr 2
    ring

theorem retained_suffix_eq (k n suffix : Nat) :
    iterateTail k n ((suffix/4)/4) = suffix/2^(4+3*k*(n+1)) := by
  rw [iterateTail_eq]
  repeat rw [Nat.div_div_eq_div_mul]
  rw [pow_add]
  congr 1
  norm_num
  ring

/-- If the retained high quotients match, the post-loader scratch streams
match exactly; the already-proved negative-side runway then protects any
continuation within its full affine workspace bound. -/
theorem source_alias_window_of_suffix_quotient (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (firstCert secondCert firstSuffix secondSuffix clock radius : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hblank : radius+clock ≤ k*(3*(w.length+1)))
    (hquot : firstSuffix/2^(4+3*k*(w.length+1)) =
      secondSuffix/2^(4+3*k*(w.length+1))) :
    Window radius
      (Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w firstSuffix) firstCert)
        (elapsed k w+clock))
      (Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w secondSuffix) secondCert)
        (elapsed k w+clock)) := by
  apply source_alias_window_of_tail k states continuation w firstCert secondCert firstSuffix secondSuffix
    clock radius hn hv hblank
  rw [retained_suffix_eq,retained_suffix_eq,hquot]
  exact agree_refl _ _

/-- Exact input-suffix information still visible beyond the flipped frame,
after all `k` paid passes. -/
theorem retained_right_agree_iff (k : Nat) (w : List Bool) (firstSuffix secondSuffix depth : Nat) :
    Agree depth
      (2*Source284ScratchFlip.flipped (w++[false]) (iterateTail k w.length ((firstSuffix/4)/4)))
      (2*Source284ScratchFlip.flipped (w++[false]) (iterateTail k w.length ((secondSuffix/4)/4))) ↔
    Agree (depth-(2*(w.length+1)+3))
      (firstSuffix/2^(4+3*k*(w.length+1)))
      (secondSuffix/2^(4+3*k*(w.length+1))) := by
  rw [right_agree_iff,retained_suffix_eq,retained_suffix_eq]
  simp

/-- For every fixed number of passes, some ignored suffix survives just
beyond the protected frame. Thus a fixed pass count cannot make all numeric
aliases agree on that extra bit. -/
theorem no_uniform_retained_alias (k : Nat) (w : List Bool) :
    ∃ suffix : Nat,
      ¬ Agree (2*(w.length+1)+4)
        (2*Source284ScratchFlip.flipped (w++[false]) (iterateTail k w.length ((suffix/4)/4)))
        (2*Source284ScratchFlip.flipped (w++[false]) (iterateTail k w.length ((1/4)/4))) := by
  let exponent := 4+3*k*(w.length+1)
  refine ⟨2^exponent,?_⟩
  intro h
  have hh := (retained_right_agree_iff k w (2^exponent) 1 (2*(w.length+1)+4)).1 h
  have hsub : 2*(w.length+1)+4-(2*(w.length+1)+3)=1 := by omega
  have hp : 0 < 2^(3*k*(w.length+1)) := pow_pos (by decide) _
  have hlarge : 1 < 2^exponent := by
    dsimp [exponent]
    rw [pow_add]
    norm_num
    omega
  have hself : 2^exponent/2^exponent=1 := Nat.div_self (by omega)
  have hone : 1/2^exponent=0 := Nat.div_eq_of_lt hlarge
  change Agree (2*(w.length+1)+4-(2*(w.length+1)+3))
    (2^exponent/2^exponent) (1/2^exponent) at hh
  rw [hsub,hself,hone] at hh
  norm_num [Agree] at hh

/-- If the retained suffix has enough low zeros, an arbitrary original
suffix can be compared with the canonical suffix 1 for the whole specified
continuation window. The divisibility premise is the remaining explicit
input-side runway obligation. -/
theorem source_window_to_canonical (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (firstCert secondCert suffix clock radius : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hblank : radius+clock ≤ k*(3*(w.length+1)))
    (hclear : 2^(radius+clock-(2*(w.length+1)+3)) ∣
      suffix/2^(4+3*k*(w.length+1))) :
    Window radius
      (Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w suffix) firstCert)
        (elapsed k w+clock))
      (Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w 1) secondCert)
        (elapsed k w+clock)) := by
  apply source_alias_window_of_tail k states continuation w firstCert secondCert suffix 1 clock radius hn hv hblank
  rw [retained_suffix_eq,retained_suffix_eq]
  have hp : 0 < 2^(3*k*(w.length+1)) := pow_pos (by decide) _
  have hone : 1 / 2^(4+3*k*(w.length+1)) = 0 := by
    apply Nat.div_eq_of_lt
    rw [pow_add]
    norm_num
    omega
  rw [hone]
  exact Nat.mod_eq_zero_of_dvd hclear

end Shared.Beeping.NPcoNP.Source284WorkspaceSuffixCost
