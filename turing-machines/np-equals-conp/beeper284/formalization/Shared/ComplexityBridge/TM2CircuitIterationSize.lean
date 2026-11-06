import Shared.ComplexityBridge.TM2CircuitIteration

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-! Serialized-size bounds for every prefix of the concrete circuit-copy
fold. The bounds use binary lengths, not unit-cost integer magnitudes. -/
namespace Shared.ComplexityBridge.TM2CircuitIterationSize
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.TM2CircuitIteration

theorem list_encoding_bound {α : Type} [BitstringEncoding α] (xs : List α) (B : Nat)
    (h : ∀ x ∈ xs, (BitstringEncoding.bitEncode x).length ≤ B) :
    (BitstringEncoding.bitEncode xs).length ≤ xs.length*(2*B+1) := by
  have hh := TM2MapSizeBounds.map_encoding_bound (id : α → α) xs B h
  simpa using hh

theorem fold_params (w : Work) (clock : List Bool) :
    (TM2PolynomialFold.fold step w clock).1 = w.1 := by
  induction clock generalizing w with
  | nil => rfl
  | cons b clock ih =>
    change (TM2PolynomialFold.fold step (advance w) clock).1 = w.1
    simpa [advance] using ih (advance w)

/-- Every fold state, for every input including invalid circuits, has a
polynomial-size canonical encoding in the complete initial request. -/
theorem fold_state_size (w : Work) (clock : List Bool) :
    let N := (BitstringEncoding.bitEncode (w,clock)).length
    (BitstringEncoding.bitEncode (TM2PolynomialFold.fold step w clock)).length ≤
      100*(N+1)^4 := by
  let p := w.1
  let s := w.2
  let final := TM2PolynomialFold.fold step w clock
  let N := (BitstringEncoding.bitEncode (w,clock)).length
  let Q := (N+1)^2
  have hw : (BitstringEncoding.bitEncode w).length ≤ N := pair_first_size (w,clock)
  have hc0 : (BitstringEncoding.bitEncode clock).length ≤ N := pair_second_size (w,clock)
  have hp : (BitstringEncoding.bitEncode p).length ≤ N := le_trans (pair_first_size w) hw
  have hs : (BitstringEncoding.bitEncode s).length ≤ N := le_trans (pair_second_size w) hw
  have hpg : (BitstringEncoding.bitEncode p.1).length ≤ N := le_trans (pair_first_size p) hp
  have ht : (BitstringEncoding.bitEncode p.1.1).length ≤ N := le_trans (pair_first_size p.1) hpg
  have hgs : (BitstringEncoding.bitEncode p.1.2).length ≤ N := le_trans (pair_second_size p.1) hpg
  have hout : (BitstringEncoding.bitEncode p.2).length ≤ N := le_trans (pair_second_size p) hp
  have hst : (BitstringEncoding.bitEncode s.2).length ≤ N := le_trans (pair_second_size s) hs
  have hin : (BitstringEncoding.bitEncode s.2.1).length ≤ N := le_trans (pair_first_size s.2) hst
  have hacc : (BitstringEncoding.bitEncode s.2.2).length ≤ N := le_trans (pair_second_size s.2) hst
  have hc : clock.length ≤ N := le_trans (CNF.list_length_le_bitEncode clock) hc0
  have htlen : p.1.1.length ≤ N := le_trans (CNF.list_length_le_bitEncode p.1.1) ht
  have hglen : p.1.2.length ≤ N := le_trans (CNF.list_length_le_bitEncode p.1.2) hgs
  have holen : p.2.length ≤ N := le_trans (CNF.list_length_le_bitEncode p.2) hout
  have hilen : s.2.1.length ≤ N := le_trans (CNF.list_length_le_bitEncode s.2.1) hin
  have halen : s.2.2.length ≤ N := le_trans (CNF.list_length_le_bitEncode s.2.2) hacc
  have hbase : (BitstringEncoding.bitEncode s.1).length ≤ N := le_trans (pair_first_size s) hs
  have hprod : clock.length*p.1.2.length ≤ N*N := Nat.mul_le_mul hc hglen
  have hQ : N ≤ Q := by dsimp [Q]; nlinarith
  have hQpos : 1 ≤ Q := by dsimp [Q]; nlinarith
  have hQQ : Q ≤ Q*Q := by nlinarith
  have hrefbound : ∀ x ∈ final.2.2.1, Nat.size x ≤ Q := by
    have hh := (fold_initial_bit_bound w.1 w.2 clock).1
    intro x hx
    have h := hh x hx
    dsimp [Q] at ⊢
    nlinarith
  have hgatebound : ∀ g ∈ final.2.2.2, ∀ i, TM2BoundedGateRename.refers g i → Nat.size i ≤ Q := by
    have hh := (fold_initial_bit_bound w.1 w.2 clock).2
    intro g hm i hi
    have h := hh g hm i hi
    dsimp [Q] at ⊢
    nlinarith
  have hrefcount : final.2.2.1.length ≤ N := by
    by_cases h : clock = []
    · subst clock
      simpa [final,TM2PolynomialFold.fold,p,s] using hilen
    · have hh := fold_refs_length p s clock h
      simpa [final,p,s,hh] using holen
  have hgatecount : final.2.2.2.length ≤ Q := by
    have hh := fold_gates_length p s clock
    have he : final.2.2.2.length = s.2.2.length+clock.length*p.1.2.length := by simpa [final,p,s] using hh
    rw [he]
    dsimp [Q]
    nlinarith
  have hbaselen : (BitstringEncoding.bitEncode final.2.1).length ≤ Q := by
    have hh := fold_base p s clock
    have he : final.2.1 = s.1+clock.length*p.1.2.length := by simpa [final,p,s] using hh
    rw [he]
    have hi := TM2GuardAllStep.index_bits_add s.1 (clock.length*p.1.2.length)
    dsimp [Q]
    nlinarith
  have hrefbits : (BitstringEncoding.bitEncode final.2.2.1).length ≤ N*(2*Q+1) := by
    have h := list_encoding_bound final.2.2.1 Q (by
      intro x hx
      rw [←nat_size_encoding]
      exact hrefbound x hx)
    exact le_trans h (Nat.mul_le_mul_right (2*Q+1) hrefcount)
  have hgatebits : (BitstringEncoding.bitEncode final.2.2.2).length ≤ Q*(6*Q+27) := by
    have h := list_encoding_bound final.2.2.2 (3*Q+13) (by
      intro g hg
      exact gate_encoding_bound g Q (hgatebound g hg))
    have hm := Nat.mul_le_mul_right (2*(3*Q+13)+1) hgatecount
    nlinarith
  have hparams : final.1 = p := fold_params w clock
  have hsz : (BitstringEncoding.bitEncode final).length ≤ 2*N+2*Q+2*N*(2*Q+1)+Q*(6*Q+27)+3 := by
    rw [pair_encoding_length final, pair_encoding_length final.2, pair_encoding_length final.2.2, hparams]
    nlinarith
  have hmul := Nat.mul_le_mul_right (2*Q+1) hQ
  change (BitstringEncoding.bitEncode final).length ≤ 100*(N+1)^4
  dsimp [Q] at hQQ hmul hsz ⊢
  nlinarith

end Shared.ComplexityBridge.TM2CircuitIterationSize
