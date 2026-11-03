import Shared.ComplexityBridge.CNFDisjunction
import Shared.ComplexityBridge.CNFComputability
import Shared.ComplexityBridge.UnaryBounded

/-! Effective construction of the disjunction layer of the CNF reduction.
These primitive-recursion proofs do not establish machine running-time bounds. -/
namespace Shared.ComplexityBridge.CNFDisjunctionComputability

open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CNFDisjunction

theorem evenLiteral_primrec : Primrec evenLiteral := by
  exact Primrec.pair (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) Primrec.snd

theorem evenClause_primrec : Primrec evenClause :=
  Primrec.list_map Primrec.id (evenLiteral_primrec.comp Primrec.snd).to₂

theorem evenFormula_primrec : Primrec evenFormula :=
  Primrec.list_map Primrec.id (evenClause_primrec.comp Primrec.snd).to₂

theorem selector_primrec : Primrec selector :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)

theorem guardClause_primrec : Primrec₂ guardClause := by
  exact (Primrec.list_cons.comp
    (Primrec.pair (selector_primrec.comp Primrec.fst) (Primrec.const false))
    (evenClause_primrec.comp Primrec.snd)).to₂

theorem guardFormula_primrec : Primrec₂ guardFormula := by
  exact (Primrec.list_map (Primrec.snd : Primrec (fun p : Nat × Formula => p.2))
    (guardClause_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂

/-- Equivalent right-recursive implementation, retaining the final index. -/
def guardSuffix (endIndex : Nat) : List Formula → Formula
  | [] => []
  | f::fs => guardFormula (endIndex-(fs.length+1)) f ++ guardSuffix endIndex fs

theorem guardSuffix_correct (fs : List Formula) (start : Nat) :
    guardSuffix (start+fs.length) fs = guardAll start fs := by
  induction fs generalizing start with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.length_cons,guardSuffix,guardAll]
    have he : start + (fs.length + 1) - (fs.length + 1) = start := by omega
    have hn : start + (fs.length + 1) = (start+1)+fs.length := by omega
    rw [he,hn,ih]

theorem guardSuffix_primrec : Primrec₂ guardSuffix := by
  let A := Nat × List Formula
  let S := Formula × List Formula × Formula
  have hstep : Primrec₂ (fun (a : A) (s : S) =>
      guardFormula (a.1-(s.2.1.length+1)) s.1 ++ s.2.2) := by
    have hindex : Primrec (fun z : A × S => z.1.1-(z.2.2.1.length+1)) :=
      Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
    exact (Primrec.list_append.comp
      (guardFormula_primrec.comp hindex (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).to₂
  have h := Primrec.list_rec (Primrec.snd : Primrec (fun a : A => a.2)) (Primrec.const ([] : Formula)) hstep
  apply h.to₂.of_eq
  intro endIndex fs
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [guardSuffix,ih]

theorem guardAll_primrec : Primrec₂ guardAll := by
  have h := guardSuffix_primrec.comp
    (Primrec.nat_add.comp (Primrec.fst : Primrec (fun a : Nat × List Formula => a.1))
      (Primrec.list_length.comp Primrec.snd)) Primrec.snd
  apply h.to₂.of_eq
  intro start fs
  exact guardSuffix_correct fs start

theorem choices_primrec : Primrec₂ choices := by
  have hentry : Primrec₂ (fun (a : Nat × Nat) (i : Nat) => (selector (a.1+i),true)) :=
    (Primrec.pair (selector_primrec.comp
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)) (Primrec.const true)).to₂
  exact (Primrec.list_map (Primrec.list_range.comp (Primrec.snd : Primrec (fun a : Nat × Nat => a.2))) hentry).to₂

theorem disjoin_primrec : Primrec disjoin := by
  have hchoices : Primrec (fun fs : List Formula => choices 0 fs.length) :=
    choices_primrec.comp (Primrec.const 0) Primrec.list_length
  have hguard : Primrec (fun fs : List Formula => guardAll 0 fs) :=
    guardAll_primrec.comp (Primrec.const 0) Primrec.id
  exact Primrec.list_append.comp
    (Primrec.list_cons.comp hchoices (Primrec.const ([] : Formula))) hguard

theorem disjoin_computable : Computable disjoin := disjoin_primrec.to_comp

/-- The uniform disjunction is primitive recursive once its individual
fixed-witness formula generator has been proved primitive recursive. -/
theorem boundedPairFormula_primrec_of_pair
    (hpair : Primrec (fun z : Shared.ComplexityBridge.UnaryBounded.Decoded =>
      Shared.ComplexityBridge.CircuitPairWitness.pairFormula z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Primrec (fun z : Shared.ComplexityBridge.UnaryBounded.Decoded =>
      boundedPairFormula z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let A := Shared.ComplexityBridge.UnaryBounded.Decoded
  have hrange : Primrec (fun z : A => List.range (z.2.2.1+1)) :=
    Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have heach : Primrec₂ (fun (z : A) (n : Nat) =>
      Shared.ComplexityBridge.CircuitPairWitness.pairFormula z.1 z.2.1 n z.2.2.2) := by
    have hp : Primrec (fun v : A × Nat => v.1.1) := Primrec.fst.comp Primrec.fst
    have hx : Primrec (fun v : A × Nat => v.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hf : Primrec (fun v : A × Nat => v.1.2.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    exact (hpair.comp (Primrec.pair hp (Primrec.pair hx (Primrec.pair Primrec.snd hf)))).to₂
  exact disjoin_primrec.comp (Primrec.list_map hrange heach)

theorem reduction_primrec_of_generator
    (hgenerator : Primrec (fun z : Shared.ComplexityBridge.UnaryBounded.Decoded =>
      BitstringEncoding.bitEncode (boundedPairFormula z.1 z.2.1 z.2.2.1 z.2.2.2))) :
    Primrec Shared.ComplexityBridge.UnaryBounded.reduction := by
  open Shared.ComplexityBridge.UnaryBounded in
  have h := Primrec.option_casesOn decodeRequest_primrec
    (Primrec.const (BitstringEncoding.bitEncode ([[]] : Formula)))
    (hgenerator.comp Primrec.snd).to₂
  apply h.of_eq
  intro raw
  cases hd : decodeRequest raw with
  | none => simp [reduction,hd]
  | some d => rcases d with ⟨p,x,bound,fuel⟩; simp [reduction,hd]

theorem reduction_primrec_of_pair_and_encoding
    (hpair : Primrec (fun z : Shared.ComplexityBridge.UnaryBounded.Decoded =>
      Shared.ComplexityBridge.CircuitPairWitness.pairFormula z.1 z.2.1 z.2.2.1 z.2.2.2))
    (hencode : Primrec (@BitstringEncoding.bitEncode Formula _)) :
    Primrec Shared.ComplexityBridge.UnaryBounded.reduction :=
  reduction_primrec_of_generator (hencode.comp (boundedPairFormula_primrec_of_pair hpair))

namespace Fixtures
example : guardSuffix 2 [[[(0,true)]],[[(1,false)]]] =
    guardAll 0 [[[(0,true)]],[[(1,false)]]] := by decide
example : disjoin [] = [[]] := by decide
end Fixtures

end Shared.ComplexityBridge.CNFDisjunctionComputability
