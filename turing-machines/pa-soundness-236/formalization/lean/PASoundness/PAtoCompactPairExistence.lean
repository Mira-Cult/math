import PASoundness.PAtoCompactPairQuantifiers
import PASoundness.PAtoCompactPairSelector
import PASoundness.PAtoCompactSingleton

/-! Existential elimination wrapper for a K unordered-pair construction.
The unconditional composition retains the singleton graph as its premise;
it does not assert uniqueness, a quotient, or a PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairExistence
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactPairSelector
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactPairQuantifiers
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Eliminate the selector's formula-code witness and external point witness,
retaining the supplied singleton graph as an explicit premise. -/
def pair_from_singleton (s a b t q r d : Nat)
    (fresh : [pairPredicate a b t,s,a,b,t,q,r,d].Nodup)
    (hgraph : KDerivation (imp (singletonCode a s q)
      (imp (pairSelectorBody s a b t) (imp (equal t b)
        (pairCode a b (pairPredicate a b t) r))))) :
    KDerivation (imp (singletonCode a s q) (existsCode d (pairCode a b d r))) := by
  let c := pairPredicate a b t
  let S := singletonCode a s q
  let B := pairSelectorBody s a b t
  let E := existsCode d (pairCode a b d r)
  have hf : [c,s,a,b,t,q,r,d].Nodup := fresh
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, not_false_eq_true] at hf
  have hcs : c ≠ s := by aesop
  have hca : c ≠ a := by aesop
  have hcb : c ≠ b := by aesop
  have hct : c ≠ t := by aesop
  have hcq : c ≠ q := by aesop
  have hcr : c ≠ r := by aesop
  have hcd : c ≠ d := by aesop
  have hta : t ≠ a := by aesop
  have htb : t ≠ b := by aesop
  have hts : t ≠ s := by aesop
  have htq : t ≠ q := by aesop
  have htr : t ≠ r := by aesop
  have htd : t ≠ d := by aesop
  have hda : d ≠ a := by aesop
  have hdb : d ≠ b := by aesop
  have hdr : d ≠ r := by aesop
  let fE : CompactNamed.Formula := .ex d (namedPair a b d r)
  let fS : CompactNamed.Formula := namedSingleton a s q
  let fC : CompactNamed.Formula := .imp fS (.imp (.equal t b) fE)
  have hnamesC : c ∉ fC.names := by
    simp [fC,fS,fE,namedSingleton,namedPair,namedBoth,namedEither,
      CompactNamed.Formula.names,hcs,hca,hcb,hct,hcq,hcr,hcd]
  have hvC : KDerivation (imp (imp S (imp (equal t b) E))
      (allCode c (imp S (imp (equal t b) E)))) := by
    have h := fC.vacuity c hnamesC
    simpa [fC,fS,fE,S,E,namedSingleton,namedPair,namedBoth,namedEither,singletonCode,
      pairCode,CompactNamed.Formula.encode,CompactProof.both,CompactProof.neg,
      CompactDerivations.either] using h
  have hbdy : KDerivation (imp B (imp S (imp (equal t b) E))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [equal t b,S,B]
    have hS : Context Γ S := .hypothesis (by simp [Γ])
    have hB : Context Γ B := .hypothesis (by simp [Γ])
    have he : Context Γ (equal t b) := .hypothesis (by simp [Γ])
    have hg : Context Γ (pairCode a b c r) := .mp he (.mp hB (.mp hS (.closed hgraph)))
    exact .mp hg (.closed (pair_existential_intro_of_fresh a b c d r
      (Ne.symm hcd) hda hdb hdr hcr))
  have hcond : KDerivation (imp S (imp (equal t b) E)) := by
    apply Context.closeEmpty
    apply Context.existsElim hvC
    · exact .closed (.generalize c hbdy)
    · exact .closed (selector8_pair_witness s a b t (Ne.symm hcs))
  let fT : CompactNamed.Formula := .imp fS fE
  have hnamesT : t ∉ fT.names := by
    simp [fT,fS,fE,namedSingleton,namedPair,namedBoth,namedEither,
      CompactNamed.Formula.names,hta,htb,hts,htq,htr,htd]
  have hvT : KDerivation (imp (imp S E) (allCode t (imp S E))) := by
    have h := fT.vacuity t hnamesT
    simpa [fT,fS,fE,S,E,namedSingleton,namedPair,namedBoth,namedEither,singletonCode,
      pairCode,CompactNamed.Formula.encode,CompactProof.both,CompactProof.neg,
      CompactDerivations.either] using h
  have hmove : KDerivation (imp (equal t b) (imp S E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    have hs : Context [S,equal t b] S := Context.head _ _
    have he : Context [S,equal t b] (equal t b) := .hypothesis (by simp)
    exact .mp he (.mp hs (.closed hcond))
  apply Context.closeEmpty
  apply Context.existsElim hvT
  · exact .closed (.generalize t hmove)
  · exact .closed (existsEqual t b)

/-- Supplying the checked selector-to-graph derivation discharges the wrapper's
proof premise. The singleton graph remains explicit. -/
def pair_from_singleton_closed (s a b t q r d : Nat)
    (fresh : [pairPredicate a b t,s,a,b,t,q,r,d].Nodup) :
    KDerivation (imp (singletonCode a s q) (existsCode d (pairCode a b d r))) := by
  have hf : [s,a,b,t,q,r].Nodup :=
    List.Nodup.sublist (List.sublist_append_left [s,a,b,t,q,r] [d])
      (List.nodup_cons.mp fresh).2
  have hcr : pairPredicate a b t ≠ r := by
    intro h
    have hr : r ∈ [s,a,b,t,q,r,d] := by simp
    exact (List.nodup_cons.mp fresh).1 (h ▸ hr)
  exact pair_from_singleton s a b t q r d fresh (pair_body_graph s a b t q r hf (Ne.symm hcr))

theorem pair_from_singleton_certificate (s a b t q r d : Nat)
    (fresh : [pairPredicate a b t,s,a,b,t,q,r,d].Nodup) :
    theoremCode (certificate (pair_from_singleton_closed s a b t q r d fresh)) =
      imp (singletonCode a s q) (existsCode d (pairCode a b d r)) :=
  certificate_correct (pair_from_singleton_closed s a b t q r d fresh)

end PASoundness.PAtoCompactPairExistence

#print axioms PASoundness.PAtoCompactPairExistence.pair_from_singleton
#print axioms PASoundness.PAtoCompactPairExistence.pair_from_singleton_closed
#print axioms PASoundness.PAtoCompactPairExistence.pair_from_singleton_certificate
