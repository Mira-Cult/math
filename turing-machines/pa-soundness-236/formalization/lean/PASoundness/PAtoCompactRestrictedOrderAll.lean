import PASoundness.PAtoCompactRestrictedOrderPoint

/-! The supplied endpoint filter preserves the entire displayed old-domain
order matrix. It does not construct the graph or establish quotient laws. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedOrderAll
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactRestrictedOrderPoint
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def restrictedOrder : Nat :=
  allCode 30 (allCode 31 (allCode 32 (allCode 33
    (imp (both (member 2 30) (both (member 2 31)
      (both (member 5 32) (both (member 5 33)
        (both (graphFormula 8 30 32).encode (graphFormula 8 31 33).encode)))))
      (both (imp (member 31 30) (member 33 32))
        (imp (member 33 32) (member 31 30)))))))

private def premise_vacuity (n : Nat) (hn : 30 ≤ n) :
    ∀ z, z ∈ [filter, orderFormula.encode, successorCode 5 1 10, successorCode 2 0 9] →
      KDerivation (imp z (allCode n z)) := by
  intro z hz
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  by_cases he : z = filter
  · subst z
    have hf : n ∉ (namedFilter 6 8 14 2 5).names := by
      intro hm
      have hle : n ≤ (namedFilter 6 8 14 2 5).names.sup id := Finset.le_sup (f := id) hm
      have hbound : (namedFilter 6 8 14 2 5).names.sup id < 30 := by decide
      omega
    exact restriction_filter_vacuity 6 8 14 2 5 n hf
  by_cases he : z = orderFormula.encode
  · subst z
    have hf : n ∉ orderFormula.names := by
      intro hm
      have hle : n ≤ orderFormula.names.sup id := Finset.le_sup (f := id) hm
      have hbound : orderFormula.names.sup id < 30 := by decide
      omega
    exact orderFormula.vacuity n hf
  by_cases he : z = successorCode 5 1 10
  · subst z
    exact successor_vacuity 5 1 10 n (by omega) (by omega) (by omega)
  have he : z = successorCode 2 0 9 := by simp_all
  subst z
  exact successor_vacuity 2 0 9 n (by omega) (by omega) (by omega)

/-- K derives the complete quantified old-domain order clause of restricted
graph 8 from the supplied raw successors, original order clause and exact
endpoint filter. No existence, totality, uniqueness or quotient is asserted. -/
def restricted_order_all : KDerivation
    (imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp orderFormula.encode (imp filter restrictedOrder)))) := by
  let SX := successorCode 2 0 9
  let SY := successorCode 5 1 10
  let O := orderFormula.encode
  let F := filter
  let A := member 2 30
  let B := member 2 31
  let C := member 5 32
  let D := member 5 33
  let H := (graphFormula 8 30 32).encode
  let I := (graphFormula 8 31 33).encode
  let Guard := both A (both B (both C (both D (both H I))))
  let Result := both (imp (member 31 30) (member 33 32))
    (imp (member 33 32) (member 31 30))
  let Γ := [F,O,SY,SX]
  have hp : Context Γ (imp Guard Result) := by
    apply Context.deduction
    have hg : Context (Guard :: Γ) Guard := .head _ _
    have hsx : Context (Guard :: Γ) SX := .hypothesis (by simp [Γ])
    have hsy : Context (Guard :: Γ) SY := .hypothesis (by simp [Γ])
    have ho : Context (Guard :: Γ) O := .hypothesis (by simp [Γ])
    have hf : Context (Guard :: Γ) F := .hypothesis (by simp [Γ])
    have ha : Context (Guard :: Γ) A := Context.conjunctionLeft hg
    have hb : Context (Guard :: Γ) B := Context.conjunctionLeft (Context.conjunctionRight hg)
    have hc : Context (Guard :: Γ) C := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hg))
    have hd : Context (Guard :: Γ) D := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg)))
    have he : Context (Guard :: Γ) H := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg))))
    have hi : Context (Guard :: Γ) I := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hg))))
    exact .mp hi (.mp he (.mp hd (.mp hc (.mp hb (.mp ha (.mp hf
      (.mp ho (.mp hsy (.mp hsx (.closed restricted_order_point))))))))))
  have h33 := Context.generalize 33 (premise_vacuity 33 (by decide)) hp
  have h32 := Context.generalize 32 (premise_vacuity 32 (by decide)) h33
  have h31 := Context.generalize 31 (premise_vacuity 31 (by decide)) h32
  have h30 := Context.generalize 30 (premise_vacuity 30 (by decide)) h31
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact h30

theorem restricted_order_all_certificate : theoremCode (certificate restricted_order_all) =
    imp (successorCode 2 0 9) (imp (successorCode 5 1 10)
      (imp orderFormula.encode (imp filter restrictedOrder))) :=
  certificate_correct restricted_order_all

end PASoundness.PAtoCompactRestrictedOrderAll

#print axioms PASoundness.PAtoCompactRestrictedOrderAll.restricted_order_all
#print axioms PASoundness.PAtoCompactRestrictedOrderAll.restricted_order_all_certificate
