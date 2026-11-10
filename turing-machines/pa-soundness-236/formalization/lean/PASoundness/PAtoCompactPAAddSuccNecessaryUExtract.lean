import PASoundness.PAtoCompactTermTranslation
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactFreeNames

/-! Constructive extraction of right-child and successor-child term-graph
witnesses. These are finite K proof-data transformations and do not assert
term-graph existence or arithmetic soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccNecessaryUExtract
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity

/-- A successor graph contains the exact child graph witness at its private
binder and allocation base. No existence premise is supplied. -/
def successor_child {α : Type} (v : α → Nat) (u : Peano.language.Term α)
    (out b : Nat) :
    KDerivation (imp (termGraph v (.func .succ ![u]) out b).encode
      (existsCode b (termGraph v u b (b+64)).encode)) := by
  let L := termGraph v u b (b+64)
  let S := succAt b b out
  let M := andF L S
  have hp : KDerivation (imp M.encode L.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [M.encode]
    have hm : Context Γ (both L.encode S.encode) := by
      have h := Context.head [] M.encode
      simpa [Γ, M, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
    exact Context.conjunctionLeft hm
  have he := existsCongr b hp
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(termGraph v (.func .succ ![u]) out b).encode]
  have hs : Context Γ (both (domainAt b out).encode (existsCode b M.encode)) := by
    have h := Context.head [] (termGraph v (.func .succ ![u]) out b).encode
    simpa [Γ, termGraph, M, L, S, andF, CompactNamed.Formula.not,
      Formula.encode, both, neg] using h
  exact .mp (Context.conjunctionRight hs) (.closed he)

/-- A binary addition graph contains a right-child graph witness. The source
names of the right term must lie below the allocator so the left binder is
vacuous in the projected result. -/
def addition_right_child {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (out b : Nat)
    (hu : ∀ a ∈ u.varFinset, v a < b) :
    KDerivation (imp (termGraph v (.func .add ![t,u]) out b).encode
      (existsCode (b+1) (termGraph v u (b+1) (b+64+termCost t)).encode)) := by
  let L := termGraph v t b (b+64)
  let R := termGraph v u (b+1) (b+64+termCost t)
  let A := addAt b b (b+1) out
  let M := andF L (andF R A)
  have hp : KDerivation (imp M.encode R.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [M.encode]
    have hm : Context Γ (both L.encode (both R.encode A.encode)) := by
      have h := Context.head [] M.encode
      simpa [Γ, M, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
    exact Context.conjunctionLeft (Context.conjunctionRight hm)
  have hi := existsCongr (b+1) hp
  have hfreeR : b ∉ R.free := by
    intro hb
    have hs := termGraph_free_subset v u (b+1) (b+64+termCost t) hb
    rcases Finset.mem_union.mp hs with h | h
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
      have hlt := hu a ha
      omega
    · have he := Finset.mem_singleton.mp h
      omega
  have hfree : b ∉ (Formula.ex (b+1) R).free := by
    simpa [Formula.free] using hfreeR
  have ho : KDerivation (imp (existsCode b (existsCode (b+1) M.encode))
      (existsCode (b+1) R.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim (free_vacuity b (Formula.ex (b+1) R) hfree)
      (.closed (.generalize b hi)) (Context.head [] _)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(termGraph v (.func .add ![t,u]) out b).encode]
  have hs : Context Γ (both (domainAt b out).encode (existsCode b (existsCode (b+1) M.encode))) := by
    have h := Context.head [] (termGraph v (.func .add ![t,u]) out b).encode
    simpa [Γ, termGraph, M, L, R, A, andF, CompactNamed.Formula.not,
      Formula.encode, both, neg] using h
  exact .mp (Context.conjunctionRight hs) (.closed ho)

theorem successor_child_certificate {α : Type} (v : α → Nat) (u : Peano.language.Term α)
    (out b : Nat) : theoremCode (certificate (successor_child v u out b)) =
      imp (termGraph v (.func .succ ![u]) out b).encode
        (existsCode b (termGraph v u b (b+64)).encode) := certificate_correct _

theorem addition_right_child_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (out b : Nat)
    (hu : ∀ a ∈ u.varFinset, v a < b) :
    theoremCode (certificate (addition_right_child v t u out b hu)) =
      imp (termGraph v (.func .add ![t,u]) out b).encode
        (existsCode (b+1) (termGraph v u (b+1) (b+64+termCost t)).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactPAAddSuccNecessaryUExtract
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryUExtract.successor_child
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryUExtract.successor_child_certificate
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryUExtract.addition_right_child
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryUExtract.addition_right_child_certificate
