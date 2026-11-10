import PASoundness.PAtoCompactVariableTermTotality
import PASoundness.PAtoCompactSuccTermReplacement
import PASoundness.PAtoCompactScopedAlphaInvariant
import PASoundness.PAtoCompactFreeVacuity

/-! A capture-safe witness-introduction step for successor term graphs.
This does not construct the candidate output, successor relation, or a
child-graph witness; they remain explicit K assumptions. -/
namespace PASoundness.PAtoCompactSuccTermTotality

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphReplace
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactScopedAlphaInvariant
open PASoundness.PAtoCompactVariableTermTotality PASoundness.PAtoCompactSuccTermReplacement
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactFreeNames

/-- Replacing the successor graph's existential name by a lower witness
updates the child output and the successor input without changing source
variable labels. -/
theorem succ_body_replace {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b out x : Nat) (hout : out < b) (_hx : x < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) :
    replace b x (andF (termGraph v t b (b + 64)) (succAt b b out)) =
      andF (termGraph v t x (b + 64)) (succAt b x out) := by
  have hr := replace_termGraph v t b (b+64) b x (by omega)
  have hm : termGraph (rename b x ∘ v) t x (b+64) = termGraph v t x (b+64) := by
    apply termGraph_name_agree
    intro a ha
    simp [Function.comp_apply, rename, show v a ≠ b by have := hv a ha; omega]
  have hs := replace_succAt b b out b x (by omega)
  simpa [andF, CompactNamed.Formula.not, replace, rename, show out ≠ b by omega, hm] using
    congrArg₂ andF hr hs

/-- Given a candidate output, a child graph and the intended quotient
successor relation for an explicit witness name, construct the successor
term graph as an actual finite K derivation. -/
def succTerm_from_witness {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b out x : Nat) (hout : out < b) (hx : x < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) :
    KDerivation (imp (domainAt b out).encode
      (imp (termGraph v t x (b+64)).encode
        (imp (succAt b x out).encode
          (termGraph v (.func .succ ![t]) out b).encode))) := by
  let f := andF (termGraph v t b (b+64)) (succAt b b out)
  have hnotb : b ∉ f.binders := by
    simp only [f, andF_binders, Finset.mem_union, not_or]
    exact ⟨termGraph_below_not_binder v t b (b+64) b (by omega),
      succAt_below_not_binder b b out b (by omega)⟩
  have hnotx : x ∉ f.binders := by
    simp only [f, andF_binders, Finset.mem_union, not_or]
    exact ⟨termGraph_below_not_binder v t b (b+64) x (by omega),
      succAt_below_not_binder b b out x (by omega)⟩
  have hi := exists_from_instance b x f (by omega) hnotb hnotx
  rw [succ_body_replace v t b out x hout hx hv] at hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(succAt b x out).encode, (termGraph v t x (b+64)).encode,
    (domainAt b out).encode]
  have hd : Context Γ (domainAt b out).encode := .hypothesis (by simp [Γ])
  have ht : Context Γ (termGraph v t x (b+64)).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (succAt b x out).encode := .hypothesis (by simp [Γ])
  have hc := Context.conjunctionIntro ht hs
  have hf : Context Γ (andF (termGraph v t x (b+64)) (succAt b x out)).encode := by
    simpa [andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hc
  have he : Context Γ (existsCode b f.encode) := .mp hf (.closed hi)
  have hh := Context.conjunctionIntro hd he
  simpa [termGraph, f, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, existsCode] using hh

/-- The K calculus projects the explicit candidate guard from any generated
term graph; no standard-model interpretation is used. -/
def termGraph_domain {α : Type} (v : α → Nat) (t : Peano.language.Term α)
    (out b : Nat) : KDerivation (imp (termGraph v t out b).encode (domainAt b out).encode) := by
  have left (a z : CompactNamed.Formula) : KDerivation (imp (andF a z).encode a.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have h := Context.head [] (andF a z).encode
    have hc : Context [(andF a z).encode] (both a.encode z.encode) := by
      simpa [andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h
    exact Context.conjunctionLeft hc
  cases t with
  | var a => exact left _ _
  | func f ts =>
      cases f <;> exact left _ _

/-- Compose a child-graph existence proof with a supplied quotient-successor
existence proof. Every K vacuity proof is retained explicitly; this theorem
does not construct the successor-closure premise. -/
def succ_total_from_child {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b out x : Nat) (g : Formula)
    (hout : out < b) (hx : x < b) (hv : ∀ a ∈ t.varFinset, v a < b)
    (child : KDerivation (imp g.encode
      (existsCode x (termGraph v t x (b+64)).encode)))
    (next : KDerivation (imp (domainAt (b+64) x).encode
      (existsCode out (andF (domainAt b out) (succAt b x out)).encode)))
    (vgx : KDerivation (imp g.encode (allCode x g.encode)))
    (vgo : KDerivation (imp g.encode (allCode out g.encode)))
    (vchildo : KDerivation (imp (termGraph v t x (b+64)).encode
      (allCode out (termGraph v t x (b+64)).encode)))
    (vgoalx : KDerivation (imp (existsCode out (termGraph v (.func .succ ![t]) out b).encode)
      (allCode x (existsCode out (termGraph v (.func .succ ![t]) out b).encode))))
    (vgoalo : KDerivation (imp (existsCode out (termGraph v (.func .succ ![t]) out b).encode)
      (allCode out (existsCode out (termGraph v (.func .succ ![t]) out b).encode)))) :
    KDerivation (imp g.encode (existsCode out (termGraph v (.func .succ ![t]) out b).encode)) := by
  let C := (termGraph v t x (b+64)).encode
  let N := (andF (domainAt b out) (succAt b x out)).encode
  let E := existsCode out (termGraph v (.func .succ ![t]) out b).encode
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [g.encode]
  have hchild : Context Γ (existsCode x C) := .mp (Context.head [] _) (.closed child)
  apply Context.existsElim vgoalx _ hchild
  apply generalizeOne x vgx
  apply Context.deduction
  let Δ := [C, g.encode]
  have hc : Context Δ C := Context.head _ _
  have hd : Context Δ (domainAt (b+64) x).encode := .mp hc (.closed (termGraph_domain v t x (b+64)))
  have hn : Context Δ (existsCode out N) := .mp hd (.closed next)
  apply Context.existsElim vgoalo _ hn
  apply Context.generalize out
  · intro q hq
    change q ∈ [C, g.encode] at hq
    by_cases he : q = C
    · subst q
      exact vchildo
    · have he' : q = g.encode := by simpa [he] using hq
      subst q
      exact vgo
  apply Context.deduction
  let Θ := [N, C, g.encode]
  have hn' : Context Θ (both (domainAt b out).encode (succAt b x out).encode) := by
    have h := Context.head [C, g.encode] N
    simpa [Θ, N, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h
  have hc' : Context Θ C := .hypothesis (by simp [Θ])
  have hs : Context Θ (termGraph v (.func .succ ![t]) out b).encode :=
    .mp (Context.conjunctionRight hn')
      (.mp hc' (.mp (Context.conjunctionLeft hn') (.closed (succTerm_from_witness v t b out x hout hx hv))))
  have hi := existsIntroduce out (termGraph v (.func .succ ![t]) out b)
    (termGraph_below_not_binder v (.func .succ ![t]) out b out hout)
  exact .mp hs (.closed hi)

/-- The same composition with the required K vacuity proofs constructed
from explicit free-name freshness. The successor-existence derivation remains
an input; this is a proof rule, not an unconditional successor totality proof. -/
def succ_total_from_fresh_child {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b out x : Nat) (g : CompactNamed.Formula)
    (hout : out < b) (hx : x < b) (hxo : x ≠ out)
    (hv : ∀ a ∈ t.varFinset, v a < b)
    (hxv : ∀ a ∈ t.varFinset, v a ≠ x)
    (hov : ∀ a ∈ t.varFinset, v a ≠ out)
    (hxg : x ∉ g.free) (hog : out ∉ g.free)
    (child : KDerivation (imp g.encode
      (existsCode x (termGraph v t x (b+64)).encode)))
    (next : KDerivation (imp (domainAt (b+64) x).encode
      (existsCode out (andF (domainAt b out) (succAt b x out)).encode))) :
    KDerivation (imp g.encode (existsCode out (termGraph v (.func .succ ![t]) out b).encode)) := by
  let s : Peano.language.Term α := .func .succ ![t]
  let G : CompactNamed.Formula := .ex out (termGraph v s out b)
  have hsuccvars : s.varFinset = t.varFinset := by
    simp [s, FirstOrder.Language.Term.varFinset]
  have houtChild : out ∉ (termGraph v t x (b+64)).free := by
    intro hm
    have h := termGraph_free_subset v t x (b+64) hm
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
      exact hov a ha he
    · exact hxo (Finset.mem_singleton.mp h).symm
  have hxG : x ∉ G.free := by
    intro hm
    have hm' : x ∈ (termGraph v s out b).free := (Finset.mem_erase.mp hm).2
    have h := termGraph_free_subset v s out b hm'
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
      rw [hsuccvars] at ha
      exact hxv a ha he
    · exact hxo (Finset.mem_singleton.mp h)
  have hoG : out ∉ G.free := by simp [G, CompactNamed.Formula.free]
  exact succ_total_from_child v t b out x g hout hx hv child next
    (free_vacuity x g hxg) (free_vacuity out g hog)
    (free_vacuity out (termGraph v t x (b+64)) houtChild)
    (by simpa [G, CompactNamed.Formula.encode, s] using free_vacuity x G hxG)
    (by simpa [G, CompactNamed.Formula.encode, s] using free_vacuity out G hoG)

theorem succ_total_from_fresh_child_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b out x : Nat) (g : CompactNamed.Formula)
    (hout : out < b) (hx : x < b) (hxo : x ≠ out)
    (hv : ∀ a ∈ t.varFinset, v a < b)
    (hxv : ∀ a ∈ t.varFinset, v a ≠ x)
    (hov : ∀ a ∈ t.varFinset, v a ≠ out)
    (hxg : x ∉ g.free) (hog : out ∉ g.free)
    (child : KDerivation (imp g.encode
      (existsCode x (termGraph v t x (b+64)).encode)))
    (next : KDerivation (imp (domainAt (b+64) x).encode
      (existsCode out (andF (domainAt b out) (succAt b x out)).encode))) :
    theoremCode (certificate (succ_total_from_fresh_child v t b out x g hout hx hxo hv
      hxv hov hxg hog child next)) =
      imp g.encode (existsCode out (termGraph v (.func .succ ![t]) out b).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactSuccTermTotality

#print axioms PASoundness.PAtoCompactSuccTermTotality.succ_body_replace
#print axioms PASoundness.PAtoCompactSuccTermTotality.succTerm_from_witness
#print axioms PASoundness.PAtoCompactSuccTermTotality.termGraph_domain
#print axioms PASoundness.PAtoCompactSuccTermTotality.succ_total_from_child
#print axioms PASoundness.PAtoCompactSuccTermTotality.succ_total_from_fresh_child
#print axioms PASoundness.PAtoCompactSuccTermTotality.succ_total_from_fresh_child_certificate
