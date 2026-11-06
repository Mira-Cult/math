import Shared.Codes.TM2PairCandidate
/-! Primitive-recursive finite representations of natural-coefficient
polynomials. The existence proof does not perform runtime reification of an
arbitrary function. -/
namespace Shared.Codes.NumericPolynomial

/-- A finite list of (coefficient, exponent) monomials. -/
abbrev Terms := List (Nat × Nat)

def eval (terms : Terms) (n : Nat) : Nat :=
  terms.foldr (fun t acc => t.1 * n ^ t.2 + acc) 0

theorem eval_primrec : Primrec₂ eval := by
  let A := Terms × Nat
  have hf : Primrec (fun p : A => p.1) := Primrec.fst
  have hg : Primrec (fun _ : A => 0) := Primrec.const 0
  have hstep : Primrec₂ (fun (p : A) (v : (Nat × Nat) × Nat) =>
      v.1.1 * p.2 ^ v.1.2 + v.2) := by
    have hpow : Primrec (fun x : A × ((Nat × Nat) × Nat) => x.1.2 ^ x.2.1.2) :=
      (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.snd.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
    have hmul : Primrec (fun x : A × ((Nat × Nat) × Nat) => x.2.1.1 * (x.1.2 ^ x.2.1.2)) :=
      Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) hpow
    exact (Primrec.nat_add.comp hmul (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr hf hg hstep).to₂

theorem eval_append (a b : Terms) (n : Nat) : eval (a++b) n = eval a n + eval b n := by
  induction a with
  | nil => simp [eval]
  | cons t a ih =>
    change t.1 * n ^ t.2 + eval (a++b) n = (t.1 * n ^ t.2 + eval a n) + eval b n
    rw [ih, Nat.add_assoc]

theorem polynomial_represented (p : Polynomial Nat) : ∃ terms : Terms, ∀ n, eval terms n = p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a,ha⟩ := hp
    obtain ⟨b,hb⟩ := hq
    refine ⟨a++b,fun n => ?_⟩
    simp [eval_append, ha, hb, Polynomial.eval_add]
  | monomial d a =>
    refine ⟨[(a,d)],fun n => ?_⟩
    simp [eval, Polynomial.eval_monomial]

example : eval [(3,2),(4,0)] 2 = 16 := by decide
example : eval [] 0 = 0 := by decide

end Shared.Codes.NumericPolynomial
