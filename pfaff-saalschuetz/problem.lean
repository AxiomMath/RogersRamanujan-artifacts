import Mathlib

/-! # Basic definitions in q-theory -/

open Finset SummationFilter

section CommSemiring
variable {R : Type*} [CommSemiring R]

/-- $q$-analogue of integer, $[n]_q = 1 + q + q^2 + \dots + q^{n-1}$. -/
def qInt (q : R) (n : ℕ) : R :=
  ∑ i ∈ range n, q ^ i

/-- $q$-factorial, $[n]_q! = [1]_q [2]_q \dots [n]_q$ -/
def qFactorial (q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, qInt q (i + 1)

/-- q-binomial coefficients. q-analogue of `Nat.choose`. -/
def qChoose (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qChoose q n k + q ^ (k + 1) * qChoose q n (k + 1)

end CommSemiring

/-- $q$-Pochhammer symbol, $(a;q)_n = \prod_{i=0}^{n-1} (1 - a*q^i)$

To enable the notation `(a; q)_n`, use `open scoped QTheory`.

For the unsafe version (use with caution) `(a)_n` which uses any local variable called `q`, use
`open scoped QTheoryUnsafe`.
-/
def qPochhammer {R : Type*} [CommRing R] (a q : R) (n : ℕ) : R :=
  ∏ i ∈ range n, (1 - a * q ^ i)

/-- Infinite $q$-Pochhammer symbol, $(a;q)_\infty = \prod_{i=0}^{\infty} (1 - a*q^i)$

To enable the notation `(a; q)_∞`, use `open scoped QTheory`.

For the unsafe version (use with caution) `(a)_∞` which uses any local variable called `q`, use
`open scoped QTheoryUnsafe`. -/
noncomputable def qPochhammerInf {R : Type*} [TopologicalSpace R] [CommRing R] (a q : R) : R :=
  ∏'[conditional ℕ] i, (1 - a * q ^ i)

namespace QTheory

@[inherit_doc] scoped notation:max "(" a "; " q ")_" n:arg => qPochhammer a q n
@[inherit_doc] scoped notation:max "(" a "; " q ")_∞" => qPochhammerInf a q

end QTheory

namespace QTheoryUnsafe

set_option hygiene false
@[inherit_doc] scoped notation:max "(" a ")_" n:arg => qPochhammer a q n
@[inherit_doc] scoped notation:max "(" a ")_∞" => qPochhammerInf a q

end QTheoryUnsafe

open QTheoryUnsafe

theorem sum_qChoose_mul_qPochhammer_eq_qPochhammer_mul
    {R : Type*} [CommRing R] (a b c q : R) (n : ℕ) :
    ∑ k ∈ range (n + 1),
      qChoose q n k * (a)_k * (b)_k * c ^ k * (c)_(n - k) * (a * b * c * q ^ k)_(n - k) =
    (a * c)_n * (b * c)_n := by
  sorry
