import data.set
import tactic.basic
import data.complex.exponential
import data.real.ennreal
import data.nat.prime

import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import algebra.euclidean_domain
import algebra.gcd_monoid
import tactic
import data.nat.modeq

import data.fintype.intervals
import data.set.intervals.basic

open set

variable {U : Type}
variables A B C : set U
variable x : U

example (h1 : A ∩ (B \ C) = ∅) : A ∩ B ⊆ C :=
begin
  intro x,
  intro h2,
  cases h2 with h2 h3,
  rw set.eq_empty_iff_forall_not_mem at h1,
  have := h1 x,
  rw set.mem_inter_iff at this,
  simp only [h2, h3, true_and, mem_diff, not_not_mem] at this,
  assumption
end

theorem absExpExpRe (z : ℂ) : complex.abs (complex.exp z) = real.exp (complex.re z) :=
calc complex.abs (complex.exp z)
    = complex.abs (complex.exp z.re) : complex.abs_exp_eq_iff_re_eq.mpr (complex.of_real_re z.re)
... = complex.abs (real.exp z.re) : by rw complex.of_real_exp z.re
... = abs (real.exp z.re) : complex.abs_of_real _
... = real.exp (z.re) : abs_of_pos (real.exp_pos _)

lemma le_self_pow (a p : nat) (h : 0 < p) : a ≤ a ^ p :=
begin
  induction p,
  { exact absurd h (lt_irrefl 0) },
  by_cases h'' : 0 < p_n,
  { specialize p_ih h'',
    rw pow_succ,
    calc a ≤ a * a : nat.le_mul_self a
    ... ≤ _ : nat.mul_le_mul_left _ p_ih },
  { rw nat.pos_iff_ne_zero at h'', push_neg at h'', subst h'', rw pow_one },
end

example (b : nat) : b ≤ b ^ 2 := le_self_pow _ _ zero_lt_two

example (p q : Prop) (h : p ∨ q) : ¬p → q := or.resolve_left h
example (a : nat) (h : a % 2 = 1) : odd a := nat.odd_iff.mpr h
example (a b c : nat) (h : a * b ≤ a * c) (h' : 0 < a) : b ≤ c := (mul_le_mul_left h').mp h
example (a k : nat) (h : a ∣ k) : a * (k/a) = k := nat.mul_div_cancel' h
lemma one_le_of_dvd {a b : nat} (h : a ∣ b)  (h' : b ≠ 0): 1 ≤ a := by {
  rw [nat.succ_le_iff, nat.pos_iff_ne_zero],
  contrapose! h',
  subst a,
  rwa zero_dvd_iff at h
}

theorem solution
  {p q : ℕ}
  (hp : nat.prime p)
  (hq : nat.prime q)
  (p_lt_q : p < q)
  (p_ne_two : p ≠ 2)
  (q_ne_two : q ≠ 2)
  (consecutive : ∀ k, p < k → k < q → ¬ nat.prime k) :
∃ a b c, p + q = a * b * c
∧ a > 1 ∧ b > 1 ∧ c > 1 :=
begin
  have hp1 := hp.eq_two_or_odd.resolve_left p_ne_two,
  have hq1 := hq.eq_two_or_odd.resolve_left q_ne_two,
  rw ←nat.odd_iff at hp1 hq1,
  obtain ⟨k, hk⟩ : even (p + q),
  { simp at hp1 hq1,
    simp [hp1, hq1] with parity_simps },
  have : ¬nat.prime k,
  { apply consecutive; linarith },
  obtain ⟨a, hadvd, hane1, hanek⟩ := nat.exists_dvd_of_not_prime (by linarith [hp.two_le, hq.two_le]) this,
  use [a, k / a, 2],
  have hapos : 0 < a,
  { rw [nat.pos_iff_ne_zero],
    rintro rfl,
    rw [zero_dvd_iff] at hadvd,
    exact hanek hadvd.symm },
  refine ⟨_, _, _, _⟩,
  { rw [hk, nat.mul_div_cancel' hadvd, mul_comm] },
  { apply lt_of_le_of_ne _ hane1.symm,
    rwa [nat.succ_le_iff] },
  { obtain ⟨b, rfl⟩ := hadvd,
    have : b ≠ 0,
    { rintro rfl,
      linarith [hp.two_le, hq.two_le, hk] },
    rw mul_comm,
    rw nat.mul_div_cancel _ hapos,
    apply lt_of_le_of_ne,
    { rwa [nat.succ_le_iff, nat.pos_iff_ne_zero] },
    { contrapose! hanek, rw [←hanek, mul_one] } },
  { dec_trivial }
end
/-
theorem solution_hybrid
  {p q : ℕ}
  (hp : nat.prime p)
  (hq : nat.prime q)
  (p_lt_q : p < q)
  (p_ne_two : p ≠ 2)
  (q_ne_two : q ≠ 2)
  (consecutive : ∀ k, p < k → k < q → ¬ nat.prime k) :
∃ a b c, p + q = a * b * c
∧ a > 1 ∧ b > 1 ∧ c > 1 :=
begin
  have hp1 := hp.eq_two_or_odd.resolve_left p_ne_two,
  have hq1 := hq.eq_two_or_odd.resolve_left q_ne_two,
  rw ←nat.odd_iff at hp1 hq1,
  obtain ⟨k, hk⟩ : even (p + q),
  { simp at hp1 hq1,
    simp [hp1, hq1] with parity_simps },
  have : ¬nat.prime k,
  { apply consecutive; linarith },
  obtain ⟨a, hadvd, hane1, hanek⟩ := nat.exists_dvd_of_not_prime (by linarith [hp.two_le, hq.two_le]) this,
  use [2, a, k / a],
  have hapos : 0 < a,
  { rw [nat.pos_iff_ne_zero],
    rintro rfl,
    rw [zero_dvd_iff] at hadvd,
    exact hanek hadvd.symm },
    have d0 : 0 < k,
    {
        omega,
    },
    have d2 : 2 ≤ k,
    {
        have := nat.prime.two_le hp,
        omega,
    },
  refine ⟨_, _, _, _⟩,
  { sorry }, --rw [hk, nat.mul_div_cancel' hadvd, mul_comm] },
  { omega },
  { have npos := nat.pos_of_dvd_of_pos hadvd d0,
    have nltd := nat.le_of_dvd d0 hadvd,

    omega },
    /-
    obtain ⟨b, rfl⟩ := hadvd,
    have : b ≠ 0,
    { rintro rfl,
      linarith [hp.two_le, hq.two_le, hk] },
    rw mul_comm,
    rw nat.mul_div_cancel _ hapos,
    apply lt_of_le_of_ne,
    { rwa [nat.succ_le_iff, nat.pos_iff_ne_zero] },
    { contrapose! hanek, rw [←hanek, mul_one] } },
    -/
  { change _ < _,
    apply (mul_lt_mul_left hapos).mp,
        rw nat.mul_div_cancel',
    omega,
      dec_trivial }
end
-/

theorem solution'
  {p q : ℕ}
  (hp : nat.prime p)
  (hq : nat.prime q)
  (p_lt_q : p < q)
  (p_ne_two : p ≠ 2)
  (q_ne_two : q ≠ 2)
  (consecutive : ∀ k, p < k → k < q → ¬ nat.prime k) :
∃ a b c, p + q = a * b * c
∧ a > 1 ∧ b > 1 ∧ c > 1 :=
begin
    have op : ¬ even p,
    {
        rw nat.not_even_iff,
        exact hp.eq_two_or_odd.resolve_left p_ne_two,
    },
    have oq : ¬ even q,
    {
        rw nat.not_even_iff,
        exact hq.eq_two_or_odd.resolve_left q_ne_two,
    },
    have epq : even (p + q),
    {
        rw nat.even_add,
        simp [op, oq],
    },
    rw even_iff_two_dvd at epq,
    cases (exists_eq_mul_right_of_dvd epq) with d hd,
    have compd : ¬ nat.prime d,
    {
        apply consecutive;
        omega,
    },
    have d2 : 2 ≤ d,
    {
        have k := nat.prime.two_le hp,
        omega,
    },
    have d0 : d > 0,
    {
        omega,
    },
    rcases (nat.exists_dvd_of_not_prime d2 compd) with ⟨n, hn1, hn2, hn3⟩,
    have npos := nat.pos_of_dvd_of_pos hn1 d0,
    have nltd := nat.le_of_dvd d0 hn1,
    use [2, n, d/n],
    split,
    {
        rw mul_assoc,
        rw nat.mul_div_cancel';
        assumption,
    },
    split,
    {
        omega,
    },
    split,
    {
        omega,
    },
    {
        apply (mul_lt_mul_left npos).mp,
        rw nat.mul_div_cancel',
        omega,
        assumption,
    },
end

example (p q : ℕ → Prop) : (∀ n, p n) ∧ (∀ n, q n) ↔ (∀ n, p n ∧ q n) := forall_and_distrib.symm
