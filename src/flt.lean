import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import tactic

lemma exists_prime_and_dvd'
  {n : ℕ} (n2 : 2 < n) : ∃ p, p ∣ n ∧ (p = 4 ∨ (nat.prime p ∧ p % 2 = 1)) :=
begin
  by_cases ∃ p, p ∣ n ∧ nat.prime p ∧ p % 2 = 1,
  { obtain ⟨p, hdvd, hp, hodd⟩ := h,
    have pnetwo : p ≠ 2,
    { intro ptwo,
      subst ptwo,
      norm_num at hodd },
    exact ⟨p, hdvd, or.inr ⟨hp, hodd⟩⟩ },
  { use 4,
    split,
    { have h0 : ∀ p ∣ n, nat.prime p → p = 2,
      { intros p hdvd hp,
        push_neg at h,
        have := h p hdvd hp,
        cases nat.prime.eq_two_or_odd hp,
        { assumption },
        { contradiction } },
      have h' : ∃ k : ℕ, n = 2 ^ k,
      { rw ← nat.prod_factors (by linarith : 0 < n),
        use (nat.factors n).length,
        rw ←nat.pow_eq_pow,
        have : n.factors = list.repeat 2 n.factors.length,
        { apply list.eq_repeat_of_mem,
          intros p hp,
          have := nat.mem_factors hp,
          have := (nat.mem_factors_iff_dvd (by linarith) this).mp hp,
          apply h0; assumption },
        conv_lhs { rw this },
        apply list.prod_repeat },
      obtain ⟨k, hk⟩ := h',
      have : 2 ≤ k,
      { subst hk,
        rcases k with (_|_|_),
        { exfalso, norm_num at n2 },
        { exfalso, exact lt_irrefl _ n2, },
        { rw le_add_iff_nonneg_left (2 : nat), exact zero_le _ }
      },
      have : n = 2 ^ (k - 2) * 4,
      { calc _
            = 2 ^ k : hk
        ... = 2 ^ (k - 2 + 2) : by rw nat.sub_add_cancel this
        ... = 2 ^ (k - 2) * 2 ^ 2 : nat.pow_add 2 (k - 2) 2
        ... = _ : by norm_num
      },
      rw this,
      apply dvd_mul_left },
    { left, refl } },
end

lemma flt_three
  (a b c : ℕ+) :
  a ^ 3 + b ^ 3 ≠ c ^ 3 :=
begin
  sorry,
end

lemma flt_four
  (a b c : ℕ+) :
  a ^ 4 + b ^ 4 ≠ c ^ 4 :=
begin
  sorry,
end

lemma flt_primes
  (p : ℕ) (a b c : ℕ+) (h : 5 ≤ p) (hp : p.prime) :
  a ^ p + b ^ p ≠ c ^ p :=
begin
--  let frey := sorry, --y ^ 2 = x * ( x - a ^ p ) * ( x + b ^ p )
  sorry,
end

lemma flt_composite
  (p n : ℕ) (a b c : ℕ+) (h : p ∣ n) (g : a ^ n + b ^ n = c ^ n):
  ∃ a' b' c' : ℕ+, a' ^ p + b' ^ p = c' ^ p :=
begin
  obtain ⟨m, hm⟩ := h,
  subst hm,
  rw [mul_comm, pow_mul, pow_mul, pow_mul] at g,
  use [a ^ m, b ^ m, c ^ m],
  exact g,
end

theorem flt (n : ℕ) (a b c : ℕ+) (h : 2 < n) : a ^ n + b ^ n ≠ c ^ n :=
begin
  by_contradiction H,
  push_neg at H,
  obtain ⟨p, hdvd, hp⟩ := exists_prime_and_dvd' h,
  obtain ⟨a', b', c', hcomp⟩ := flt_composite p n a b c hdvd H,
  cases hp,
  { subst hp,
    apply flt_four a' b' c' hcomp },
  { obtain ⟨hp, hodd⟩ := hp,
    by_cases h3 : p = 3,
    { subst h3,
      apply flt_three a' b' c' hcomp },
    { apply flt_primes p a' b' c' _ hp hcomp,
      rcases p with (_|_|_|_|_|_),
      { exfalso, exact nat.not_prime_zero hp },
      { exfalso, exact nat.not_prime_one hp },
      { exfalso, norm_num at hodd },
      { exfalso, apply h3, refl },
      { exfalso, norm_num at hodd },
      { rw le_add_iff_nonneg_left (5 : nat), exact zero_le _ } },
  },
end
