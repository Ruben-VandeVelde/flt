import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import tactic

lemma nat.mem_factors' {n p} (hn : 0 < n) : p ∈ nat.factors n ↔ nat.prime p ∧ p ∣ n :=
⟨λ h, ⟨nat.mem_factors h, (nat.mem_factors_iff_dvd hn (nat.mem_factors h)).mp h⟩,
 λ ⟨hprime, hdvd⟩, (nat.mem_factors_iff_dvd hn hprime).mpr hdvd⟩

lemma l0 {n : ℕ} (h : 2 < 2 ^ n) : 2 ≤ n :=
begin
  rcases n with (_|_|_),
  { exfalso, norm_num at h },
  { exfalso, exact lt_irrefl _ h, },
  { rw le_add_iff_nonneg_left (2 : nat),
    exact zero_le _ }
end

example (n m : nat) (h : m ≤ n) : m + (n - m) = n := by library_search

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
    { push_neg at h,
      have h0 : 0 < n := by linarith,
      set k := n.factors.length,
      use 2 ^ (k - 2),

      have h2 : n = 2 ^ k,
      { rw [←nat.prod_factors h0, ←nat.pow_eq_pow],
        have := list.prod_repeat 2 k,
        refine trans _ this,
        suffices : n.factors = list.repeat 2 k, { rw this },
        apply list.eq_repeat_of_mem,
        intros p hp,
        rw nat.mem_factors' h0 at hp,
        cases nat.prime.eq_two_or_odd hp.left,
        { assumption },
        { have := h p hp.right hp.left,
          contradiction } },

      have h3 : 2 ≤ k,
      { rw h2 at n2,
        apply l0 n2 },

      calc n
          = 2 ^ k : _
      ... = 2 ^ (2 + (k - 2)) : _
      ... = 2 ^ 2 * 2 ^ (k - 2) : nat.pow_add 2 2 (k - 2)
      ... = 4 * 2 ^ (k - 2) : by norm_num,
      exact h2,
      rw nat.add_sub_of_le,
      exact h3,
      },
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
