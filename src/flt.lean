import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import tactic
import .primes
import .odd_prime_or_four

lemma flt_three
  (a b c : ℤ) :
  a ^ 3 + b ^ 3 ≠ c ^ 3 :=
begin
  sorry,
end

lemma flt_four
  (a b c : ℤ) :
  a ^ 4 + b ^ 4 ≠ c ^ 4 :=
begin
  sorry,
end

lemma flt_primes
  (p : ℕ) (a b c : ℤ) (h : 5 ≤ p) (hp : p.prime) :
  a ^ p + b ^ p ≠ c ^ p :=
begin
--  let frey := sorry, --y ^ 2 = x * ( x - a ^ p ) * ( x + b ^ p )
  sorry,
end

lemma flt_composite
  (p n : ℕ) (a b c : ℤ) (h : p ∣ n) (g : a ^ n + b ^ n = c ^ n):
  ∃ a' b' c' : ℤ, a' ^ p + b' ^ p = c' ^ p :=
begin
  obtain ⟨m, hm⟩ := h,
  subst hm,
  rw [mul_comm, pow_mul, pow_mul, pow_mul] at g,
  use [a ^ m, b ^ m, c ^ m],
  exact g,
end

theorem flt (n : ℕ) (a b c : ℤ) (h : 2 < n) : a ^ n + b ^ n ≠ c ^ n :=
begin
  by_contradiction H,
  push_neg at H,
  zify at h,
  obtain ⟨p, hdvd, hp⟩ := odd_prime_or_four.exists_and_dvd h,
  rw [int.coe_nat_dvd_right] at hdvd,
  obtain ⟨a', b', c', hcomp⟩ := flt_composite p.nat_abs n a b c hdvd H,
  cases hp,
  { subst hp,
    apply flt_four a' b' c' hcomp },
  { obtain ⟨hp, hodd⟩ := hp,
    by_cases h3 : p.nat_abs = 3,
    { rw h3 at hcomp,
      apply flt_three a' b' c' hcomp },
    { rw int.prime_iff_nat_abs_prime at hp,
      rw [←int.nat_abs_odd, nat.odd_iff_not_even] at hodd,
      apply flt_primes p.nat_abs a' b' c' _ hp hcomp,
      by_contradiction hcon,
      push_neg at hcon,
      have := hp.two_le,
      interval_cases p.nat_abs with hp',
      { rw hp' at hodd, exact hodd (even_bit0 1) },
      { exact h3 hp' },
      { rw hp' at hodd, exact hodd (even_bit0 2) } } },
end
