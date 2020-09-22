import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import tactic
import .primes

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
