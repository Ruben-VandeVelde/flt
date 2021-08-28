import algebraic_geometry.EllipticCurve
import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import tactic
import number_theory.fermat4
import .primes
import .odd_prime_or_four
import .euler

lemma flt_four
  {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
  a ^ 4 + b ^ 4 ≠ c ^ 4 :=
not_fermat_4 ha hb

lemma flt_primes
  {p : ℕ} {a b c : ℤ} (h : 5 ≤ p) (hp : p.prime) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
  a ^ p + b ^ p ≠ c ^ p :=
begin
  intro H,
  let disc : ℚ := 16 * (a ^ p * b ^ p * c ^ p) ^ 2,
  have disc_ne_zero : disc ≠ 0,
  { dsimp [disc],
    refine mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero _ _) _));
    apply pow_ne_zero; assumption_mod_cast },
  let frey : EllipticCurve ℚ :=
  { a1 := 0,
    a2 := b ^ p - a ^p,
    a3 := 0,
    a4 := - (a ^ p * b ^ p),
    a6 := 0,
    disc_unit := units.mk0 _ disc_ne_zero,
    disc_unit_eq := by {
      rw [←@int.cast_inj ℚ, int.cast_pow] at H, simp [EllipticCurve.disc_aux, ←H], ring } },
  -- by wiles
  sorry,
end

lemma flt_composite
  {p n : ℕ} {a b c : ℤ} (h : p ∣ n) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (g : a ^ n + b ^ n = c ^ n):
  ∃ a' b' c' : ℤ, a' ≠ 0 ∧ b' ≠ 0 ∧ c' ≠ 0 ∧ a' ^ p + b' ^ p = c' ^ p :=
begin
  obtain ⟨m, rfl⟩ := h,
  rw [mul_comm, pow_mul, pow_mul, pow_mul] at g,
  exact ⟨a ^ m, b ^ m, c ^ m, pow_ne_zero _ ha, pow_ne_zero _ hb, pow_ne_zero _ hc, g⟩,
end

theorem flt {n : ℕ} {a b c : ℤ} (h : 2 < n) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
  a ^ n + b ^ n ≠ c ^ n :=
begin
  intro H,
  zify at h,
  obtain ⟨p, hdvd, hp⟩ := odd_prime_or_four.exists_and_dvd h,
  rw [int.coe_nat_dvd_right] at hdvd,
  obtain ⟨a', b', c', ha', hb', hc', hcomp⟩ := flt_composite hdvd ha hb hc H,
  obtain rfl|⟨hp, hodd⟩ := hp,
  { exact flt_four ha' hb' hc' hcomp },
  { by_cases h3 : p.nat_abs = 3,
    { rw h3 at hcomp,
      apply flt_three ha' hb' hc' hcomp },
    { rw int.prime_iff_nat_abs_prime at hp,
      rw [←int.nat_abs_odd, nat.odd_iff_not_even] at hodd,
      refine flt_primes _ hp ha' hb' hc' hcomp,
      by_contradiction hcon,
      push_neg at hcon,
      have := hp.two_le,
      interval_cases p.nat_abs with hp',
      { rw hp' at hodd, exact hodd (even_bit0 1) },
      { exact h3 hp' },
      { rw hp' at hodd, exact hodd (even_bit0 2) } } },
end
