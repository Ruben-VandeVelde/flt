/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import algebraic_geometry.elliptic_curve.weierstrass
import number_theory.fermat4
import .primes
import .odd_prime_or_four
import .euler
import mod_forms.modularity_conjecture

lemma flt_four
  {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
  a ^ 4 + b ^ 4 ≠ c ^ 4 :=
not_fermat_4 ha hb

def frey (p : ℕ) (a b : ℤ) (disc_ne_zero : (16 * (a ^ p * b ^ p * (a ^ p + b ^ p)) ^ 2 : ℚ) ≠ 0) :
  elliptic_curve ℚ :=
{ a₁ := 0,
  a₂ := b ^ p - a ^p,
  a₃ := 0,
  a₄ := - (a ^ p * b ^ p),
  a₆ := 0,
  Δ' := units.mk0 _ disc_ne_zero,
  coe_Δ' := by { simp [elliptic_curve.Δ'], ring } }

def frey.mk (p : ℕ) {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (H : a ^ p + b ^ p = c ^ p) :
  elliptic_curve ℚ :=
frey p a b begin
  let disc : ℚ := 16 * (a ^ p * b ^ p * c ^ p) ^ 2,
  have disc_ne_zero : disc ≠ 0,
  { dsimp [disc],
    refine mul_ne_zero (by norm_num) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero _ _) _));
    apply pow_ne_zero; assumption_mod_cast },
  rw [←@int.cast_inj ℚ, int.cast_add, int.cast_pow, int.cast_pow, int.cast_pow] at H,
  rwa [H],
end

lemma flt_primes
  {p : ℕ} {a b c : ℤ} (h : 5 ≤ p) (hp : p.prime) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
  a ^ p + b ^ p ≠ c ^ p :=
begin
  intro H,
  let frey : elliptic_curve ℚ := frey.mk p ha hb hc H,
  obtain ⟨n, f, hf, h'⟩ := modularity_conjecture frey,
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
