import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import ring_theory.coprime.lemmas
import ring_theory.int.basic
import ring_theory.euclidean_domain
import ring_theory.noetherian
import ring_theory.principal_ideal_domain
import ring_theory.prime
import ring_theory.unique_factorization_domain
import tactic

lemma is_coprime_mul_unit_left {R : Type*} [comm_semiring R] {x : R} (hu : is_unit x) (y z : R) :
  is_coprime (x * y) (x * z) ↔ is_coprime y z :=
⟨λ ⟨a, b, h⟩, ⟨a * x, b * x, by { rwa [mul_assoc, mul_assoc] }⟩,
  λ ⟨a, b, h⟩,
    let ⟨x', hx⟩ := hu.exists_left_inv in
    ⟨a * x', b * x', by rwa
      [←mul_assoc (a * x'), mul_assoc a, ←mul_assoc (b * x'), mul_assoc b, hx, mul_one, mul_one]⟩⟩

lemma is_coprime_mul_unit_right {R : Type*} [comm_semiring R] {x : R} (hu : is_unit x) (y z : R) :
  is_coprime (y * x) (z * x) ↔ is_coprime y z :=
by rw [mul_comm y, mul_comm z, is_coprime_mul_unit_left hu]

section
variables {R : Type*} [comm_ring R] {x y z : R}
lemma coprime_add_self_pow
  {n : ℕ}
  (hn : 0 < n)
  (hsoln : x ^ n + y ^ n = z ^ n)
  (hxx : is_coprime x y)
   : is_coprime x z :=
begin
  have := is_coprime.mul_add_left_right hxx.pow 1,
  rwa [mul_one, hsoln, is_coprime.pow_iff hn hn] at this,
end
end

-- Edwards p49 introduction
lemma int.factor_div (a x : ℤ) (hodd : odd x) :
  ∃ (m c : ℤ), c + m * x = a ∧ 2 * c.nat_abs < x.nat_abs :=
begin
  have h0' : x ≠ 0,
  { rintro rfl,
    simpa only [int.even_zero, not_true, int.odd_iff_not_even] using hodd },
  set c := a % x with hc,
  by_cases H : 2 * c.nat_abs < x.nat_abs,
  { exact ⟨a / x, c, int.mod_add_div' a x, H⟩ },
  { push_neg at H,
    refine ⟨(a + abs x) / x, c - abs x, _, _⟩,
    { have := self_dvd_abs x,
      rw [int.add_div_of_dvd_right this, add_mul, int.div_mul_cancel this, sub_add_add_cancel, hc,
        int.mod_add_div'] },
    { zify at ⊢ H,
      have hcnonneg := int.mod_nonneg a h0',
      have := int.mod_lt a h0',
      rw [int.nat_abs_of_nonneg hcnonneg] at H,
      rw [←int.nat_abs_neg, neg_sub, int.nat_abs_of_nonneg (sub_nonneg_of_le this.le),
        mul_sub, sub_lt_iff_lt_add, two_mul, int.abs_eq_nat_abs, add_lt_add_iff_left],
      apply lt_of_le_of_ne H,
      contrapose! hodd with heqtwomul,
      rw [←int.even_iff_not_odd, ←int.nat_abs_even, ←int.even_coe_nat],
      exact ⟨_, heqtwomul⟩ } },
end

section
theorem is_unit_of_irreducible_pow {α} [monoid α] {x : α} {n : ℕ} (hn : n ≠ 1) :
  irreducible (x ^ n) → is_unit x :=
begin
  obtain hn|hn := hn.lt_or_lt,
  { simp only [nat.lt_one_iff.mp hn, forall_false_left, not_irreducible_one, pow_zero] },
  intro h,
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt hn,
  rw [pow_succ, add_comm] at h,
  exact (or_iff_left_of_imp ((is_unit_pos_pow_iff (nat.succ_pos _)).mp)).mp (of_irreducible_mul h)
end


variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [cancel_comm_monoid_with_zero α]


lemma pow_not_prime {x : α} {n : ℕ} (hn : n ≠ 1) : ¬ prime (x ^ n) :=
λ hp, hp.not_unit $ is_unit.pow _ $ is_unit_of_irreducible_pow hn $ hp.irreducible

end

lemma two_not_cube (r : ℕ) : r ^ 3 ≠ 2 :=
begin
  have : 1 ≤ 3,
  { norm_num },
  apply monotone.ne_of_lt_of_lt_nat (nat.pow_left_strict_mono this).monotone 1; norm_num,
end

lemma int.two_not_cube (r : ℤ) : r ^ 3 ≠ 2 :=
begin
  intro H,
  apply two_not_cube r.nat_abs,
  rw [←int.nat_abs_pow, H],
  norm_num,
end

-- todo square neg_square and neg_pow_bit0

lemma int.dvd_mul_cancel_prime {p : ℕ} {n k : ℤ}
  (hne : k.nat_abs ≠ p)
  (hp : nat.prime p)
  (hk : prime k)
  (h : k ∣ p * n) : k ∣ n :=
begin
  apply (prime.dvd_or_dvd hk h).resolve_left,
  rw int.prime_iff_nat_abs_prime at hk,
  rwa [int.coe_nat_dvd_right, nat.prime_dvd_prime_iff_eq hk hp]
end

lemma int.dvd_mul_cancel_prime' {p k m n : ℤ}
  (hdvd1 : ¬(p ∣ m))
  (hdvd2 : k ∣ m)
  (hp : prime p)
  (hk : prime k)
  (h : k ∣ p * n) : k ∣ n :=
begin
  rw int.prime_iff_nat_abs_prime at hp,
  apply int.dvd_mul_cancel_prime _ hp hk,
  { apply dvd_trans h (mul_dvd_mul_right _ _),
    rw int.dvd_nat_abs },
  { rintro hk,
    apply hdvd1,
    rwa [←int.nat_abs_dvd, ←hk, int.nat_abs_dvd] }
end

lemma int.abs_sign {a : ℤ} (ha : a ≠ 0) : |a.sign| = 1 :=
begin
  cases ha.lt_or_lt with ha ha,
  { rw [int.sign_eq_neg_one_of_neg ha, abs_neg, abs_one] },
  { rw [int.sign_eq_one_of_pos ha, abs_one] },
end

namespace int
theorem gcd_pos_iff {i j : ℤ} : 0 < gcd i j ↔ i ≠ 0 ∨ j ≠ 0 :=
pos_iff_ne_zero.trans $ (not_congr int.gcd_eq_zero_iff).trans not_and_distrib
end int
