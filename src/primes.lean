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

section
variables {α : Type*} [ordered_semiring α] [nontrivial α] {a b c d : α}

@[field_simps] lemma three_ne_zero : (3:α) ≠ 0 :=
zero_lt_three.ne.symm

@[field_simps] lemma four_ne_zero : (4:α) ≠ 0 :=
zero_lt_four.ne.symm

end

lemma eq_pow
  {n p : ℕ}
  (hpos : n ≠ 0)
  (h : ∀ {d}, nat.prime d → d ∣ n → d = p) :
  n = p ^ n.factors.length :=
begin
  set k := n.factors.length,
  rw [←nat.prod_factors hpos, ←list.prod_repeat p k],
  congr,
  apply list.eq_repeat_of_mem,
  intros d hd,
  rw nat.mem_factors hpos at hd,
  exact h hd.left hd.right,
end

lemma l0 {n : ℕ} (h : 2 < 2 ^ n) : 2 ≤ n :=
begin
  rcases n with (_|_|_),
  { exfalso, norm_num at h },
  { exfalso, exact lt_irrefl _ h, },
  { rw le_add_iff_nonneg_left (2 : nat),
    exact zero_le _ }
end

lemma exists_odd_prime_and_dvd_or_two_pow
  (n : ℕ) : (∃ k : ℕ, n = 2 ^ k) ∨ ∃ p, nat.prime p ∧ p ∣ n ∧ odd p :=
begin
  obtain rfl|hn := eq_or_ne n 0,
  { exact or.inr ⟨3, nat.prime_three, dvd_zero 3, nat.odd_iff_not_even.mpr (nat.not_even_bit1 1)⟩ },
  rw or_iff_not_imp_right,
  intro H,
  push_neg at H,
  use n.factors.length,
  apply eq_pow hn,
  intros p hprime hdvd,
  apply hprime.eq_two_or_odd.resolve_right,
  rw ←nat.odd_iff,
  exact H p hprime hdvd,
end

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
  obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero (pos_of_gt hn).ne',
  rw nat.succ_lt_succ_iff at hn,
  obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero hn.ne',
  rw pow_succ at h,
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

-- todo norm_num for prime ℤ
lemma int.prime_two : prime (2 : ℤ) := nat.prime_iff_prime_int.mp nat.prime_two
lemma int.prime_three : prime (3 : ℤ) := nat.prime_iff_prime_int.mp nat.prime_three

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
