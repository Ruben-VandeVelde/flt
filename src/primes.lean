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
  (hpos : 0 < n)
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

lemma int.four_dvd_add_or_sub_of_odd {a b : ℤ} (ha : odd a) (hb : odd b) : 4 ∣ a + b ∨ 4 ∣ a - b :=
begin
  obtain ⟨m, rfl⟩ := ha,
  obtain ⟨n, rfl⟩ := hb,
  obtain h|h := int.even_or_odd (m + n),
  { right,
    rw [int.even_add, ←int.even_sub] at h,
    obtain ⟨k, hk⟩ := h,
    convert dvd_mul_right 4 k,
    rw [eq_add_of_sub_eq hk],
    rw [mul_add, add_assoc, add_sub_cancel, ←mul_assoc],
    norm_num },
  { left,
    obtain ⟨k, hk⟩ := h,
    convert dvd_mul_right 4 (k + 1),
    rw [eq_sub_of_add_eq hk, add_right_comm, ←add_sub, mul_add, mul_sub, add_assoc, add_assoc,
      sub_add, add_assoc, ←sub_sub (2 * n), sub_self, zero_sub, sub_neg_eq_add, ←mul_assoc,
      mul_add],
    norm_num },
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
variables [comm_cancel_monoid_with_zero α]


lemma pow_not_prime {x : α} {n : ℕ} (hn : n ≠ 1) : ¬ prime (x ^ n) :=
λ hp, hp.not_unit $ is_unit.pow _ $ is_unit_of_irreducible_pow hn $ hp.irreducible

end

@[norm_cast]
lemma int.of_nat_is_unit {n : ℕ} : is_unit (n : ℤ) ↔ is_unit n :=
by rw [nat.is_unit_iff, int.is_unit_iff_nat_abs_eq, int.nat_abs_of_nat]

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

lemma int.is_unit_iff_abs_eq {x : ℤ} : is_unit x ↔ abs x = 1 :=
by rw [int.is_unit_iff_nat_abs_eq, int.abs_eq_nat_abs, ←int.coe_nat_one, int.coe_nat_inj']

theorem int.exists_prime_and_dvd {n : ℤ} (n2 : 2 ≤ n.nat_abs) : ∃ p, prime p ∧ p ∣ n :=
begin
  obtain ⟨p, pp, pd⟩ := nat.exists_prime_and_dvd n2,
  exact ⟨p, nat.prime_iff_prime_int.mp pp, int.coe_nat_dvd_left.mpr pd⟩,
end

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
