import .primes

def odd_prime_or_four (z : ℤ) : Prop :=
  z = 4 ∨ (prime z ∧ odd z)

lemma odd_prime_or_four.ne_zero {z : ℤ} (h : odd_prime_or_four z) : z ≠ 0 :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { norm_num },
  { exact h.ne_zero }
end

lemma odd_prime_or_four.ne_one {z : ℤ} (h : odd_prime_or_four z) : z ≠ 1 :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { norm_num },
  { exact h.ne_one }
end

lemma odd_prime_or_four.one_lt_abs {z : ℤ} (h : odd_prime_or_four z) : 1 < abs z :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { rw int.abs_eq_nat_abs, norm_cast, norm_num },
  { rw int.abs_eq_nat_abs,
    rw int.prime_iff_nat_abs_prime at h,
    norm_cast,
    exact h.one_lt, }
end

lemma odd_prime_or_four.not_unit {z : ℤ} (h : odd_prime_or_four z) : ¬ is_unit z :=
begin
  obtain rfl|⟨h, -⟩ := h,
  { rw is_unit_iff_dvd_one, norm_num },
  { exact h.not_unit }
end

lemma odd_prime_or_four.abs {z : ℤ} (h : odd_prime_or_four z) : odd_prime_or_four (abs z) :=
begin
  obtain rfl|⟨hp, ho⟩ := h,
  { left, rw abs_eq_self, norm_num },
  { right, exact ⟨hp.abs, odd_abs.mpr ho⟩ }
end

lemma exists_odd_prime_and_dvd_or_two_pow
  {n : ℕ} (n2 : 2 ≤ n) : (∃ k : ℕ, n = 2 ^ k) ∨ ∃ p, nat.prime p ∧ p ∣ n ∧ odd p :=
begin
  rw or_iff_not_imp_right,
  intro H,
  push_neg at H,
  use n.factors.length,
  apply eq_pow (zero_lt_two.trans_le n2),
  intros p hprime hdvd,
  apply hprime.eq_two_or_odd.resolve_right,
  rw ←nat.odd_iff,
  exact H p hprime hdvd,
end

lemma odd_prime_or_four.exists_and_dvd
  {n : ℤ} (n2 : 2 < n) : ∃ p, p ∣ n ∧ odd_prime_or_four p :=
begin
  lift n to ℕ using (zero_lt_two.trans n2).le,
  norm_cast at n2,
  obtain ⟨k, h2⟩|⟨p, hp, hdvd, hodd⟩ := exists_odd_prime_and_dvd_or_two_pow n2.le,
  { refine ⟨4, _, _⟩,
    { use 2 ^ (k - 2),
      norm_cast,

      have h3 : 2 ≤ k,
      { rw h2 at n2,
        apply l0 n2 },

      calc n
          = 2 ^ k : h2
      ... = 2 ^ 2 * 2 ^ (k - 2) : (pow_mul_pow_sub _ h3).symm
      ... = 4 * 2 ^ (k - 2) : by norm_num },
    { left, refl } },
  { rw nat.prime_iff_prime_int at hp,
    rw ←int.odd_coe_nat at hodd,
    exact ⟨p, int.coe_nat_dvd.mpr hdvd, or.inr ⟨hp, hodd⟩⟩ },
end
