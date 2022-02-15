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
  apply eq_pow (zero_lt_two.trans_le n2).ne',
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

lemma associated_of_dvd {a p : ℤ}
  (ha : odd_prime_or_four a)
  (hp : odd_prime_or_four p)
  (h: p ∣ a) : associated p a :=
begin
  obtain (rfl|⟨ap, aodd⟩) := ha;
  obtain (rfl|⟨pp, podd⟩) := hp,
  { refl },
  { exfalso,
    have h0 : (4 : ℤ) = 2 ^ 2,
    { norm_num },
    rw h0 at h,
    refine int.even_iff_not_odd.mp (associated.dvd _) podd,
    exact ((pp.dvd_prime_iff_associated int.prime_two).mp (pp.dvd_of_dvd_pow h)).symm },
  { exfalso,
    rw int.odd_iff_not_even at aodd,
    refine aodd (dvd_trans _ h),
    norm_num },
  { rwa prime.dvd_prime_iff_associated pp ap at h }
end

lemma dvd_or_dvd {a p x : ℤ}
  (ha : odd_prime_or_four a)
  (hp : odd_prime_or_four p)
  (hdvd : p ∣ a * x) : p ∣ a ∨ p ∣ x :=
begin
  obtain (rfl|⟨pp, podd⟩) := hp,
  { obtain (rfl|⟨ap, aodd⟩) := ha,
    { exact or.inl dvd_rfl },
    { right,
      have : (4 : ℤ) = 2 ^ 2,
      { norm_num },
      rw this at hdvd ⊢,
      apply int.prime_two.pow_dvd_of_dvd_mul_left _ _ hdvd,
      rwa [←even_iff_two_dvd, ←int.odd_iff_not_even] } },
  { exact (pp.dvd_or_dvd hdvd) }
end

lemma exists_associated_mem_of_dvd_prod''
  {p : ℤ} (hp : odd_prime_or_four p)
  {s : multiset ℤ}
  (hs : ∀ r ∈ s, odd_prime_or_four r)
  (hdvd : p ∣ s.prod) :
  ∃ q ∈ s, associated p q :=
begin
  induction s using multiset.induction_on with a s ih hs generalizing hs hdvd,
  { simpa [hp.not_unit, ←is_unit_iff_dvd_one] using hdvd },
  { rw [multiset.prod_cons] at hdvd,
    have := hs a (multiset.mem_cons_self _ _),
    obtain h|h := dvd_or_dvd this hp hdvd,
    { exact ⟨a, multiset.mem_cons_self _ _, associated_of_dvd this hp h⟩ },
    { obtain ⟨q, hq₁, hq₂⟩ := ih (λ r hr, hs _ (multiset.mem_cons_of_mem hr)) h,
      exact ⟨q, multiset.mem_cons_of_mem hq₁, hq₂⟩ } }
end

lemma factors_unique_prod' : ∀{f g : multiset ℤ},
  (∀x∈f, odd_prime_or_four x) →
  (∀x∈g, odd_prime_or_four x) →
  (associated f.prod g.prod) →
  multiset.rel associated f g :=
begin
  intros f,
  refine multiset.induction_on f _ _,
  { rintros g - hg h,
    rw [multiset.prod_zero] at h,
    rw [multiset.rel_zero_left],
    apply multiset.eq_zero_of_forall_not_mem,
    intros x hx,
    apply (hg x hx).not_unit,
    rw is_unit_iff_dvd_one,
    exact dvd_trans (multiset.dvd_prod hx) h.symm.dvd },
  { intros p f ih g hf hg hfg,
    have hp := hf p (multiset.mem_cons_self _ _),
    have hdvd : p ∣ g.prod,
    { rw [←hfg.dvd_iff_dvd_right, multiset.prod_cons],
      exact dvd_mul_right _ _ },
    obtain ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod'' hp hg hdvd,
    rw ← multiset.cons_erase hbg,
    apply multiset.rel.cons hb,
    apply ih _ _ _,
    { exact (λ q hq, hf _ (multiset.mem_cons_of_mem hq)) },
    { exact (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq)) },
    { apply associated.of_mul_left _ hb hp.ne_zero,
      rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg] } },
end
