import data.int.basic
import data.int.parity
import data.nat.gcd
import ring_theory.int.basic
import tactic
import tactic.slim_check
import .primes

lemma l1_4_coprime
  {n : ℕ}
  (hn : 0 < n)
  {x y : ℤ}
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hp : prime (x ^ 2 + n * y ^ 2)) :
  is_coprime x y := 
begin
  rw ←int.gcd_eq_one_iff_coprime,
  have hp' := irreducible_of_prime hp,
  unfold irreducible at hp',
  contrapose! hp',

  intros notunit,
  have : 1 < x.gcd y,
  { refine hp'.symm.le_iff_lt.mp _,
    rw nat.succ_le_iff,
    refine pos_iff_ne_zero.mpr _,
    exact int.gcd_ne_zero_iff.mpr (or.inl hx) },
  obtain ⟨c, hc⟩ : (x.gcd y : ℤ) ∣ x^2 + n * y ^ 2,
  { apply dvd_add,
    { apply dvd_pow _ two_ne_zero,
      apply int.gcd_dvd_left},
    { apply dvd_mul_of_dvd_right,
      apply dvd_pow _ two_ne_zero,
      apply int.gcd_dvd_right} }, 
  use [x.gcd y, c, hc],
  split,
  { norm_cast, rwa [nat.is_unit_iff], },
  contrapose! notunit,
  rw is_unit_int at notunit,

  have hcnat : (x ^ 2 + n * y ^ 2).nat_abs = ((x.gcd y : ℤ) * c).nat_abs, rw hc,
  zify at hcnat,
  have : 0 ≤ x ^ 2 + n * y ^ 2,
  { apply add_nonneg,
    { exact (pow_two_nonneg _) },
    { apply mul_nonneg (int.coe_nat_nonneg n),
      exact (pow_two_nonneg _) } },
  rw [int.nat_abs_of_nonneg this, int.nat_abs_mul, int.nat_abs_of_nat, int.coe_nat_mul, notunit] at hcnat,
  simp only [mul_one, int.coe_nat_one, zero_add] at hcnat,
  have := int.gcd_dvd_left x y,
  have : x ∣ x ^ 2 := dvd_pow (dvd_refl x) two_ne_zero,
  have := dvd_trans (int.gcd_dvd_left x y) (dvd_pow (dvd_refl x) two_ne_zero),
  rw ←hcnat at this,
  have xxx : 0 < x ^ 2 := lt_of_le_of_ne (pow_two_nonneg x) (pow_ne_zero 2 hx).symm,
  have := int.le_of_dvd xxx this,
  simp only [add_le_iff_nonpos_right] at this,
  exfalso,
  apply hy,
  rw ←pow_eq_zero_iff zero_lt_two,
  apply le_antisymm _ (pow_two_nonneg y),
  apply nonpos_of_mul_nonpos_left this,
  rwa [←int.coe_nat_zero, int.coe_nat_lt],

  apply_instance,
end

lemma l1_4
  (a b x y : ℤ)
  (habcoprime : is_coprime a b)
  (hdvd : x ^ 2 + y ^ 2 ∣ a ^ 2 + b ^ 2)
  (hp : prime (x ^ 2 + y ^ 2))
  :
  ∃ c d,
    a ^ 2 + b ^ 2 = (x ^ 2 + y ^ 2) * (c ^ 2 + d ^ 2) ∧
    is_coprime c d
  := 
begin
  obtain ⟨hx, hy⟩ : x ≠ 0 ∧ y ≠ 0,
  { split;
    { rintro rfl,
      rw [zero_pow zero_lt_two] at hp,
      simp only [zero_add, add_zero] at hp,
      exact not_prime_pow one_lt_two hp } },
  have hxycoprime : is_coprime x y,
  { apply l1_4_coprime zero_lt_one hx hy,
    rwa [int.coe_nat_one, one_mul] },
  set N := a ^ 2 + b ^ 2 with hN,
  set q := x ^ 2 + y ^ 2 with hq,
  have : x ^ 2 * N - a^2 * q = (x * b - a * y) * (x * b + a * y),
  { rw [hN, hq], ring },
  have : q ∣ (x * b - a * y) * (x * b + a * y),
  { rw ←this,
    apply dvd_sub,
    { exact dvd_mul_of_dvd_right hdvd _ },
    { exact dvd_mul_left _ _ } },
  have := hp.div_or_div this,
  obtain ⟨d, hd⟩|⟨d, hd⟩ := this,
  { have xxx : (a + d * y) * y = x * (b - d * x),
    { rw [sub_eq_iff_eq_add, ←sub_eq_iff_eq_add'] at hd,
      rw [add_mul, ←hd, hq],
      ring },
    obtain ⟨c, hc⟩ : x ∣ a + d * y,
    { apply is_coprime.dvd_of_dvd_mul_right hxycoprime,
      rw xxx,
      exact dvd_mul_right x (b - d * x) },
    have ha : a = c * x - d * y,
    { rwa [eq_comm, ←sub_eq_iff_eq_add, eq_comm, mul_comm x] at hc },
    have hb : b = d * x + c * y,
    { rw [←sub_eq_iff_eq_add',  ←mul_right_inj' hx, ←xxx, hc, mul_assoc] },
    use [c, d],

    split,
    { rw [hN, hq, ha, hb], ring },
    { 
      apply is_coprime_of_dvd,
      { rintro ⟨rfl, rfl⟩,
        simp at *,
        subst a,
        subst b,
        simp at *,
        exact habcoprime },
      { intros z znu znezero zdvdc zdvdd,
        have zdvda : z ∣ a,
        { rw ha,
          apply dvd_sub;
          {apply dvd_mul_of_dvd_left, assumption } },
        have zdvdb : z ∣ b,
        { rw hb,
          apply dvd_add;
          {apply dvd_mul_of_dvd_left, assumption } },
        have := habcoprime.is_unit_of_dvd' zdvda zdvdb,
        exact absurd this znu } },
  },
  { have xxx : (-a + d * y) * y = x * (b - d * x),
    { rw [eq_comm, ←sub_eq_iff_eq_add'] at hd,
      rw [add_mul, ←neg_mul_eq_neg_mul, ←hd, hq],
      ring },
    obtain ⟨c, hc⟩ : x ∣ -a + d * y,
    { apply is_coprime.dvd_of_dvd_mul_right hxycoprime,
      rw xxx,
      exact dvd_mul_right x (b - d * x) },
    have ha : a = d * y - c * x,
    { rwa [←sub_eq_neg_add, sub_eq_iff_eq_add', ←sub_eq_iff_eq_add, eq_comm, mul_comm x] at hc },
    have hb : b = d * x + c * y,
    { rw [←sub_eq_iff_eq_add',  ←mul_right_inj' hx, ←xxx, hc, mul_assoc] },
    use [c, d],

    split,
    { rw [hN, hq, ha, hb], ring },
    { 
      apply is_coprime_of_dvd,
      { rintro ⟨rfl, rfl⟩,
        simp at *,
        subst a,
        subst b,
        simp at *,
        exact habcoprime },
      { intros z znu znezero zdvdc zdvdd,
        have zdvda : z ∣ a,
        { rw ha,
          apply dvd_sub;
          {apply dvd_mul_of_dvd_left, assumption } },
        have zdvdb : z ∣ b,
        { rw hb,
          apply dvd_add;
          {apply dvd_mul_of_dvd_left, assumption } },
        have := habcoprime.is_unit_of_dvd' zdvda zdvdb,
        exact absurd this znu } },
  },
end

lemma l1_4''
  {n : ℕ}
  (hn : 0 < n)
  (a b x y : ℤ)
  (habcoprime : is_coprime a b)
  (hdvd : x ^ 2 + n * y ^ 2 ∣ a ^ 2 + n * b ^ 2)
  (hp : prime (x ^ 2 + n * y ^ 2))
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  :
  ∃ c d,
    a ^ 2 + n * b ^ 2 = (x ^ 2 + n * y ^ 2) * (c ^ 2 + n * d ^ 2) ∧
    is_coprime c d
  := 
begin
  have hxycoprime : is_coprime x y := l1_4_coprime hn hx hy hp,
  have hn' := int.coe_nat_pos.mpr hn,
  set N := a ^ 2 + n * b ^ 2 with hN,
  set q := x ^ 2 + n * y ^ 2 with hq,
  obtain ⟨hx' : 1 ≤ x ^ 2, hy' : 1 ≤ y ^ 2⟩ : _ ∧ _,
  { split;
    { rw ←int.nat_abs_pow_two,
      norm_cast,
      rw [nat.succ_le_iff, pos_iff_ne_zero],
      apply pow_ne_zero,
      rwa int.nat_abs_ne_zero,
    } },
  have qbound : (1 + n : ℤ) ≤ q,
  { rw [←mul_one n, hq, int.coe_nat_mul],
    apply add_le_add hx' _,
    rwa mul_le_mul_left hn' },
  have qne3 : q ≠ n,
  { intro H,
    norm_num [H] at qbound, },
  have qnonneg : 0 ≤ q,
  { apply le_of_lt,
    calc (0 : ℤ) < n : hn'
    ... < 1 + n : lt_add_of_pos_left _ zero_lt_one
    ... ≤ q : qbound },
  have : x ^ 2 * N - a^2 * q = n * (x * b - a * y) * (x * b + a * y),
  { rw [hN, hq], ring },
  have : q ∣ n * (x * b - a * y) * (x * b + a * y),
  { rw ←this,
    apply dvd_sub,
    { exact dvd_mul_of_dvd_right hdvd _ },
    { exact dvd_mul_left _ _ } },
  obtain dvd|⟨d, hd⟩ := hp.div_or_div this,
  { obtain dvd|⟨d, hd⟩ := hp.div_or_div dvd,
    { exfalso,
      have := qbound.trans (int.le_of_dvd hn' dvd),
      norm_num at this },
    have xxx : (a + n * d * y) * y = x * (b - d * x),
    { rw [sub_eq_iff_eq_add, ←sub_eq_iff_eq_add'] at hd,
      rw [add_mul, ←hd, hq],
      ring },
    obtain ⟨c, hc⟩ : x ∣ a + n * d * y,
    { apply is_coprime.dvd_of_dvd_mul_right hxycoprime,
      rw xxx,
      exact dvd_mul_right x (b - d * x) },
    have ha : a = c * x - n * d * y,
    { rwa [eq_comm, ←sub_eq_iff_eq_add, eq_comm, mul_comm x] at hc },
    have hb : b = d * x + c * y,
    { rw [←sub_eq_iff_eq_add',  ←mul_right_inj' hx, ←xxx, hc, mul_assoc] },
    use [c, d],

    split,
    { rw [hN, hq, ha, hb], ring },
    { 
      apply is_coprime_of_dvd,
      { rintro ⟨rfl, rfl⟩,
        simp at *,
        subst a,
        subst b,
        simp at *,
        exact habcoprime },
      { intros z znu znezero zdvdc zdvdd,
        have zdvda : z ∣ a,
        { rw ha,
          apply dvd_sub,
          {apply dvd_mul_of_dvd_left, assumption, },
          {apply dvd_mul_of_dvd_left, apply dvd_mul_of_dvd_right, assumption, },
           },
        have zdvdb : z ∣ b,
        { rw hb,
          apply dvd_add;
          {apply dvd_mul_of_dvd_left, assumption } },
        have := habcoprime.is_unit_of_dvd' zdvda zdvdb,
        exact absurd this znu } },
  },
  { have xxx : (-a + n * d * y) * y = x * (b - d * x),
    { rw [eq_comm, ←sub_eq_iff_eq_add'] at hd,
      rw [add_mul, ←neg_mul_eq_neg_mul, ←hd, hq],
      ring },
    obtain ⟨c, hc⟩ : x ∣ -a + n * d * y,
    { apply is_coprime.dvd_of_dvd_mul_right hxycoprime,
      rw xxx,
      exact dvd_mul_right x (b - d * x) },
    have ha : a = n * d * y - c * x,
    { rwa [←sub_eq_neg_add, sub_eq_iff_eq_add', ←sub_eq_iff_eq_add, eq_comm, mul_comm x] at hc },
    have hb : b = d * x + c * y,
    { rw [←sub_eq_iff_eq_add',  ←mul_right_inj' hx, ←xxx, hc, mul_assoc] },
    use [c, d],

    split,
    { rw [hN, hq, ha, hb], ring },
    { 
      apply is_coprime_of_dvd,
      { rintro ⟨rfl, rfl⟩,
        simp at *,
        subst a,
        subst b,
        simp at *,
        exact habcoprime },
      { intros z znu znezero zdvdc zdvdd,
        have zdvda : z ∣ a,
        { rw ha,
          apply dvd_sub,
          {apply dvd_mul_of_dvd_left, apply dvd_mul_of_dvd_right, assumption, },
          {apply dvd_mul_of_dvd_left, assumption, },
           },
        have zdvdb : z ∣ b,
        { rw hb,
          apply dvd_add;
          {apply dvd_mul_of_dvd_left, assumption } },
        have := habcoprime.is_unit_of_dvd' zdvda zdvdb,
        exact absurd this znu } },
  },
end

lemma l1_4'
  (a b x y : ℤ)
  (habcoprime : is_coprime a b)
  (hdvd : x ^ 2 + 3 * y ^ 2 ∣ a ^ 2 + 3 * b ^ 2)
  (hp : prime (x ^ 2 + 3 * y ^ 2))
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  :
  ∃ c d,
    a ^ 2 + 3 * b ^ 2 = (x ^ 2 + 3 * y ^ 2) * (c ^ 2 + 3 * d ^ 2) ∧
    is_coprime c d
  := l1_4'' zero_lt_three _ _ _ _ habcoprime hdvd hp hx hy
/-
begin
  apply l1_4'' zero_lt_three _ _ _ _ habcoprime hdvd hp hx hy,
  have hxycoprime : is_coprime x y,
  { apply l1_4_coprime zero_lt_three hx hy,
    norm_cast,
    exact hp },
  set N := a ^ 2 + 3 * b ^ 2 with hN,
  set q := x ^ 2 + 3 * y ^ 2 with hq,
  obtain ⟨hx' : 1 ≤ x ^ 2, hy' : 1 ≤ y ^ 2⟩ : _ ∧ _,
  { split;
    { rw ←int.nat_abs_pow_two,
      norm_cast,
      rw [nat.succ_le_iff, pos_iff_ne_zero],
      apply pow_ne_zero,
      rwa int.nat_abs_ne_zero,
    } },
  have qbound : 4 ≤ q,
  { calc 4 = 1 + 3 * 1 : by norm_num
    ... ≤ q : add_le_add hx' _,
    rwa mul_le_mul_left zero_lt_three,
    apply_instance },
  have qne3 : q ≠ 3,
  { intro H,
    norm_num [H] at qbound, },
  have qnonneg : 0 ≤ q := zero_lt_four.le.trans qbound,
  have : x ^ 2 * N - a^2 * q = 3 * (x * b - a * y) * (x * b + a * y),
  { rw [hN, hq], ring },
  have : q ∣ 3 * (x * b - a * y) * (x * b + a * y),
  { rw ←this,
    apply dvd_sub,
    { exact dvd_mul_of_dvd_right hdvd _ },
    { exact dvd_mul_left _ _ } },
 -- have q_
  obtain dvd|⟨d, hd⟩ := hp.div_or_div this,
  { obtain ⟨d, hd⟩ : q ∣ x * b - a * y,
    { rw ←int.nat_abs_dvd_abs_iff at ⊢ dvd,
      rw int.nat_abs_mul at dvd,
      apply dvd_mul_cancel_prime dvd,
      { zify,
        rwa [int.nat_abs_of_nonneg qnonneg, int.nat_abs_of_nonneg zero_lt_three.le] },
      { convert nat.prime_three },
      { rwa [nat.prime_iff_prime_int, int.nat_abs_of_nonneg qnonneg] } },
    have xxx : (a + 3 * d * y) * y = x * (b - d * x),
    { rw [sub_eq_iff_eq_add, ←sub_eq_iff_eq_add'] at hd,
      rw [add_mul, ←hd, hq],
      ring },
    obtain ⟨c, hc⟩ : x ∣ a + 3 * d * y,
    { apply is_coprime.dvd_of_dvd_mul_right hxycoprime,
      rw xxx,
      exact dvd_mul_right x (b - d * x) },
    have ha : a = c * x - 3 * d * y,
    { rwa [eq_comm, ←sub_eq_iff_eq_add, eq_comm, mul_comm x] at hc },
    have hb : b = d * x + c * y,
    { rw [←sub_eq_iff_eq_add',  ←mul_right_inj' hx, ←xxx, hc, mul_assoc] },
    use [c, d],

    split,
    { rw [hN, hq, ha, hb], ring },
    { 
      apply is_coprime_of_dvd,
      { rintro ⟨rfl, rfl⟩,
        simp at *,
        subst a,
        subst b,
        simp at *,
        exact habcoprime },
      { intros z znu znezero zdvdc zdvdd,
        have zdvda : z ∣ a,
        { rw ha,
          apply dvd_sub,
          {apply dvd_mul_of_dvd_left, assumption, },
          {apply dvd_mul_of_dvd_left, apply dvd_mul_of_dvd_right, assumption, },
           },
        have zdvdb : z ∣ b,
        { rw hb,
          apply dvd_add;
          {apply dvd_mul_of_dvd_left, assumption } },
        have := habcoprime.is_unit_of_dvd' zdvda zdvdb,
        exact absurd this znu } },
  },
  { have xxx : (-a + 3 * d * y) * y = x * (b - d * x),
    { rw [eq_comm, ←sub_eq_iff_eq_add'] at hd,
      rw [add_mul, ←neg_mul_eq_neg_mul, ←hd, hq],
      ring },
    obtain ⟨c, hc⟩ : x ∣ -a + 3 * d * y,
    { apply is_coprime.dvd_of_dvd_mul_right hxycoprime,
      rw xxx,
      exact dvd_mul_right x (b - d * x) },
    have ha : a = 3 * d * y - c * x,
    { rwa [←sub_eq_neg_add, sub_eq_iff_eq_add', ←sub_eq_iff_eq_add, eq_comm, mul_comm x] at hc },
    have hb : b = d * x + c * y,
    { rw [←sub_eq_iff_eq_add',  ←mul_right_inj' hx, ←xxx, hc, mul_assoc] },
    use [c, d],

    split,
    { rw [hN, hq, ha, hb], ring },
    { 
      apply is_coprime_of_dvd,
      { rintro ⟨rfl, rfl⟩,
        simp at *,
        subst a,
        subst b,
        simp at *,
        exact habcoprime },
      { intros z znu znezero zdvdc zdvdd,
        have zdvda : z ∣ a,
        { rw ha,
          apply dvd_sub,
          {apply dvd_mul_of_dvd_left, apply dvd_mul_of_dvd_right, assumption, },
          {apply dvd_mul_of_dvd_left, assumption, },
           },
        have zdvdb : z ∣ b,
        { rw hb,
          apply dvd_add;
          {apply dvd_mul_of_dvd_left, assumption } },
        have := habcoprime.is_unit_of_dvd' zdvda zdvdb,
        exact absurd this znu } },
  },
end
-/

lemma ineq {p : ℕ} {a b : ℤ}
  (ha : 2 * a.nat_abs < p)
  (hb : 2 * b.nat_abs < p) :
  2 * (a ^ 2 + b ^ 2) < ↑p ^ 2 :=
begin
  rw [←int.nat_abs_pow_two a, ←int.nat_abs_pow_two b],
  zify at ha hb,
  nlinarith [ha, hb],
end

lemma ineq3 {p : ℕ} {a b : ℤ}
  (ha : 2 * a.nat_abs < p)
  (hb : 2 * b.nat_abs < p) :
  a ^ 2 + 3 * b ^ 2 < ↑p ^ 2 :=
begin
  rw [←int.nat_abs_pow_two a, ←int.nat_abs_pow_two b],
  zify at ha hb,
  nlinarith [ha, hb],
end

lemma fermat1_wlog
  (p : ℕ)
  (x y : ℤ)
  (hp : nat.prime p)
  (hpodd : odd p)
  (hdvd : (p : ℤ) ∣ x ^ 2 + y ^ 2)
  (hcoprime : int.gcd x y = 1) :
  ∃ a b : ℤ,
    (p : ℤ) ∣ a ^ 2 + b ^ 2 ∧
    is_coprime a b ∧
    2 * a.nat_abs < p ∧
    2 * b.nat_abs < p ∧
    (a ≠ 0 ∨ b ≠ 0) ∧
    2 * (a ^ 2 + b ^ 2) < p ^ 2 :=
begin
  obtain ⟨a, b, ha, hb, habnezero, hdvd'⟩ : ∃ a b : ℤ,
    2 * a.nat_abs < p ∧
    2 * b.nat_abs < p ∧
    (a ≠ 0 ∨ b ≠ 0) ∧
    (p : ℤ) ∣ a ^ 2 + b ^ 2,
  { obtain ⟨a, a', ha, ha'⟩ := int.factor_div x p hpodd hp.pos,
    obtain ⟨b, b', hb, hb'⟩ := int.factor_div y p hpodd hp.pos,
    refine ⟨a', b', ha', hb', _, _⟩,
    { rw [ne.def, ne.def, ←not_and_distrib],
      rintro ⟨rfl, rfl⟩,
      apply hp.ne_one,
      rw zero_add at ha hb,
      rw [←ha, ←hb, int.gcd_mul_right, int.nat_abs_of_nat, nat.mul_eq_one_iff] at hcoprime,
      exact hcoprime.2 },
    set c := 2 * a' * a + p * a ^ 2 + 2 * b' * b + p * b ^ 2 with hc,
    rw ←dvd_add_left (dvd_mul_right _ c),
    convert hdvd using 1,
    rw [←ha, ←hb, hc, add_pow_two, add_pow_two],
    ring },
  obtain ⟨a, b, ha, hb, habnezero, habcoprime, hdvd'⟩ : ∃ a b : ℤ,
    2 * a.nat_abs < p ∧
    2 * b.nat_abs < p ∧
    (a ≠ 0 ∨ b ≠ 0) ∧
    (is_coprime a b) ∧
    (p : ℤ) ∣ a ^ 2 + b ^ 2,
  {
    set d := int.gcd a b with hd,
    have dnezero : d ≠ 0 := int.gcd_ne_zero_iff.mpr habnezero,
    have dpos := pos_iff_ne_zero.mpr dnezero,
    use [a / d, b / d],
    have hdvda : ↑d ∣ a := int.gcd_dvd_left a b,
    have hdvdb : ↑d ∣ b := int.gcd_dvd_right a b,
    have hcoprime_div : is_coprime (a / d) (b / d) := int.coprime_div_gcd_div_gcd dnezero,
    refine ⟨lt_of_le_of_lt _ ha, lt_of_le_of_lt _ hb, _, hcoprime_div, _⟩,
    { apply nat.mul_le_mul_left,
      rw int.nat_abs_div _ _ hdvda,
      exact nat.div_le_self _ _ },
    { apply nat.mul_le_mul_left,
      rw int.nat_abs_div _ _ hdvdb,
      exact nat.div_le_self _ _ },
    { apply or.imp _ _ habnezero;
      { intro hx,
        apply int.div_ne_zero_of_dvd hx _ ‹_›,
        norm_cast,
        assumption },

    },
    have : ¬(p ∣ d),
    { intro H,
      obtain ⟨A, HA⟩ := hdvda,
      rw HA at *,
      obtain ⟨B, HB⟩ := hdvdb,
      rw HB at *,
      rw [int.nat_abs_mul, int.nat_abs_of_nat] at ha hb,
      cases habnezero,
      { have := nat.le_of_dvd dpos H,
        have := lt_of_lt_of_le ha this,
        rw ←int.nat_abs_ne_zero at habnezero,
        rw [int.nat_abs_mul, int.nat_abs_of_nat] at habnezero,
        rw [mul_comm d, ←mul_assoc] at this,
        conv_rhs at this { rw ←one_mul d },
        have := lt_of_mul_lt_mul_right' this,
        obtain ⟨_, HH⟩:= mul_ne_zero_iff.mp habnezero,
        apply HH,
        linarith, },
      { have := nat.le_of_dvd dpos H,
        have := lt_of_lt_of_le hb this,
        rw ←int.nat_abs_ne_zero at habnezero,
        rw [int.nat_abs_mul, int.nat_abs_of_nat] at habnezero,
        rw [mul_comm d, ←mul_assoc] at this,
        conv_rhs at this { rw ←one_mul d },
        have := lt_of_mul_lt_mul_right' this,
        obtain ⟨_, HH⟩:= mul_ne_zero_iff.mp habnezero,
        apply HH,
        linarith } },
    rw [int.div_pow hdvda, int.div_pow hdvdb],
    rw ←int.add_div_of_dvd_left (pow_dvd_pow_of_dvd hdvda _),
    obtain ⟨A, HA⟩ : (d ^ 2 : ℤ) ∣ a ^ 2 + b ^ 2,
    { apply dvd_add; apply pow_dvd_pow_of_dvd; assumption },
    rw [HA],
    rw int.mul_div_cancel_left,
    apply int.of_nat_dvd_of_dvd_nat_abs,
    rw HA at hdvd',
    have := int.dvd_nat_abs_of_of_nat_dvd hdvd',
    rw [int.nat_abs_mul, int.nat_abs_pow, int.nat_abs_of_nat] at this,
    have := (nat.prime.dvd_mul hp).mp this,
    apply this.resolve_left,
    have := mt hp.dvd_of_dvd_pow,
    apply this,
    assumption,

    apply pow_ne_zero,
    rw int.coe_nat_ne_zero,
    exact dnezero,
  },
  exact ⟨a, b, hdvd', habcoprime, ha, hb, habnezero, ineq ha hb⟩,
end

lemma fermat1_descent
  (p : ℕ)
  (N : ℤ)
  (hp : nat.prime p)
  (hpodd : odd p)
  (hdvd : (p : ℤ) ∣ N)
  (H : ¬(∃ a b : ℤ, (p : ℤ) ∣ a ^ 2 + b ^ 2)) :
  ¬(∃ a b : ℤ, N = a ^ 2 + b ^ 2) :=
begin
  contrapose! H,
  obtain ⟨a, b, h⟩ := H,
  use [a, b],
  rwa ←h,
end

--theorem coprime_primes {p q : ℤ} (pp : prime p) (pq : prime q) : is_coprime p q ↔ p ≠ q :=
--by { rw coprime_iff_not_dvd }
--pp.coprime_iff_not_dvd.trans $ not_congr $ dvd_prime_two_le pq pp.two_le

lemma fermat1_two_pow
  (k : ℕ) :
  ∃ X Y : ℤ, 2 ^ k = X ^ 2 + Y ^ 2 :=
begin
  obtain ⟨m, rfl|rfl⟩ := nat.even_or_odd' k,
  { use [0, 2 ^ m], rw [mul_comm, pow_mul], ring },
  { use [2 ^ m, 2 ^ m], rw [←two_mul, pow_add, mul_comm 2 m, pow_mul], ring }
end

lemma fermat1_two_pow'
  (p k : ℕ)
  (x y : ℤ)
  (hp : nat.prime p)
  (hpodd : odd p)
  (h : x ^ 2 + y ^ 2 = ↑p * 2 ^ k)
  (hcoprime : is_coprime x y) :
  ∃ X Y : ℤ, (p : ℤ) = X ^ 2 + Y ^ 2 :=
begin
  induction k with k ih generalizing x y,
  { rw [pow_zero, mul_one] at h,
    exact ⟨x, y, h.symm⟩ },
  { have h2 : (1 ^ 2 + 1 ^ 2 : ℤ) = 2,
    { norm_num },
    rw nat.succ_eq_add_one at h,
    have hdvd2 : (1 ^ 2 + 1 ^ 2) ∣ x ^ 2 + y ^ 2,
    { rw [h2, h, pow_succ', ←mul_assoc],
      apply dvd_mul_left },
    have hprime_two : prime (1 ^ 2 + 1 ^ 2 : ℤ),
    { norm_cast, rw ←nat.prime_iff_prime_int, convert nat.prime_two },
    obtain ⟨c, d, hcd, hcdcoprime⟩ := l1_4 x y 1 1 hcoprime hdvd2 hprime_two,
    refine ih c d _ hcdcoprime,
    rw [h, h2] at hcd,
    rw [←mul_right_inj' (@two_ne_zero ℤ _ _), ←hcd, pow_succ],
    ring },
end

lemma fermat1''
  (p : ℕ)
  (x y : ℤ)
  (hp : nat.prime p)
  (hpodd : odd p)
  (hdvd : (p : ℤ) ∣ x ^ 2 + y ^ 2)
  (hcoprime : int.gcd x y = 1) :
  ∃ X Y : ℤ, (p : ℤ) = X ^ 2 + Y ^ 2 :=
begin
  induction p using nat.strong_induction_on with p ih generalizing x y,
  dsimp at ih,
  have := fermat1_wlog p x y hp hpodd hdvd hcoprime,
  obtain ⟨a, b, hdvd', habcoprime, ha, hb, habnezero, this⟩ := this,
  have bound := this,
  obtain ⟨A, hA⟩ := hdvd',
  rw [hA, pow_two, mul_comm (p : ℤ), ←mul_assoc] at this,
  replace this := lt_of_mul_lt_mul_right this (int.coe_zero_le p),
  have nonneg_A : 0 ≤ A,
  { apply nonneg_of_mul_nonneg_left,
    { rw ←hA,
      exact add_nonneg (pow_two_nonneg a) (pow_two_nonneg b) },
    { norm_cast, exact hp.pos } },
  lift A to ℕ using nonneg_A,
  induction A using nat.strong_induction_on with A IH2 generalizing a b,
  dsimp at IH2,
  change ∀ N' : ℕ, _ at IH2,

  have asq_bsq_ne_zero : a ^ 2 + b ^ 2 ≠ 0,
  { intro H,
    rw [add_eq_zero_iff_eq_zero_of_nonneg (pow_two_nonneg a) (pow_two_nonneg b)] at H,
    obtain rfl := (pow_eq_zero_iff zero_lt_two).mp H.left,
    obtain rfl := (pow_eq_zero_iff zero_lt_two).mp H.right,
    simp only [eq_self_iff_true, not_true, ne.def, or_self] at habnezero,
    assumption },
  /-
  have,
  calc A
      ≤ 2 * A : sorry
  ... < p : lt_of_mul_lt_mul_right this (int.coe_zero_le p),
  -/

  /-
  { norm_num at hA, contradiction },
  { cases A',
    { simp only [mul_one, int.coe_nat_zero, int.coe_nat_succ, zero_add] at hA,
      exact ⟨_, _, hA.symm⟩ },

    have : 2 ≤ A'.succ.succ, { norm_num [nat.succ_eq_add_one, add_assoc] }, 
    obtain ⟨q, hqprime, hqdvd⟩ := nat.exists_prime_and_dvd this,

    sorry,
  },

  -/
  by_cases hA' : A < 2,
  { have : 0 < A,
    { rw pos_iff_ne_zero,
      rintro rfl,
      rw [int.coe_nat_zero, mul_zero] at hA,
      contradiction },
    obtain rfl : A = 1, linarith,
    rw [int.coe_nat_one, mul_one] at hA,
    exact ⟨a, b, hA.symm⟩ },
  { push_neg at hA',
    obtain ⟨k, hk⟩|⟨q, hqprime, hqdvd, hqodd⟩ := exists_odd_prime_and_dvd_or_two_pow hA',
    { apply fermat1_two_pow' p k _ _ hp hpodd _ habcoprime,
      rw [hA, hk],
      norm_num },
    have hpq : q < p,
    { calc q ≤ A : nat.le_of_dvd (zero_lt_two.trans_le hA') hqdvd
      ... ≤ 2 * A : nat.le_mul_of_pos_left zero_lt_two
      ... < p : by { norm_cast at this, exact this }},
    obtain ⟨C, D, HCD⟩ := ih q hpq hqprime hqodd a b _ _,
    have l14_1 : C ^ 2 + D ^ 2 ∣ a ^ 2 + b ^ 2,
    { rw [←HCD, hA],
      apply dvd_mul_of_dvd_right,
      rwa int.coe_nat_dvd },
    have l14_2 : prime (C ^ 2 + D ^ 2),
    { rwa [←HCD, ←nat.prime_iff_prime_int] },
    obtain ⟨E, F, HEF, HEFcoprime⟩ := l1_4 a b C D habcoprime l14_1 l14_2,
    have hqdvd' : (q : ℤ) ∣ a ^ 2 + b ^ 2,
    { rw ←int.coe_nat_dvd at hqdvd,
      apply dvd_trans hqdvd,
      rw hA,
      apply dvd_mul_left },
    obtain ⟨B, hB⟩ := hqdvd,
    rw hB at hA,
    have B_lt_A : B < A,
    { rw hB,
      have : 0 < B,
      { rw pos_iff_ne_zero,
        rintro rfl,
        norm_num [hB] at hA' },
      rw lt_mul_iff_one_lt_left this,
      exact hqprime.one_lt },
    have two_B_lt_p : (2 * B : ℤ) < p,
    { norm_cast,
      calc 2 * B < 2 * A : by { rwa mul_lt_mul_left zero_lt_two, apply_instance, /-XXX-/ }
      ... < p : by { norm_cast at this, exact this } },
    have : (p * B : ℤ) = E ^ 2 + F ^ 2,
    { have : (q : ℤ) ≠ 0 := int.coe_nat_ne_zero.mpr hqprime.ne_zero,
      rw [←mul_right_inj' this, HCD, ←HEF, hA, ←HCD],
      norm_cast,
      ring },


    obtain ⟨E_bound, F_bound⟩ : (2 * E.nat_abs < p) ∧ (2 * F.nat_abs < p),
    { have EF_bound,
      calc 2 * (E ^ 2 + F ^ 2)
          = 2 * (p * B) : by rw this
      ... ≤ q * (p * B) : by {
        apply mul_le_mul_of_nonneg_right,
        { norm_cast, apply hqprime.two_le, },
        {rw [←int.coe_nat_mul], apply int.coe_nat_nonneg}, 
      }
      ... = a ^ 2 + b ^ 2 : by {rw [hA], norm_cast, ring,},

      split,
      { apply lt_of_pow_lt_pow 2,
        { apply zero_le,},
        zify,
        calc _
            = 2 * (2 * E ^ 2) : by rw [mul_pow, int.nat_abs_pow_two, pow_two, mul_assoc]
        ... ≤ 2 * (a ^ 2 + b ^ 2) : mul_le_mul_of_nonneg_left _ zero_le_two
        ... < p ^ 2 : bound,
        
        calc 2 * E ^ 2
            ≤ 2 * (E ^ 2 + F ^ 2) : by {
                  rw mul_add,
                  apply le_add_of_nonneg_right,
                  apply mul_nonneg,
                  apply zero_le_two,
                  apply (pow_two_nonneg _), }
        ... ≤ a ^ 2 + b ^ 2 : EF_bound },
      { apply lt_of_pow_lt_pow 2,
        { apply zero_le,},
        zify,
        calc _
            = 2 * (2 * F ^ 2) : by rw [mul_pow, int.nat_abs_pow_two, pow_two, mul_assoc]
        ... ≤ 2 * (a ^ 2 + b ^ 2) : mul_le_mul_of_nonneg_left _ zero_le_two
        ... < p ^ 2 : bound,
        
        calc 2 * F ^ 2
          ≤ 2 * (E ^ 2 + F ^ 2) : by {
                rw mul_add,
                apply le_add_of_nonneg_left,
                apply mul_nonneg,
                apply zero_le_two,
                apply (pow_two_nonneg _), }
        ... ≤ a ^ 2 + b ^ 2 : EF_bound },
    },

    refine IH2 _ B_lt_A two_B_lt_p _ _ HEFcoprime E_bound F_bound _ _ this.symm,
    { rw ←not_and_distrib,
      rintro ⟨rfl, rfl⟩,
      simp only [zero_pow zero_lt_two, add_zero, mul_zero] at HEF,
      contradiction, },
    { apply ineq E_bound F_bound },
/-




    obtain ⟨B', hB'⟩ := hqdvd',
    lift B' to ℕ using (sorry : 0 ≤ B'),
    have : p ∣ B',
    {
      have := hpq.ne.symm,
      rw ←nat.coprime_primes hp hqprime at this,
      apply nat.coprime.dvd_of_dvd_mul_left this,
      rw ←int.coe_nat_dvd,
      rw int.coe_nat_mul,
      rw [←hB', hA],
      apply dvd_mul_right },  
    obtain ⟨G, H, HGH, HGHcoprime⟩ := l_1_4 a b C D habcoprime l14_1 l14_2,
    rw [hB', ←HCD, mul_right_inj' _] at HGH,
-/


/-
    induction A with A' IH2,
    { norm_num at hA' },
    { cases A',
      { norm_num at hA' },
      
      sorry },

    induction B' with B'' IH2,
    { simp only [int.coe_nat_zero, mul_zero] at hB', contradiction },
    { cases B'',
      simp only [mul_one, int.coe_nat_zero, int.coe_nat_succ, zero_add] at hB',
      sorry },
-/
/-
    rw [hA, ←HCD, hB, int.coe_nat_mul, mul_comm, mul_assoc, mul_right_inj' _] at HEF,
    sorry,
    { norm_cast,
      apply nat.prime.ne_zero hqprime, },
-/
    { rw ←int.coe_nat_dvd at hqdvd,
      apply dvd_trans hqdvd,
      rw hA,
      apply dvd_mul_left },
    { rwa int.gcd_eq_one_iff_coprime },
  },
end
/-
lemma fermat1'
  (p : ℕ)
  (x y : ℤ)
  (hp : nat.prime p)
  (hpodd : odd p)
  (hdvd : (p : ℤ) ∣ x ^ 2 + y ^ 2)
  (hcoprime : int.gcd x y = 1) :
  ∃ X Y : ℤ, (p : ℤ) = X ^ 2 + Y ^ 2 :=
begin
  induction p using nat.strong_induction_on with p ih generalizing x y,
  dsimp at ih,
  have := fermat1_wlog p x y hp hpodd hdvd hcoprime,
  obtain ⟨a, b, hdvd', habcoprime, ha, hb, habnezero, this⟩ := this,
  have asq_bsq_ne_zero : a ^ 2 + b ^ 2 ≠ 0,
  { intro H,
    rw [add_eq_zero_iff_eq_zero_of_nonneg (pow_two_nonneg a) (pow_two_nonneg b)] at H,
    obtain rfl := (pow_eq_zero_iff zero_lt_two).mp H.left,
    obtain rfl := (pow_eq_zero_iff zero_lt_two).mp H.right,
    simp only [eq_self_iff_true, not_true, ne.def, or_self] at habnezero,
    assumption },
  obtain ⟨A, hA⟩ := hdvd',
  rw [hA, pow_two, mul_comm (p : ℤ), ←mul_assoc] at this,
  have nonneg_A : 0 ≤ A, sorry,
  have,
  calc A
      ≤ 2 * A : sorry
  ... < p : lt_of_mul_lt_mul_right this (int.coe_zero_le p),

  by_cases hA' : A < 2,
  { lift A to ℕ using nonneg_A,
    have : 0 < A,
    { rw pos_iff_ne_zero,
      rintro rfl,
      rw [int.coe_nat_zero, mul_zero] at hA,
      contradiction },
    norm_cast at hA',
    obtain rfl : A = 1, linarith,
    rw [int.coe_nat_one, mul_one] at hA,
    exact ⟨a, b, hA.symm⟩ },
  { push_neg at hA',
    lift A to ℕ using nonneg_A,
    norm_cast at hA',
    obtain ⟨q, hqprime, hqdvd⟩ := nat.exists_prime_and_dvd hA',
    cases nat.prime.eq_two_or_odd hqprime with heqtwo hqodd,
    { sorry },
    rw ←nat.odd_iff at hqodd,
    have hpq : q < p := sorry,
    obtain ⟨C, D, HCD⟩ := ih q hpq hqprime hqodd a b _ _,
    have l14_1 : C ^ 2 + D ^ 2 ∣ a ^ 2 + b ^ 2,
    { rw [←HCD, hA],
      apply dvd_mul_of_dvd_right,
      rwa int.coe_nat_dvd },
    have l14_2 : prime (C ^ 2 + D ^ 2),
    { rwa [←HCD, ←nat.prime_iff_prime_int] },
    obtain ⟨E, F, HEF, HEFcoprime⟩ := l_1_4 a b C D habcoprime l14_1 l14_2,
    have hqdvd' : (q : ℤ) ∣ a ^ 2 + b ^ 2,
    { rw ←int.coe_nat_dvd at hqdvd,
      apply dvd_trans hqdvd,
      rw hA,
      apply dvd_mul_left },
    --obtain ⟨B, hB⟩ := hqdvd,
    obtain ⟨B', hB'⟩ := hqdvd',
    lift B' to ℕ using (sorry : 0 ≤ B'),
    have : p ∣ B',
    {
      have := hpq.ne.symm,
      rw ←nat.coprime_primes hp hqprime at this,
      apply nat.coprime.dvd_of_dvd_mul_left this,
      rw ←int.coe_nat_dvd,
      rw int.coe_nat_mul,
      rw [←hB', hA],
      apply dvd_mul_right },  
    obtain ⟨G, H, HGH, HGHcoprime⟩ := l_1_4 a b C D habcoprime l14_1 l14_2,
    rw [hB', ←HCD, mul_right_inj' _] at HGH,

    induction A with A' IH2,
    { norm_num at hA' },
    { cases A',
      { norm_num at hA' },
      
      sorry },

    induction B' with B'' IH2,
    { simp only [int.coe_nat_zero, mul_zero] at hB', contradiction },
    { cases B'',
      simp only [mul_one, int.coe_nat_zero, int.coe_nat_succ, zero_add] at hB',
      sorry },

    rw [hA, ←HCD, hB, int.coe_nat_mul, mul_comm, mul_assoc, mul_right_inj' _] at HEF,
    sorry,
    { norm_cast,
      apply nat.prime.ne_zero hqprime, },
    { rw ←int.coe_nat_dvd at hqdvd,
      apply dvd_trans hqdvd,
      rw hA,
      apply dvd_mul_left },
    { rwa int.gcd_eq_one_iff_coprime },
  },
end

lemma fermat1
  (p : ℕ)
  (x y : ℤ)
  (hp : nat.prime p)
  (hpodd : odd p)
  (hdvd : (p : ℤ) ∣ x ^ 2 + y ^ 2)
  (hcoprime : int.gcd x y = 1) :
  (p : ℤ) = x ^ 2 + y ^ 2 :=
begin
  induction p using nat.strong_induction_on with p ih generalizing x y,
  dsimp at ih,
  obtain ⟨a, b, ha, hb, habnezero, hdvd'⟩ : ∃ a b : ℤ,
    2 * a.nat_abs < p ∧
    2 * b.nat_abs < p ∧
    (a ≠ 0 ∨ b ≠ 0) ∧
    (p : ℤ) ∣ a ^ 2 + b ^ 2,
  { obtain ⟨a, a', ha, ha'⟩ := int.factor_div x p hpodd hp.pos,
    obtain ⟨b, b', hb, hb'⟩ := int.factor_div y p hpodd hp.pos,
    refine ⟨a', b', ha', hb', _, _⟩,
    { rw [ne.def, ne.def, ←not_and_distrib],
      rintro ⟨rfl, rfl⟩,
      apply hp.ne_one,
      rw zero_add at ha hb,
      rw [←ha, ←hb, int.gcd_mul_right, int.nat_abs_of_nat, nat.mul_eq_one_iff] at hcoprime,
      exact hcoprime.2 },
    set c := 2 * a' * a + p * a ^ 2 + 2 * b' * b + p * b ^ 2 with hc,
    rw ←dvd_add_left (dvd_mul_right _ c),
    convert hdvd using 1,
    rw [←ha, ←hb, hc, add_pow_two, add_pow_two],
    ring },
  obtain ⟨a, b, ha, hb, habnezero, hdvd'⟩ : ∃ a b : ℤ,
    2 * a.nat_abs < p ∧
    2 * b.nat_abs < p ∧
    (is_coprime a b) ∧
    (p : ℤ) ∣ a ^ 2 + b ^ 2,
  {
    set d := int.gcd a b with hd,
    have dnezero : d ≠ 0 := int.gcd_ne_zero_iff.mpr habnezero,
    have dpos := pos_iff_ne_zero.mpr dnezero,
    use [a / d, b / d],
    have hdvda : ↑d ∣ a := int.gcd_dvd_left a b,
    have hdvdb : ↑d ∣ b := int.gcd_dvd_right a b,
    have hcoprime_div : is_coprime (a / d) (b / d) := int.coprime_div_gcd_div_gcd dnezero,
    refine ⟨lt_of_le_of_lt _ ha, lt_of_le_of_lt _ hb, hcoprime_div, _⟩,
    { apply nat.mul_le_mul_left,
      rw int.nat_abs_div _ _ hdvda,
      exact nat.div_le_self _ _ },
    { apply nat.mul_le_mul_left,
      rw int.nat_abs_div _ _ hdvdb,
      exact nat.div_le_self _ _ },
    have : ¬(p ∣ d),
    { intro H,
      obtain ⟨A, HA⟩ := hdvda,
      rw HA at *,
      obtain ⟨B, HB⟩ := hdvdb,
      rw HB at *,
      rw [int.nat_abs_mul, int.nat_abs_of_nat] at ha hb,
      cases habnezero,
      { have := nat.le_of_dvd dpos H,
        have := lt_of_lt_of_le ha this,
        rw ←int.nat_abs_ne_zero at habnezero,
        rw [int.nat_abs_mul, int.nat_abs_of_nat] at habnezero,
        rw [mul_comm d, ←mul_assoc] at this,
        conv_rhs at this { rw ←one_mul d },
        have := lt_of_mul_lt_mul_right' this,
        obtain ⟨_, HH⟩:= mul_ne_zero_iff.mp habnezero,
        apply HH,
        linarith, },
      { have := nat.le_of_dvd dpos H,
        have := lt_of_lt_of_le hb this,
        rw ←int.nat_abs_ne_zero at habnezero,
        rw [int.nat_abs_mul, int.nat_abs_of_nat] at habnezero,
        rw [mul_comm d, ←mul_assoc] at this,
        conv_rhs at this { rw ←one_mul d },
        have := lt_of_mul_lt_mul_right' this,
        obtain ⟨_, HH⟩:= mul_ne_zero_iff.mp habnezero,
        apply HH,
        linarith } },
    rw [int.div_pow hdvda, int.div_pow hdvdb],
    rw ←int.add_div_of_dvd_left (pow_dvd_pow_of_dvd hdvda _),
    obtain ⟨A, HA⟩ : (d ^ 2 : ℤ) ∣ a ^ 2 + b ^ 2,
    { apply dvd_add; apply pow_dvd_pow_of_dvd; assumption },
    rw [HA],
    rw int.mul_div_cancel_left,
    apply int.of_nat_dvd_of_dvd_nat_abs,
    rw HA at hdvd',
    have := int.dvd_nat_abs_of_of_nat_dvd hdvd',
    rw [int.nat_abs_mul, int.nat_abs_pow, int.nat_abs_of_nat] at this,
    have := (nat.prime.dvd_mul hp).mp this,
    apply this.resolve_left,
    have := mt hp.dvd_of_dvd_pow,
    apply this,
    assumption,

    apply pow_ne_zero,
    rw int.coe_nat_ne_zero,
    exact dnezero,
  },
  have : 2 * (a ^ 2 + b ^ 2) < p ^ 2,
  { rw [←int.nat_abs_pow_two a, ←int.nat_abs_pow_two b],
    zify at ha hb,
    nlinarith [ha, hb] },
  obtain ⟨q, hq⟩ := hdvd',
  rw [hq, pow_two, mul_comm (p : ℤ), ←mul_assoc] at this,
  have nonneg_q : 0 ≤ q, sorry,
  have,
  calc q
      ≤ 2 * q : sorry
  ... < p : lt_of_mul_lt_mul_right this (int.coe_zero_le p),
  have := nat.exists_prime_and_dvd,
  have := lt_of_mul_lt_mul_right this (int.coe_zero_le p),
  sorry,
end
-/

lemma fermat3_wlog
  (p : ℕ)
  (x y : ℤ)
  (hp : nat.prime p)
  (hpodd : odd p)
  (hdvd : (p : ℤ) ∣ x ^ 2 + 3 * y ^ 2)
  (hcoprime : int.gcd x y = 1) :
  ∃ a b : ℤ,
    (p : ℤ) ∣ a ^ 2 + 3 * b ^ 2 ∧
    is_coprime a b ∧
    2 * a.nat_abs < p ∧
    2 * b.nat_abs < p ∧
    (a ≠ 0 ∨ b ≠ 0) ∧
    a ^ 2 + 3 * b ^ 2 < p ^ 2 :=
begin
  obtain ⟨a, b, ha, hb, habnezero, hdvd'⟩ : ∃ a b : ℤ,
    2 * a.nat_abs < p ∧
    2 * b.nat_abs < p ∧
    (a ≠ 0 ∨ b ≠ 0) ∧
    (p : ℤ) ∣ a ^ 2 + 3 * b ^ 2,
  { obtain ⟨a, a', ha, ha'⟩ := int.factor_div x p hpodd hp.pos,
    obtain ⟨b, b', hb, hb'⟩ := int.factor_div y p hpodd hp.pos,
    refine ⟨a', b', ha', hb', _, _⟩,
    { rw [ne.def, ne.def, ←not_and_distrib],
      rintro ⟨rfl, rfl⟩,
      apply hp.ne_one,
      rw zero_add at ha hb,
      rw [←ha, ←hb, int.gcd_mul_right, int.nat_abs_of_nat, nat.mul_eq_one_iff] at hcoprime,
      exact hcoprime.2 },
    set c := 2 * a' * a + p * a ^ 2 + 6 * b' * b + 3 * p * b ^ 2 with hc,
    rw ←dvd_add_left (dvd_mul_right _ c),
    convert hdvd using 1,
    rw [←ha, ←hb, hc, add_pow_two, add_pow_two],
    ring },
  obtain ⟨a, b, ha, hb, habnezero, habcoprime, hdvd'⟩ : ∃ a b : ℤ,
    2 * a.nat_abs < p ∧
    2 * b.nat_abs < p ∧
    (a ≠ 0 ∨ b ≠ 0) ∧
    (is_coprime a b) ∧
    (p : ℤ) ∣ a ^ 2 + 3 * b ^ 2,
  {
    set d := int.gcd a b with hd,
    have dnezero : d ≠ 0 := int.gcd_ne_zero_iff.mpr habnezero,
    have dpos := pos_iff_ne_zero.mpr dnezero,
    use [a / d, b / d],
    have hdvda : ↑d ∣ a := int.gcd_dvd_left a b,
    have hdvdb : ↑d ∣ b := int.gcd_dvd_right a b,
    have hcoprime_div : is_coprime (a / d) (b / d) := int.coprime_div_gcd_div_gcd dnezero,
    refine ⟨lt_of_le_of_lt _ ha, lt_of_le_of_lt _ hb, _, hcoprime_div, _⟩,
    { apply nat.mul_le_mul_left,
      rw int.nat_abs_div _ _ hdvda,
      exact nat.div_le_self _ _ },
    { apply nat.mul_le_mul_left,
      rw int.nat_abs_div _ _ hdvdb,
      exact nat.div_le_self _ _ },
    { apply or.imp _ _ habnezero;
      { intro hx,
        apply int.div_ne_zero_of_dvd hx _ ‹_›,
        norm_cast,
        assumption },

    },
    have : ¬(p ∣ d),
    { intro H,
      obtain ⟨A, HA⟩ := hdvda,
      rw HA at *,
      obtain ⟨B, HB⟩ := hdvdb,
      rw HB at *,
      rw [int.nat_abs_mul, int.nat_abs_of_nat] at ha hb,
      cases habnezero,
      { have := nat.le_of_dvd dpos H,
        have := lt_of_lt_of_le ha this,
        rw ←int.nat_abs_ne_zero at habnezero,
        rw [int.nat_abs_mul, int.nat_abs_of_nat] at habnezero,
        rw [mul_comm d, ←mul_assoc] at this,
        conv_rhs at this { rw ←one_mul d },
        have := lt_of_mul_lt_mul_right' this,
        obtain ⟨_, HH⟩:= mul_ne_zero_iff.mp habnezero,
        apply HH,
        linarith, },
      { have := nat.le_of_dvd dpos H,
        have := lt_of_lt_of_le hb this,
        rw ←int.nat_abs_ne_zero at habnezero,
        rw [int.nat_abs_mul, int.nat_abs_of_nat] at habnezero,
        rw [mul_comm d, ←mul_assoc] at this,
        conv_rhs at this { rw ←one_mul d },
        have := lt_of_mul_lt_mul_right' this,
        obtain ⟨_, HH⟩:= mul_ne_zero_iff.mp habnezero,
        apply HH,
        linarith } },
    rw [int.div_pow hdvda, int.div_pow hdvdb],
    rw ←int.mul_div_assoc _ (pow_dvd_pow_of_dvd hdvdb _),
    rw ←int.add_div_of_dvd_left (pow_dvd_pow_of_dvd hdvda _),
    obtain ⟨A, HA⟩ : (d ^ 2 : ℤ) ∣ a ^ 2 + 3 * b ^ 2,
    { apply dvd_add,
      { apply pow_dvd_pow_of_dvd, assumption },
      { apply dvd_mul_of_dvd_right, apply pow_dvd_pow_of_dvd, assumption },

      },
    rw [HA],
    rw int.mul_div_cancel_left,
    apply int.of_nat_dvd_of_dvd_nat_abs,
    rw HA at hdvd',
    have := int.dvd_nat_abs_of_of_nat_dvd hdvd',
    rw [int.nat_abs_mul, int.nat_abs_pow, int.nat_abs_of_nat] at this,
    have := (nat.prime.dvd_mul hp).mp this,
    apply this.resolve_left,
    have := mt hp.dvd_of_dvd_pow,
    apply this,
    assumption,

    apply pow_ne_zero,
    rw int.coe_nat_ne_zero,
    exact dnezero,
  },
  exact ⟨a, b, hdvd', habcoprime, ha, hb, habnezero, ineq3 ha hb⟩,
end

lemma le_3'
  (y : ℤ) :
  0 ≤ 3 * y ^ 2 :=
begin
  apply mul_nonneg zero_lt_three.le,
  exact (pow_two_nonneg _),
  apply_instance,
end


lemma le_3
  (x y : ℤ) :
  0 ≤ x ^ 2 + 3 * y ^ 2 :=
add_nonneg (pow_two_nonneg _) (le_3' _)

/-
lemma fermat3_two_pow'
  (p k : ℕ)
  (x y : ℤ)
  (hk : 1 < k)
  (hp : nat.prime p)
  (hpodd : odd p)
  (h : x ^ 2 + 3 * y ^ 2 = ↑p * 2 ^ k)
  (hcoprime : is_coprime x y) :
  ∃ X Y : ℤ, (p : ℤ) = X ^ 2 + 3 * Y ^ 2 :=
begin
  induction k with k ih generalizing x y,
  { rw [pow_zero, mul_one] at h,
    exact ⟨x, y, h.symm⟩ },
  { have h2 : (1 ^ 2 + 3 * 1 ^ 2 : ℤ) = 4,
    { norm_num },
    rw nat.succ_eq_add_one at h,

    cases k,
    { exact (lt_irrefl _ hk).elim, },
    rw nat.succ_eq_add_one at h,

    have hdvd2 : (1 ^ 2 + 3 * 1 ^ 2) ∣ x ^ 2 + 3 * y ^ 2,
    { rw [h2, h],
      apply dvd_mul_of_dvd_right,
      rw [pow_succ', pow_succ', mul_assoc],
      apply dvd_mul_of_dvd_right,
      apply dvd_refl },
    have hprime_two : prime (1 ^ 2 + 1 ^ 2 : ℤ),
    { norm_cast, rw ←nat.prime_iff_prime_int, convert nat.prime_two },
    obtain ⟨c, d, hcd, hcdcoprime⟩ := l1_4' x y 1 1 hcoprime hdvd2 hprime_two,
    refine ih c d _ hcdcoprime,
    rw [h, h2] at hcd,
    rw [←mul_right_inj' (@two_ne_zero ℤ _ _), ←hcd, pow_succ],
    ring },
end

lemma fermat3
  (p : ℕ)
  (x y : ℤ)
  (hp : nat.prime p)
  (hpodd : odd p)
  (hdvd : (p : ℤ) ∣ x ^ 2 + 3 * y ^ 2)
  (hcoprime : int.gcd x y = 1) :
  ∃ X Y : ℤ, (p : ℤ) = X ^ 2 + 3 * Y ^ 2 :=
begin
  induction p using nat.strong_induction_on with p ih generalizing x y,
  dsimp at ih,
  have := fermat3_wlog p x y hp hpodd hdvd hcoprime,
  obtain ⟨a, b, hdvd', habcoprime, ha, hb, habnezero, this⟩ := this,
  have bound := this,
  obtain ⟨A, hA⟩ := hdvd',
  rw [hA, pow_two] at this,
  replace this := lt_of_mul_lt_mul_left this (int.coe_zero_le p),
  have nonneg_A : 0 ≤ A,
  { apply nonneg_of_mul_nonneg_left,
    { rw ←hA, apply le_3 },
    { norm_cast, exact hp.pos } },
  lift A to ℕ using nonneg_A,
  induction A using nat.strong_induction_on with A IH2 generalizing a b,
  dsimp at IH2,
  change ∀ N' : ℕ, _ at IH2,

  have asq_bsq_ne_zero : a ^ 2 + 3 * b ^ 2 ≠ 0,
  { intro H,
    rw [add_eq_zero_iff_eq_zero_of_nonneg (pow_two_nonneg a) (le_3' b)] at H,
    obtain rfl := (pow_eq_zero_iff zero_lt_two).mp H.left,
    obtain rfl := (pow_eq_zero_iff zero_lt_two).mp ((mul_eq_zero.mp H.right).resolve_left three_ne_zero),
    simp only [eq_self_iff_true, not_true, ne.def, or_self] at habnezero,
    assumption },

  by_cases hA' : A < 2,
  { have : 0 < A,
    { rw pos_iff_ne_zero,
      rintro rfl,
      rw [int.coe_nat_zero, mul_zero] at hA,
      contradiction },
    obtain rfl : A = 1, linarith,
    rw [int.coe_nat_one, mul_one] at hA,
    exact ⟨a, b, hA.symm⟩ },
  { push_neg at hA',
    obtain ⟨k, hk⟩|⟨q, hqprime, hqdvd, hqodd⟩ := exists_odd_prime_and_dvd_or_two_pow hA',
    { have : 0 < k,
      { rw pos_iff_ne_zero,
        rintro rfl,
        rw [hk, pow_zero] at hA',
        norm_num at hA' },
      apply fermat1_two_pow' p k _ _ this hp hpodd _ habcoprime,
      rw [hA, hk],
      norm_num },
    have hpq : q < p,
    { calc q ≤ A : nat.le_of_dvd (zero_lt_two.trans_le hA') hqdvd
      ... ≤ 2 * A : nat.le_mul_of_pos_left zero_lt_two
      ... < p : by { norm_cast at this, exact this }},
    obtain ⟨C, D, HCD⟩ := ih q hpq hqprime hqodd a b _ _,
    have l14_1 : C ^ 2 + D ^ 2 ∣ a ^ 2 + b ^ 2,
    { rw [←HCD, hA],
      apply dvd_mul_of_dvd_right,
      rwa int.coe_nat_dvd },
    have l14_2 : prime (C ^ 2 + D ^ 2),
    { rwa [←HCD, ←nat.prime_iff_prime_int] },
    obtain ⟨E, F, HEF, HEFcoprime⟩ := l1_4 a b C D habcoprime l14_1 l14_2,
    have hqdvd' : (q : ℤ) ∣ a ^ 2 + b ^ 2,
    { rw ←int.coe_nat_dvd at hqdvd,
      apply dvd_trans hqdvd,
      rw hA,
      apply dvd_mul_left },
    obtain ⟨B, hB⟩ := hqdvd,
    rw hB at hA,
    have B_lt_A : B < A,
    { rw hB,
      have : 0 < B,
      { rw pos_iff_ne_zero,
        rintro rfl,
        norm_num [hB] at hA' },
      rw lt_mul_iff_one_lt_left this,
      exact hqprime.one_lt },
    have two_B_lt_p : (2 * B : ℤ) < p,
    { norm_cast,
      calc 2 * B < 2 * A : by { rwa mul_lt_mul_left zero_lt_two, apply_instance, /-XXX-/ }
      ... < p : by { norm_cast at this, exact this } },
    have : (p * B : ℤ) = E ^ 2 + F ^ 2,
    { have : (q : ℤ) ≠ 0 := int.coe_nat_ne_zero.mpr hqprime.ne_zero,
      rw [←mul_right_inj' this, HCD, ←HEF, hA, ←HCD],
      norm_cast,
      ring },


    obtain ⟨E_bound, F_bound⟩ : (2 * E.nat_abs < p) ∧ (2 * F.nat_abs < p),
    { have EF_bound,
      calc 2 * (E ^ 2 + F ^ 2)
          = 2 * (p * B) : by rw this
      ... ≤ q * (p * B) : by {
        apply mul_le_mul_of_nonneg_right,
        { norm_cast, apply hqprime.two_le, },
        {rw [←int.coe_nat_mul], apply int.coe_nat_nonneg}, 
      }
      ... = a ^ 2 + b ^ 2 : by {rw [hA], norm_cast, ring,},

      split,
      { apply lt_of_pow_lt_pow 2,
        { apply zero_le,},
        zify,
        calc _
            = 2 * (2 * E ^ 2) : by rw [mul_pow, int.nat_abs_pow_two, pow_two, mul_assoc]
        ... ≤ 2 * (a ^ 2 + b ^ 2) : mul_le_mul_of_nonneg_left _ zero_le_two
        ... < p ^ 2 : bound,
        
        calc 2 * E ^ 2
            ≤ 2 * (E ^ 2 + F ^ 2) : by {
                  rw mul_add,
                  apply le_add_of_nonneg_right,
                  apply mul_nonneg,
                  apply zero_le_two,
                  apply (pow_two_nonneg _), }
        ... ≤ a ^ 2 + b ^ 2 : EF_bound },
      { apply lt_of_pow_lt_pow 2,
        { apply zero_le,},
        zify,
        calc _
            = 2 * (2 * F ^ 2) : by rw [mul_pow, int.nat_abs_pow_two, pow_two, mul_assoc]
        ... ≤ 2 * (a ^ 2 + b ^ 2) : mul_le_mul_of_nonneg_left _ zero_le_two
        ... < p ^ 2 : bound,
        
        calc 2 * F ^ 2
          ≤ 2 * (E ^ 2 + F ^ 2) : by {
                rw mul_add,
                apply le_add_of_nonneg_left,
                apply mul_nonneg,
                apply zero_le_two,
                apply (pow_two_nonneg _), }
        ... ≤ a ^ 2 + b ^ 2 : EF_bound },
    },

    refine IH2 _ B_lt_A two_B_lt_p _ _ HEFcoprime E_bound F_bound _ _ this.symm,
    { rw ←not_and_distrib,
      rintro ⟨rfl, rfl⟩,
      simp only [zero_pow zero_lt_two, add_zero, mul_zero] at HEF,
      contradiction, },
    { apply ineq E_bound F_bound },
    { rw ←int.coe_nat_dvd at hqdvd,
      apply dvd_trans hqdvd,
      rw hA,
      apply dvd_mul_left },
    { rwa int.gcd_eq_one_iff_coprime },
  },
end
-/
/-
lemma l3_25 -- p. 73
  (m : ℕ)
  (modd : odd m)
  (n : ℕ)
  (hn : 1 < n) :
  The number of ways that m is properly represented by a reduced form of discriminant -4 * n is
  2 * ∏ p ∣ m, (1 + zmod.legendre_sym (-n mod p) p)

-/