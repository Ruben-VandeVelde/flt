import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import algebra.euclidean_domain
import algebra.gcd_monoid
import tactic
import data.nat.modeq
import ring_theory.int.basic
import .primes
example (a b c : int) (h : a + b = c) : a = c - b := eq_sub_of_add_eq h
def flt_solution
  (n : ℕ)
  (a b c : ℤ) :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ 
  a ^ n + b ^ n = c ^ n

def flt_coprime
  (n : ℕ)
  (a b c : ℤ) :=
  flt_solution n a b c ∧ 
  is_coprime a b ∧
  is_coprime a c ∧
  is_coprime b c

section gcd_monoid
variables {α : Type*}
variables [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α]
lemma gcd_ne_zero_iff (a b : α) : gcd a b ≠ 0 ↔ a ≠ 0 ∨ b ≠ 0 :=
begin
  convert not_congr (gcd_eq_zero_iff a b),
  rw [eq_iff_iff, not_and_distrib],
end
end gcd_monoid

lemma int.gcd_eq_one_iff_coprime' {a b : ℤ} : gcd a b = 1 ↔ is_coprime a b :=
by rw [←int.coe_gcd, ←int.coe_nat_one, int.coe_nat_inj', int.gcd_eq_one_iff_coprime]

lemma coprime_div_gcd_div_gcd {a b : ℤ}
  (H : gcd a b ≠ 0) :
  is_coprime (a / (gcd a b)) (b / (gcd a b)) := by {
--theorem coprime_div_gcd_div_gcd {m n : ℕ} (H : 0 < gcd m n) :
--  coprime (m / gcd m n) (n / gcd m n) :=
--by delta coprime; rw [gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), nat.div_self H]
--refine int.gcd_eq_one_iff_coprime.mp _,
  have :=int.gcd_div (gcd_dvd_left a b) (gcd_dvd_right a b),
  rw ←int.gcd_eq_one_iff_coprime,
  rw this,
  rw ←int.coe_gcd,
  rw int.nat_abs_of_nat,
  rw nat.div_self,

  rw ←int.nat_abs_gcd,
  rw gt_iff_lt,
  rw pos_iff_ne_zero,
  rw int.nat_abs_ne_zero,
  exact H,

}
lemma exists_coprime
  (n : ℕ)
  (hn : 0 < n)
  {a b c : ℤ}
  (hsoln : flt_solution n a b c) :
  ∃ a' b' c' : ℤ,
    a'.nat_abs ≤ a.nat_abs ∧
    b'.nat_abs ≤ b.nat_abs ∧
    c'.nat_abs ≤ c.nat_abs ∧
    flt_coprime n a' b' c' :=
begin
  obtain ⟨ha, hb, hc, h⟩ := hsoln,
  let d := gcd a b,
  have hadvd : d ∣ a := gcd_dvd_left a b,
  have hbdvd : d ∣ b := gcd_dvd_right a b,
  have hcdvd : d ∣ c,
  { rw [←int.pow_dvd_pow_iff hn, ←h],
    apply dvd_add; rw int.pow_dvd_pow_iff hn; assumption },
  have hd : d ≠ 0 := (gcd_ne_zero_iff a b).mpr (or.inl ha),
  have hsoln : (a / d) ^ n + (b / d) ^ n = (c / d) ^ n,
  { apply int.eq_of_mul_eq_mul_right (pow_ne_zero n hd),
    calc ((a / d) ^ n + (b / d) ^ n) * d ^ n
        = (a / d * d) ^ n  + (b / d * d) ^ n : by rw [add_mul, mul_pow (a / d), mul_pow (b / d)]
    ... = a ^ n + b ^ n : by rw [int.div_mul_cancel hadvd, int.div_mul_cancel hbdvd]
    ... = c ^ n : h
    ... = (c / d * d) ^ n : by rw [int.div_mul_cancel hcdvd]
    ... = (c / d) ^ n * d ^ n : by rw mul_pow },
  have hsoln' : (b / d) ^ n + (a / d) ^ n = (c / d) ^ n,
  { rwa add_comm at hsoln },
  have hcoprime_div : is_coprime (a / d) (b / d) := coprime_div_gcd_div_gcd hd,
  exact ⟨
    a / d,
    b / d,
    c / d,
    (int.nat_abs_div _ _ hadvd).symm ▸ nat.div_le_self _ _,
    (int.nat_abs_div _ _ hbdvd).symm ▸ nat.div_le_self _ _,
    (int.nat_abs_div _ _ hcdvd).symm ▸ nat.div_le_self _ _,
    ⟨
      int.div_ne_zero_of_dvd ha hd hadvd,
      int.div_ne_zero_of_dvd hb hd hbdvd,
      int.div_ne_zero_of_dvd hc hd hcdvd,
      hsoln
    ⟩,
    hcoprime_div,
    coprime_add_self_pow hn hsoln hcoprime_div,
    coprime_add_self_pow hn hsoln' hcoprime_div.symm
  ⟩,
end

lemma descent1a {a b c : ℤ}
  (h : a ^ 3 + b ^ 3 = c ^ 3)
  (habcoprime : is_coprime a b)
  (haccoprime : is_coprime a c)
  (hbccoprime : is_coprime b c) :
  (even a ∧ ¬even b ∧ ¬even c ∨
   ¬even a ∧ even b ∧ ¬even c) ∨
  ¬even a ∧ ¬even b ∧ even c :=
begin
  have contra : ∀ {x y : ℤ}, is_coprime x y → even x → even y → false,
  { intros x y hcoprime hx hy,
    rw even_iff_two_dvd at hx hy,
    have := (dvd_gcd_iff 2 x y).mpr ⟨hx, hy⟩,
    rw ←int.gcd_eq_one_iff_coprime' at hcoprime,
    rw hcoprime at this,
    norm_num at this },
  by_cases haparity : even a;
  by_cases hbparity : even b;
  by_cases hcparity : even c,
  { exact false.elim (contra habcoprime ‹_› ‹_›) },
  { exact false.elim (contra habcoprime ‹_› ‹_›) },
  { exact false.elim (contra haccoprime ‹_› ‹_›) },
  { tauto },
  { exact false.elim (contra hbccoprime ‹_› ‹_›) },
  { tauto },
  { tauto },
  { exfalso,
    apply hcparity,
    rw [←int.even_pow' three_ne_zero, ←h],
    simp [haparity, hbparity, three_ne_zero] with parity_simps },
end

lemma descent1left {a b c : ℤ}
  (h : flt_coprime 3 a b c)
  (ha : even a)
  (hb : ¬even b)
  (hc : ¬even c) :
  ∃ (p q : ℤ),
    p ≠ 0 ∧
      q ≠ 0 ∧
        p.gcd q = 1 ∧
          (even p ↔ ¬even q) ∧
            (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
                 2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) :=
begin
  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, habcoprime, haccoprime, hbccoprime⟩ := h,

  obtain ⟨p, hp⟩ : even (c - b),
  { simp [hb, hc] with parity_simps},
  obtain ⟨q, hq⟩ : even (c + b),
  { simp [hb, hc] with parity_simps},
  have hadd : p + q = c,
  { apply int.eq_of_mul_eq_mul_left two_ne_zero,
    rw [mul_add, ←hp, ←hq],
    ring },

  have : b ≠ c,
  { rintro rfl,
    conv_rhs at h { rw ←zero_add (b ^ 3), },
    exact (hapos $ pow_eq_zero $ add_right_cancel h) },
  have : p ≠ 0,
  { rintro rfl,
    rw [mul_zero, sub_eq_zero] at hp,
    exact this hp.symm },

  have hsub : q - p = b,
  { apply int.eq_of_mul_eq_mul_left two_ne_zero,
    rw [mul_sub, ←hp, ←hq],
    ring },
  have hqpos : q ≠ 0,
  { apply right_ne_zero_of_mul,
    { rw ←hq,
      intro H,
      rw add_eq_zero_iff_eq_neg at H,
      subst c,
      norm_cast,
      apply nat.add_pos_left hcpos },
    { norm_num } },


  refine ⟨p.nat_abs, q.nat_abs, _, _, _, _, _⟩,
  { rw pos_iff_ne_zero,
    rw int.nat_abs_ne_zero,
    assumption, },
  { rw pos_iff_ne_zero,
    rw int.nat_abs_ne_zero,
    apply ne_of_gt,
    assumption, },
  { rw [←nat.dvd_one, ←hbccoprime.gcd_eq_one],
    apply nat.dvd_gcd; rw ←int.coe_nat_dvd,
    { rw ← hsub,
      apply dvd_sub; rw int.coe_nat_dvd_left,
      { apply nat.gcd_dvd_right },
      { apply nat.gcd_dvd_left } },
    { rw ← hadd,
      apply dvd_add; rw int.coe_nat_dvd_left,
      { apply nat.gcd_dvd_left },
      { apply nat.gcd_dvd_right } } },
  { have : ¬even (p + q),
    { rwa [hadd, int.even_coe_nat] },
    simp with parity_simps at this ⊢,
    tauto },
  { left,
    zify,
    zify at h,
    rw eq_sub_of_add_eq h,
    rw [←hadd, ←hsub],
    have : p = p.nat_abs,
    { lift p to ℕ using hppos.le,
      rw [int.nat_abs_of_nat] },
    rw ←this,
    have : q = q.nat_abs,
    { lift q to ℕ using hqpos.le,
      rw [int.nat_abs_of_nat] },
    rw ←this,
    ring },
end

lemma two_not_cube (r : ℕ) : r ^ 3 ≠ 2 :=
begin
  have : 1 ≤ 3,
  { norm_num },
  apply monotone.ne_of_lt_of_lt_nat (nat.pow_left_strict_mono this).monotone 1; norm_num,
end

lemma flt_not_add_self {a b c : ℕ} (hapos : 0 < a) (h : a ^ 3 + b ^ 3 = c ^ 3) : a ≠ b :=
begin
  rintro rfl,
  rw ←mul_two at h,
  apply two_not_cube (c/a),
  rw div_pow',
  rw ←h,
  rw mul_comm,
  rw nat.mul_div_cancel,
  exact pow_pos hapos 3,

  rw ←nat.pow_dvd_pow_iff (by norm_num : 0 < 3),
  rw ←h,
  apply dvd_mul_right,
end

lemma descent1 (a b c : ℤ)
  (h : flt_coprime 3 a b c) :
  ∃ (p q : ℤ),
    0 < p ∧
    0 < q ∧
    p.gcd q = 1 ∧
    (even p ↔ ¬even q) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) :=
begin
  have h' := h,
  obtain ⟨⟨hapos, hbpos, hcpos, h⟩, habcoprime, haccoprime, hbccoprime⟩ := h,
  have := descent1a h habcoprime haccoprime hbccoprime,
  cases this,
  { cases this,
    { rcases this with ⟨ha, hb, hc⟩,
      exact descent1left h' ha hb hc },
    { rw add_comm at h,
      rcases this with ⟨ha, hb, hc⟩,
      have := descent1left hbpos hapos hcpos h habcoprime.symm hbccoprime haccoprime hb ha hc,
      obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := this,
      refine ⟨p, q, hp, hq, hcoprime, hodd, _⟩,
      tauto } },
  {
    rcases this with ⟨ha, hb, hc⟩,
    obtain ⟨p, hp⟩ : even (a + b : ℤ),
    { simp [ha, hb] with parity_simps},
    obtain ⟨q, hq⟩ : even (a - b : ℤ),
    { simp [ha, hb] with parity_simps},
    have hadd : p + q = a,
    { apply int.eq_of_mul_eq_mul_left two_ne_zero,
      rw [mul_add, ←hp, ←hq],
      ring },
    have hsub : p - q = b,
    { apply int.eq_of_mul_eq_mul_left two_ne_zero,
      rw [mul_sub, ←hp, ←hq],
      ring },
    have : p ≠ 0,
    { rintro rfl,
      rw [mul_zero, ←int.coe_nat_zero, ←int.coe_nat_add, int.coe_nat_eq_coe_nat_iff] at hp,
      exact ne_of_gt hapos (nat.eq_zero_of_add_eq_zero_right hp) },
    have : int.gcd p q = 1,
    { rw [←nat.dvd_one, ←habcoprime.gcd_eq_one],
      apply nat.dvd_gcd; rw ←int.coe_nat_dvd,
      { rw ← hadd,
        apply dvd_add; rw int.coe_nat_dvd_left,
        { apply nat.gcd_dvd_left },
        { apply nat.gcd_dvd_right } },
      { rw ← hsub,
        apply dvd_sub; rw int.coe_nat_dvd_left,
        { apply nat.gcd_dvd_left },
        { apply nat.gcd_dvd_right } } },
    have : 0 < p,
    { refine pos_of_mul_pos_left _ zero_lt_two.le,
      { rw ←hp,
        norm_cast,
        apply nat.add_pos_left hapos } },
    have : p = p.nat_abs,
    { rw ←int.abs_eq_nat_abs,
      symmetry,
      apply abs_of_nonneg,
      exact this.le },
    have : q ≠ 0,
    { rintro rfl,
      apply flt_not_add_self hapos h,
      rwa [mul_zero, sub_eq_zero, int.coe_nat_inj'] at hq },
    refine ⟨p.nat_abs, q.nat_abs, _, _, _, _, _⟩,
    { rw pos_iff_ne_zero,
      rw int.nat_abs_ne_zero,
      apply ne_of_gt,
      assumption, },
    { rw pos_iff_ne_zero,
      rw int.nat_abs_ne_zero,
      assumption, },
    { assumption },
    { have : ¬even (p + q),
      { rwa [hadd, int.even_coe_nat] },
      simp with parity_simps at this ⊢,
      tauto },
    { right, right,
      rw  ←h,
      zify,
      rw [←‹p = _›, int.nat_abs_square q, ←hadd, ←hsub],
      ring,
    } },
end

lemma descent11 {a b c d : ℕ} (h : d = a ∨ d = b ∨ d = c) : d ∣ (a * b * c) :=
begin
  rcases h with rfl | rfl | rfl,
  { apply dvd_mul_of_dvd_left, apply dvd_mul_right },
  { apply dvd_mul_of_dvd_left, apply dvd_mul_left },
  { apply dvd_mul_left }
end

lemma descent12 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
 (h : d = a ∨ d = b ∨ d = c) : d ≤ (a * b * c) :=
nat.le_of_dvd (mul_pos (mul_pos ha hb) hc) (descent11 h)

lemma descent2 (a b c : ℕ)
  (h : flt_coprime a b c 3) :
  ∃ (p q : ℕ),
    0 < p ∧
    0 < q ∧
    p.gcd q = 1 ∧
    (even p ↔ ¬even q) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) ∧
    (2 * p < a ^ 3 * b ^ 3 * c ^ 3) :=
begin
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := descent1 a b c h,
  refine ⟨p, q, hp, hq, hcoprime, hodd, hcube, _⟩,

  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  apply lt_of_lt_of_le,
  swap,
  { refine descent12 _ _ _ hcube;
    rwa ←nat.pos_pow_iff zero_lt_three },
  { apply lt_mul_of_one_lt_right,
    { linarith },
    { rw nat.pos_pow_iff zero_lt_two at hp hq,
      linarith } }
end

lemma gcd1or3
  (p q : ℕ)
  (hp : 0 < p) (hq : 0 < q)
  (hcoprime : nat.coprime p q)
  (hparity : even p ↔ ¬even q) :
  nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 1 ∨ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 3 :=
begin
  let g := nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2),
  suffices H : ∃ k, g = 3 ^ k ∧ k < 2,
  { obtain ⟨k, hg, hk⟩ := H,
    rcases k with (_|_|_),
    { left, norm_num at hg, exact hg },
    { right, norm_num at hg, exact hg },
    { change k + 2 < 2 at hk,
      linarith },
  },

  have basic : ∀ f, nat.prime f → f ∣ 2 * p → f ∣ (p ^ 2 + 3 * q ^ 2) → f = 3,
  { intros d hdprime hdleft hdright,
    have hne2 : d ≠ 2,
    { rintro rfl,
      change even _ at hdright,
      simp [hparity, two_ne_zero] with parity_simps at hdright,
      assumption },
    have : 2 < d := lt_of_le_of_ne (hdprime.two_le) hne2.symm,
    by_contra hne3,
    change d ≠ 3 at hne3,
    have : 3 < d := lt_of_le_of_ne (this) hne3.symm,
    obtain ⟨P, hP⟩ := hdleft,
    obtain ⟨Q, hQ⟩ := hdright,
    obtain ⟨H, hH⟩ : 2 ∣ P,
    { have H := dvd_mul_right 2 p,
      rw [hP, nat.prime.dvd_mul nat.prime_two] at H,
      cases H,
      { rw nat.dvd_prime hdprime at H,
        cases H,
        { norm_num at H },
        { exfalso,
          exact hne2 H.symm } },
      { assumption } },
    have : p = d * H,
    { rw [←nat.mul_right_inj zero_lt_two, hP, hH],
      ring },
    have : 3 * q ^ 2 = d * (Q - d * H ^ 2),
    { calc 3 * q ^ 2
          = d * Q - p ^ 2 : (nat.sub_eq_of_eq_add hQ.symm).symm
      ... = d * Q - d ^ 2 * H ^ 2 : by rw [this, mul_pow]
      ... = d * Q - d * (d * H ^ 2) : by ring
      ... = d * (Q - d * H ^ 2) : by rw nat.mul_sub_left_distrib },
    have : d ∣ q,
    { have h000 : d ∣ 3 * q ^ 2,
      { rw this,
        apply dvd_mul_right },
      rw nat.prime.dvd_mul hdprime at h000,
      cases h000,
      { linarith [nat.le_of_dvd (by norm_num) h000] },
      { exact nat.prime.dvd_of_dvd_pow hdprime h000 } },
    have : d ∣ p,
    { rw ‹p = _›, exact dvd_mul_right d H },
    have := nat.not_coprime_of_dvd_of_dvd hdprime.one_lt ‹d ∣ p› ‹d ∣ q›,
    contradiction },

  set k := g.factors.length,
  have hg : g = 3 ^ k,
  { apply eq_pow,
   { apply nat.gcd_pos_of_pos_left,
     apply nat.mul_pos zero_lt_two hp },
    intros d hdprime hddvdg,
    apply basic _ hdprime,
    exact dvd_trans hddvdg (nat.gcd_dvd_left _ _),
    exact dvd_trans hddvdg (nat.gcd_dvd_right _ _) },
  refine ⟨k, hg, _⟩,
  by_contra H,
  push_neg at H,
  rw ←pow_mul_pow_sub _ H at hg,
  have hdvdp : 3 ∣ p,
  { suffices : 3 ∣ 2 * p,
    { apply dvd_mul_cancel_prime this (by norm_num) nat.prime_two nat.prime_three },
    have : 3 ∣ g,
    { rw [hg, pow_two, mul_assoc],
      apply dvd_mul_right },
    exact dvd_trans this (nat.gcd_dvd_left _ _) }, 
  have hdvdq : 3 ∣ q,
  { have dvdpsq : 3 ^ 2 ∣ p ^ 2,
    { rwa nat.pow_dvd_pow_iff zero_lt_two },
    suffices : 3 ∣ q ^ 2,
    { apply nat.prime.dvd_of_dvd_pow nat.prime_three this },
    suffices : 3 ^ 2 ∣ 3 * q ^ 2,
    { rwa [pow_two, nat.mul_dvd_mul_iff_left (by norm_num : 0 < 3)] at this },
    suffices : 3 ^ 2 ∣ p ^ 2 + 3 * q ^ 2,
    { rwa nat.dvd_add_iff_right dvdpsq },
    refine dvd_trans _ (nat.gcd_dvd_right _ _),
    exact 2 * p,
    change 3 ^ 2 ∣ g,
    rw hg,
    apply dvd_mul_right },

  apply nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 3) hdvdp hdvdq hcoprime,
end

lemma factors2
  {a b : ℕ}
  (heven : even (a ^ 2 + 3 * b ^ 2)) :
  ∃ c d, a ^ 2 + 3 * b ^ 2 = 4 * (c ^ 2 + 3 * d ^ 2) :=
begin
  have hparity : even a ↔ even b,
  { simp [two_ne_zero] with parity_simps at heven, assumption },

  by_cases h : even a,
  {
    obtain ⟨d, hd⟩ := hparity.mp h,
    obtain ⟨c, hc⟩ := h,
    use [c, d],
    rw [hc, hd],
    ring },
  { have : ¬even b,
    { rwa ←hparity },

    obtain ⟨m, hm⟩ := mod_four_of_odd' h,
    zify at hm,
    obtain ⟨n, hn⟩ := mod_four_of_odd' this,
    zify at hn,
    have h4 : (4 : ℤ) ∣ a + b ∨ (4 : ℤ) ∣ a - b,
    {
      cases hm; cases hn; rw [hm, hn],
      any_goals
      { right,
        rw [add_sub_add_right_eq_sub, ←mul_sub_left_distrib],
        apply dvd_mul_right },
      all_goals
      { left,
        rw add_assoc,
        apply dvd_add (dvd_mul_right _ _),
        rw [add_comm, add_assoc],
        apply dvd_add (dvd_mul_right _ _),
        apply dvd_refl } },
    have h4coe : (4 : ℤ) = ((4 : ℕ) : ℤ),
    { refl },
    cases h4,
    { obtain ⟨v, hv⟩ := h4,
      obtain ⟨u, hu⟩ : (4 : ℤ) ∣ a - 3 * b,
      { have : (a - 3 * b : ℤ) = a + b - 4 * b,
        { ring },
        rw this,
        apply dvd_sub ⟨v, hv⟩ (dvd_mul_right _ _) },
      use [u.nat_abs, v.nat_abs],
      apply nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4),
      zify,
      rw [int.nat_abs_pow_two u, int.nat_abs_pow_two v],
      calc (4 * (a ^ 2 + 3 * b ^ 2) : ℤ)
          = (a - 3 * b) ^ 2 + 3 * (a + b) ^ 2 : by ring
      ... = (4 * u) ^ 2 + 3 * (4 * v) ^ 2 : by rw [hu, hv]
      ... = 4 * (4 * (u ^ 2 + 3 * v ^ 2)) : by ring },
    { obtain ⟨v, hv⟩ := h4,
      obtain ⟨u, hu⟩ : (4 : ℤ) ∣ a + 3 * b,
      { have : (a + 3 * b : ℤ) = a - b + 4 * b,
        { ring },
        rw this,
        apply dvd_add ⟨v, hv⟩ (dvd_mul_right _ _) },
      use [u.nat_abs, v.nat_abs],
      apply nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4),
      zify,
      rw [int.nat_abs_pow_two u, int.nat_abs_pow_two v],
      calc (4 * (a ^ 2 + 3 * b ^ 2) : ℤ)
          = (a + 3 * b) ^ 2 + 3 * (a - b) ^ 2 : by ring
      ... = (4 * u) ^ 2 + 3 * (4 * v) ^ 2 : by rw [hu, hv]
      ... = 4 * (4 * (u ^ 2 + 3 * v ^ 2)) : by ring }
  }
end

lemma factors2'
  {a : ℕ}
  (hpos : 0 < a)
  (heven : 2 ∣ a) :
  ∃ k l : ℕ, a = 2 ^ k * l ∧ ¬(2 ∣ l) :=
begin
  revert hpos heven,
  apply nat.strong_induction_on a,
  intros a' IH hpos heven,
  obtain ⟨b, hb⟩ := heven,
  have hbpos : 0 < b,
  { rw pos_iff_ne_zero,
    rintro rfl,
    rw mul_zero at hb,
    subst hb,
    exact lt_irrefl _ hpos },
  have hsmaller : b < a',
  { rw [hb, lt_mul_iff_one_lt_left hbpos],
    norm_num },
  by_cases H : even b,
  { obtain ⟨k', l', heqb, hnotdvd⟩ := IH b hsmaller hbpos H,
    refine ⟨k' + 1, l', _, hnotdvd⟩,
    rw [hb, heqb, pow_succ, mul_assoc] },
  { refine ⟨1, b, _, H⟩,
    rwa pow_one }
end

lemma factors2''
  {a b : ℕ}
  (hnontrivial : a ^ 2 + 3 * b ^ 2 ≠ 0)
  (heven : even (a ^ 2 + 3 * b ^ 2)) :
  ∃ c d k : ℕ,
    a ^ 2 + 3 * b ^ 2 = 4 ^ k * (c ^ 2 + 3 * d ^ 2) ∧
    ¬even (c ^ 2 + 3 * d ^ 2) :=
begin
  suffices : ∀ s a b : ℕ,
    s = a ^ 2 + 3 * b ^ 2 →
    s ≠ 0 →
    even s →
    ∃ c d k : ℕ, s = 4 ^ k * (c ^ 2 + 3 * d ^ 2) ∧ ¬even (c ^ 2 + 3 * d ^ 2),
  {
    exact this ( a ^ 2 + 3 * b ^ 2 ) a b rfl hnontrivial heven,
  },
  intro s',
  apply nat.strong_induction_on s',
  rintros s IH a b rfl hnontrivial heven,
  obtain ⟨c, d, hcd⟩ := factors2 heven,
  by_cases H : 2 ∣ (c ^ 2 + 3 * d ^ 2),
  { have : (c ^ 2 + 3 * d ^ 2) < (a ^ 2 + 3 * b ^ 2),
    { rw ←mul_lt_mul_left (by norm_num : 0 < 4),
      rw ←hcd,
      suffices : 1 * (a ^ 2 + 3 * b ^ 2) < 4 * (a ^ 2 + 3 * b ^ 2),
      { rwa nat.one_mul  at this, },
      refine nat.mul_lt_mul _ _ _,
      { norm_num },
      { refl },
      { rwa pos_iff_ne_zero } },
    
    obtain ⟨c', d', k', hcd', heven'⟩ := IH (c ^ 2 + 3 * d ^ 2) this c d rfl _ H,
    refine ⟨c', d', k' + 1, _, heven'⟩,
    { rw [hcd, hcd', ←mul_assoc, (pow_succ 4)] },
    { rintro HH,
      rw [HH, mul_zero] at hcd,
      exact hnontrivial hcd } },
  { refine ⟨c, d, 1, _, H⟩,
    rw pow_one,
    exact hcd }
end

lemma int.sq_plus_three_sq_eq_zero_iff {a b : ℤ} : a ^ 2 + 3 * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 :=
begin
  split,
  { intro h,
    have hposleft := pow_two_nonneg a,
    have hposright := mul_nonneg (by norm_num : (0 : ℤ) ≤ 3) (pow_two_nonneg b),
    obtain ⟨ha, hb⟩ := (add_eq_zero_iff_eq_zero_of_nonneg hposleft hposright).mp h,
    split,
    { exact pow_eq_zero ha },
    { rw [mul_eq_zero, eq_false_intro (by norm_num : (3 : ℤ) ≠ 0), false_or] at hb,
      exact pow_eq_zero hb } },
  { rintro ⟨rfl, rfl⟩, norm_num }
end

lemma nat.sq_plus_three_sq_eq_zero_iff {a b : ℕ} : a ^ 2 + 3 * b ^ 2 = 0 ↔ a = 0 ∧ b = 0 :=
begin
  zify,
  exact int.sq_plus_three_sq_eq_zero_iff
end

lemma spts_mul_spts
  {a b c d : ℕ} :
  ∃ e f, (a ^ 2 + 3 * b ^ 2) * (c ^ 2 + 3 * d ^ 2) = e ^ 2 + 3 * f ^ 2 :=
begin
  use [(a * c - 3 * b * d : ℤ).nat_abs, a * d + b * c],
  zify,
  rw int.nat_abs_pow_two,
  ring,
end
example (a b c : int) (h : a = b + c) : (a - c = b) := sub_eq_of_eq_add h
lemma sq_plus_three_sq_prime_dvd (p q a b: ℕ)
  (hprime : nat.prime (p ^ 2 + 3 * q ^ 2))
  (h : p ^ 2 + 3 * q ^ 2 ∣ a ^ 2 + 3 * b ^ 2) :
  ∃ c d, (p ^ 2 + 3 * q ^ 2) * (c ^ 2 + 3 * d ^ 2) = a ^ 2 + 3 * b ^ 2 :=
begin
  obtain ⟨f, hf⟩ := h,
  rw hf,
  have : ((p * b - a * q) * (p * b + a * q) : ℤ) = b ^ 2 * (p ^ 2 + 3 * q ^ 2) - q ^ 2 * (a ^ 2 + 3 * b ^ 2),
  { ring },
  have : ((p * b - a * q) * (p * b + a * q) : ℤ) = (p ^ 2 + 3 * q ^ 2) * (b ^ 2 - q ^ 2 * f),
  { rw this,
    zify at hf,
    rw hf,
    ring },
  have h0 : p ^ 2 + 3 * q ^ 2 ∣ (p * b - a * q : ℤ).nat_abs ∨
         p ^ 2 + 3 * q ^ 2 ∣ (p * b + a * q : ℤ).nat_abs,
  { apply int.prime.dvd_mul hprime,
    rw this,
    norm_cast,
    apply dvd_mul_right },
  have h1 : (p ^ 2 + 3 * q ^ 2) * (a ^ 2 + 3 * b ^ 2) =
            (p * a - 3 * q * b : ℤ).nat_abs ^ 2 + 3 * (p * b + a * q : ℤ).nat_abs ^ 2,
  { zify,
    rw int.nat_abs_pow_two,
    rw int.nat_abs_pow_two,
    ring },
  have h1' : (p ^ 2 + 3 * q ^ 2) * (a ^ 2 + 3 * b ^ 2) =
             (p * a + 3 * q * b : ℤ).nat_abs ^ 2 + 3 * (p * b - a * q : ℤ).nat_abs ^ 2,
  { zify,
    rw int.nat_abs_pow_two,
    rw int.nat_abs_pow_two,
    ring },
  cases h0 with h0 h0,
  swap,
  { obtain ⟨d, hd⟩ := h0,
    obtain ⟨c, hc⟩ : (p ^ 2 + 3 * q ^ 2) ∣ (p * a - 3 * q * b : ℤ).nat_abs,
    { apply @nat.prime.dvd_of_dvd_pow _ _ 2 hprime,
      rw nat.dvd_add_iff_left,
      { rw ←h1, exact dvd_mul_right _ _},
      { apply dvd_mul_of_dvd_right,
        rw ←int.coe_nat_dvd,
        rw hd,
        rw int.coe_nat_dvd,
        apply dvd_pow _ two_ne_zero,
        apply dvd_mul_right } },
    use [c, d],
    apply nat.eq_of_mul_eq_mul_left hprime.pos,
    rw [←hf, h1, hc, hd],
    ring },
  { obtain ⟨d, hd⟩ := h0,
    obtain ⟨c, hc⟩ : (p ^ 2 + 3 * q ^ 2) ∣ (p * a + 3 * q * b : ℤ).nat_abs,
    { apply @nat.prime.dvd_of_dvd_pow _ _ 2 hprime,
      rw nat.dvd_add_iff_left,
      { rw ←h1', exact dvd_mul_right _ _},
      { apply dvd_mul_of_dvd_right,
        rw ←int.coe_nat_dvd,
        rw hd,
        rw int.coe_nat_dvd,
        apply dvd_pow _ two_ne_zero,
        apply dvd_mul_right } },
    use [c, d],
    apply nat.eq_of_mul_eq_mul_left hprime.pos,
    rw [←hf, h1', hc, hd],
    ring },
end

lemma factors'
  (a b f g : ℕ)
  (hodd : ¬even f)
  (hgpos : 0 < g)
  (hfactor : f * g = (a ^ 2 + 3 * b ^ 2))
  (hnotform : ¬∃p q, f = p ^ 2 + 3 * q ^ 2)
  :
  ∃ f',
    f' ∣ g ∧
    ¬even f' ∧
    ¬∃p q, f' = p ^ 2 + 3 * q ^ 2 :=
begin
  contrapose! hnotform,
  revert g a b,
  intro g',
  apply g'.strong_induction_on _,
  intros g IH a b hgpos hfactor hnotform,
  by_cases H : 2 ∣ a ^ 2 + 3 * b ^ 2,
  { obtain ⟨c, d, hcd⟩ := factors2 H,
    obtain ⟨g', hg'⟩ : 2 ^ 2 ∣ g,
    { apply @nat.coprime.dvd_of_dvd_mul_left f _ (2 ^ 2) _ _,
      { apply nat.coprime.symm,
        exact nat.prime.coprime_pow_of_not_dvd nat.prime_two hodd },
      { rw [hfactor, hcd],
        exact dvd_mul_right _ _ } },
    have hgcdcd : 0 < nat.gcd c d,
    { rw pos_iff_ne_zero,
      intro H',
      obtain ⟨rfl, rfl⟩ := nat.gcd_eq_zero_iff.mp H',
      simp only [zero_pow, zero_lt_two, nat.mul_eq_zero, add_eq_zero_iff, mul_zero,
        pow_eq_zero_iff, three_ne_zero, false_or] at hcd,
      obtain ⟨rfl, rfl⟩ := hcd,
      norm_num at hfactor,
      rcases hfactor with (rfl|rfl),
      { exact hodd nat.even_zero },
      { exact (lt_irrefl 0) hgpos } },
    refine IH g' _ c d _ _ _,
    { rw hg',
      apply nat.lt_mul_left; linarith },
    { rw hg' at hgpos,
      linarith, },
    { rw [←nat.mul_right_inj (by norm_num : 0 < 4), ←hcd, ←hfactor, hg'],
      ring },
    { intros f' hf'dvd hf'odd,
      refine hnotform f' _ hf'odd,
      rw hg',
      apply dvd_mul_of_dvd_right hf'dvd } },
  { by_cases g = 1,
    { subst h,
      rw mul_one at hfactor,
      exact ⟨_, _, hfactor⟩ },
    { rw ←ne.def at h,
      have : 2 ≤ g,
      { rw nat.succ_le_iff,
        apply lt_of_le_of_ne _ h.symm,
        rw nat.succ_le_iff,
        exact hgpos },
      obtain ⟨p, pprime, pdvd⟩ := nat.exists_prime_and_dvd this,
      have podd : ¬even p,
      { rcases pprime.eq_two_or_odd with (rfl|hodd),
        { contrapose! H,
          rw ←hfactor,
          apply dvd_mul_of_dvd_right pdvd },
        { exact nat.not_even_iff.mpr hodd } },
      obtain ⟨A, B, hAB⟩ := hnotform p pdvd podd,
      have pdvd' : A ^ 2 + 3 * B ^ 2 ∣ a ^ 2 + 3 * b ^ 2,
      { rw ←hAB,
        apply dvd_trans pdvd,
        rw ←hfactor,
        exact dvd_mul_left g f },
      rw hAB at pprime,
      obtain ⟨c, d, hcd⟩ := sq_plus_three_sq_prime_dvd A B _ _ pprime pdvd',
      obtain ⟨q, hq⟩ := pdvd,
      refine IH q _ c d _ _ _,
      { rw [hq, hAB],
        apply nat.lt_mul_left _ _ pprime.one_lt,
        rw hq at hgpos,
        rw pos_iff_ne_zero at hgpos ⊢,
        contrapose! hgpos,
        subst hgpos,
        rw mul_zero },
      { rw hq at hgpos,
        rw pos_iff_ne_zero,
        rintro rfl,
        norm_num at hgpos },
      { rw ←nat.mul_right_inj pprime.pos,
        rw hcd,
        rw ←hfactor,
        rw hq,
        rw ←hAB,
        ring },
      { intros f' hf'dvd hf'odd,
        refine hnotform f' _ hf'odd,
        rw hq,
        apply dvd_mul_of_dvd_right hf'dvd },
    } }
end

lemma factor_div (a x : ℕ)
  (hodd : ¬even x)
  (h0' : 0 < x) :
  ∃ (m : ℕ) (c : ℤ), c + ↑m * ↑x = ↑a ∧ 2 * c.nat_abs < x :=
begin
    set c : ℤ := a % x with hc,
    have : c < x,
    { rw hc,
      exact int.mod_lt_of_pos a (int.coe_nat_lt.mpr h0') },
    by_cases H : 2 * c.nat_abs < x,
    {
      refine ⟨a/x, c, _, H⟩,
      rw hc,
      norm_cast,
      rw mul_comm,
      exact nat.mod_add_div a x },
    { push_neg at H,
      set c' : ℤ := c - x with hc',
      refine ⟨a / x + 1, c', _, _⟩,
      { rw [←int.coe_nat_mul, add_mul, one_mul],
        push_cast,
        rw hc',
        conv_rhs { rw ←nat.mod_add_div a x },
        ring },
      { rw hc',
        rw ←int.nat_abs_neg,
        rw neg_sub,
        zify,
        rw ←int.abs_eq_nat_abs,
        rw abs_of_nonneg _,
        { rw mul_sub,
          rw sub_lt_iff_lt_add,
          rw two_mul,
          rw add_lt_add_iff_left,
          rw hc, norm_cast,
          apply lt_of_le_of_ne,
          { convert H, },
          { contrapose! hodd with heqtwomul,
            exact ⟨_, heqtwomul⟩ } },
        rw sub_nonneg,
        exact le_of_lt this,
      } },
end

lemma factors
  (a b x : ℕ)
  (hcoprime : nat.gcd a b = 1)
  (hodd : ¬even x)
  (hfactor : x ∣ (a ^ 2 + 3 * b ^ 2)) :
  ∃ c d, x = c ^ 2 + 3 * d ^ 2 :=
begin
  revert x a b,
  intro x',
  apply nat.strong_induction_on x',
  clear x',
  intros x IH a b hcoprime hodd hfactor,
  have hneg1 : 1 ≤ a ^ 2 + 3 * b ^ 2,
  { rw [nat.succ_le_iff, pos_iff_ne_zero],
    intro H,
    obtain ⟨rfl, rfl⟩ := nat.sq_plus_three_sq_eq_zero_iff.mp H,
    simp only [nat.gcd_zero_right, zero_ne_one] at hcoprime,
    assumption },
  by_cases h : x = 1,
  { subst h,
    refine ⟨1, 0, _⟩,
    ring },
  obtain ⟨f, hf⟩ := hfactor,
  have h0' : 0 < x,
  { rw pos_iff_ne_zero,
    rintro rfl,
    exact hodd nat.even_zero },

  have h0 : 1 < x,
  { apply lt_of_le_of_ne _ _,
    { apply nat.succ_le_of_lt,
      exact h0' },
    { symmetry,
      exact h } },

  obtain ⟨m, c, ha, hc⟩ := factor_div a x hodd h0',
  obtain ⟨n, d, hb, hd⟩ := factor_div b x hodd h0',

  set e : ℤ := m ^ 2 * x + 2 * m * c + 3 * n ^ 2 * x + 6 * n * d with he,

  have h1 : (a ^ 2 + 3 * b ^ 2 : ℤ) = x * e + c ^ 2 + 3 * d ^ 2,
  { rw [he, ←ha, ←hb],
    ring },

  have h2 : (x : ℤ) ∣ c ^ 2 + 3 * d ^ 2,
  { have : c ^ 2 + 3 * d ^ 2 = x * e + c ^ 2 + 3 * d ^ 2 - x * e,
    { ring },
    rw this,
    apply dvd_sub,
    { rw ←h1,
      norm_cast,
      rw hf,
      exact dvd_mul_right _ _ },
    { exact dvd_mul_right _ _ }
  },

  obtain ⟨y, hy⟩ : x ∣ c.nat_abs ^ 2 + 3 * d.nat_abs ^ 2,
  { rw ←int.coe_nat_dvd,
    push_cast,
    rw [int.nat_abs_pow_two c, int.nat_abs_pow_two d],
    exact h2 },

  have h3 : y < x,
  {
    rw ←mul_lt_mul_left h0',
    rw ←mul_lt_mul_left (by norm_num : 0 < 4),
    calc 4 * (x * y)
        = 4 * (c.nat_abs ^ 2 + 3 * d.nat_abs ^ 2) : by rw hy
    ... = (2 * c.nat_abs) ^ 2 + 3 * (2 * d.nat_abs) ^ 2 : by ring
    ... < x ^ 2 + 3 * x ^ 2 : add_lt_add _ _
    ... = 4 * (x * x) : by ring,
    { exact nat.pow_lt_pow_of_lt_left hc zero_lt_two },
    { rw mul_lt_mul_left (by norm_num : 0 < 3),
      exact nat.pow_lt_pow_of_lt_left hd zero_lt_two },
  },

  have h4 : c ^ 2 + 3 * d ^ 2 ≠ 0,
  { contrapose! hcoprime with H,
    obtain ⟨rfl, rfl⟩ := int.sq_plus_three_sq_eq_zero_iff.mp H,
    norm_num at ha hb,
    norm_cast at ha hb,
    apply nat.not_coprime_of_dvd_of_dvd h0,
    { rw ←ha, exact dvd_mul_left _ _ },
    { rw ←hb, exact dvd_mul_left _ _ } },

  set g := nat.gcd c.nat_abs d.nat_abs with hg,
  have hgpos : 0 < g,
  { rw hg,
    suffices H : 0 < c.nat_abs ∨ 0 < d.nat_abs,
    { cases H,
      { exact nat.gcd_pos_of_pos_left _ H },
      { exact nat.gcd_pos_of_pos_right _ H } },

    contrapose! h4 with H,
    obtain ⟨H1, H2⟩ := H,
    rw [nat.le_zero_iff, int.nat_abs_eq_zero] at H1 H2,
    subst H1,
    subst H2,
    norm_num },
  obtain ⟨C, D, HCDcoprime, HC, HD⟩ := nat.exists_coprime hgpos,
  rw ←hg at HC HD,
  have h5 : x * y = (C ^ 2 + 3 * D ^ 2) * g ^ 2,
  { rw [←hy, HC, HD],
    ring },
  obtain ⟨z, hz⟩ : g ^ 2 ∣ y,
  { have : g ^ 2 ∣ x * y,
    { rw h5, exact dvd_mul_left _ _ },
    apply nat.coprime.dvd_of_dvd_mul_left _ this,
    apply nat.coprime_of_dvd',
    rintros p hpprime hpdvdleft ⟨X, hX⟩,
    obtain ⟨G, hG⟩ := hpprime.dvd_of_dvd_pow hpdvdleft,
    rw ←hcoprime,
    apply nat.dvd_gcd,
    { rw [←int.coe_nat_dvd, ←ha],
      apply dvd_add,
      { rw [int.coe_nat_dvd_left, HC, hG],
        apply dvd_mul_of_dvd_right,
        exact dvd_mul_right _ _ },
      { apply dvd_mul_of_dvd_right,
        rw [int.coe_nat_dvd, hX],
        exact dvd_mul_right _ _ } },
    { rw [←int.coe_nat_dvd, ←hb],
      apply dvd_add,
      { rw [int.coe_nat_dvd_left, HD, hG],
        apply dvd_mul_of_dvd_right,
        exact dvd_mul_right _ _ },
      { apply dvd_mul_of_dvd_right,
        rw [int.coe_nat_dvd, hX],
        exact dvd_mul_right _ _ } } },

  have h6 : x * z = C ^ 2 + 3 * D ^ 2,
  { apply nat.eq_of_mul_eq_mul_right (pow_pos hgpos 2),
    rw [←h5, hz],
    ring },

  contrapose! IH,
  have h6' : z ∣ C ^ 2 + 3 * D ^ 2 := h6 ▸ dvd_mul_left z x,
  have h6'' : x ∣ C ^ 2 + 3 * D ^ 2 := h6 ▸ dvd_mul_right x z,

  have h7 : C ^ 2 + 3 * D ^ 2 ≠ 0,
  { contrapose! hcoprime with H,
    obtain ⟨rfl, rfl⟩ := nat.sq_plus_three_sq_eq_zero_iff.mp H,
    rw [zero_mul, int.nat_abs_eq_zero] at HC HD,
    subst HC,
    subst HD,
    norm_num at h4 },
  have h8 : 0 < z,
  { rw pos_iff_ne_zero,
    rintro rfl,
    rw ←h6 at h7,
    norm_num at h7,
    exact h7 },
  obtain ⟨w, hwdvd, hwodd, hnform⟩ := factors' C D x z hodd h8 h6 (by { push_neg, exact IH }),
  refine ⟨w, _, C, D, HCDcoprime, hwodd, _, _⟩,
  { calc w
        ≤ z : nat.le_of_dvd h8 hwdvd
    ... ≤ y : by { rw hz, exact nat.le_mul_of_pos_left (pow_pos hgpos 2) }
    ... < x : h3 },
  { exact dvd_trans hwdvd h6' },
  { push_neg at hnform,
    exact hnform },
end

lemma obscure
  (p q : ℕ)
  (hp : 0 < p) (hq : 0 < q)
  (hcoprime : nat.gcd p q = 1)
  (hparity : even p ↔ ¬even q)
  (hcube : ∃ r, p ^ 2 + 3 * q ^ 2 = r ^ 3) :
  ∃ a b,
    0 < b ∧
    3 * b < a ∧
    p = a ^ 3 - 9 * a * b ^ 2 ∧
    q = 3 * a ^ 2 * b - 3 * b ^ 3 ∧
    nat.gcd a b = 1 ∧
    (even a ↔ ¬even b) :=
begin
  -- (1)
  obtain ⟨u, hu⟩ := hcube,

  -- (2)
  have hodd : ¬even u,
  { rw [←nat.even_pow' three_ne_zero, ←hu],
    simp [three_ne_zero, two_ne_zero, hparity] with parity_simps },
  
  -- (3)
  have hfactor : u ∣ p ^ 2 + 3 * q ^ 2,
  { rw hu,
    exact dvd_pow (dvd_refl u) three_ne_zero },
  obtain ⟨a, b, rfl⟩ := factors p q u hcoprime hodd hfactor,

  -- (4-7)
  have : (p ^ 2 + 3 * q ^ 2 : ℤ) = (a ^ 3 - 9 * a * b ^ 2) ^ 2 + 3 * (3 * a ^ 2 * b - 3 * b ^ 3) ^ 2,
  { zify at hu,
    rw [hu],
    ring },

  have hb : 0 < b := sorry,
  have hab : 3 * b < a := sorry,
  have hp' : p = a ^ 3 - 9 * a * b ^ 2 := sorry,
  have hq' : q = 3 * a ^ 2 * b - 3 * b ^ 3 := sorry,
  have haaa : 9 * a * b ^ 2 ≤ a ^ 3,
  { rw [pow_succ a, mul_comm 9, mul_assoc],
    apply nat.mul_le_mul_left,
    have : 9 * b ^ 2 = (3 * b) ^ 2,
    { rw mul_pow, norm_num },
    rw this,
    exact nat.pow_le_pow_of_le_left (le_of_lt hab) _ },
  have hbbb : 3 * b ^ 3 ≤ 3 * a ^ 2 * b,
  { rw [mul_assoc],
    apply nat.mul_le_mul_left,
    rw [pow_succ'],
    apply nat.mul_le_mul_right,
    apply nat.pow_le_pow_of_le_left,
    apply le_trans _ (le_of_lt hab),
    apply nat.le_mul_of_pos_left,
    norm_num },

  refine ⟨a, b, hb, hab, hp', hq', _, _⟩,
  { apply nat.coprime_of_dvd',
    intros k hkprime hkdvdleft hkdvdright,
    rw ←hcoprime,
    apply nat.dvd_gcd,
    { rw hp',
      apply nat.dvd_sub',
      { exact dvd_pow hkdvdleft (by norm_num) },
      { rw [mul_comm 9, mul_assoc],
        exact dvd_mul_of_dvd_left hkdvdleft _ },
    },
    { rw hq',
      apply nat.dvd_sub',
      { exact dvd_mul_of_dvd_right hkdvdright _ },
      { apply dvd_mul_of_dvd_right,
        exact dvd_pow hkdvdright (by norm_num) },
     } },

/-
(8) Which means that we could define a,b such that:
p = a3 -9ab2.
q = 3a2b - 3b3.
gcd(a,b)=1 [since otherwise, any common factor would divide p and q].
-/
  -- (9)
  {
    by_cases haparity : even a; by_cases hbparity : even b,
    { exfalso,
      have : even p,
      { rw hp',
        simp [haaa, haparity, hbparity, three_ne_zero] with parity_simps },
      have : even q,
      { rw hq',
        simp [hbbb, haparity, hbparity, three_ne_zero] with parity_simps },
      tauto },
    { tauto },
    { tauto },
    { exfalso,
      have : even p,
      { rw hp',
        simp [haaa, haparity, hbparity, three_ne_zero] with parity_simps },
      have : even q,
      { rw hq',
        simp [hbbb, haparity, hbparity, three_ne_zero] with parity_simps },
      tauto } }
end

lemma cube_of_coprime (a b c s : ℕ)
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hcoprimeab : nat.coprime a b)
  (hcoprimeac : nat.coprime a c)
  (hcoprimebc : nat.coprime b c)
  (hs : a * b * c = s ^ 3) :
  ∃ A B C, 0 < A ∧ 0 < B ∧ 0 < C ∧ a = A ^ 3 ∧ b = B ^ 3 ∧ c = C ^ 3 :=
begin
  obtain ⟨A, HA⟩ : ∃ A, a = A ^ 3,
  { rw [mul_assoc] at hs,
    apply nat.eq_pow_of_mul_eq_pow ha _ _ hs,
    { exact nat.mul_pos hb hc },
    { rw nat.coprime_mul_iff_right,
      exact ⟨hcoprimeab, hcoprimeac⟩ } },
  obtain ⟨B, HB⟩ : ∃ B, b = B ^ 3,
  { rw [mul_comm a b, mul_assoc] at hs,
    apply nat.eq_pow_of_mul_eq_pow hb _ _ hs,
    { exact nat.mul_pos ha hc },
    { rw nat.coprime_mul_iff_right,
      exact ⟨hcoprimeab.symm, hcoprimebc⟩ } },
  obtain ⟨C, HC⟩ : ∃ C, c = C ^ 3,
  { rw [mul_comm] at hs,
    apply nat.eq_pow_of_mul_eq_pow hc _ _ hs,
    { exact nat.mul_pos ha hb },
    { rw nat.coprime_mul_iff_right,
      exact ⟨hcoprimeac.symm, hcoprimebc.symm⟩ } },
  refine ⟨A, B, C, _, _, _, HA, HB, HC⟩,
  all_goals {
    rw [nat.pos_pow_iff zero_lt_three],
  },
  { rwa [←HA] },
  { rwa [←HB] },
  { rwa [←HC] },
end

lemma gcd1_coprime12 (u v : ℕ)
  (huvcoprime : u.gcd v = 1)
  (notdvd_2_2 : ¬2 ∣ u - 3 * v)
  (hccc : 2 * (u - 3 * v) ≤ 2 * u)
  (hbbb : 2 * 3 * v = 2 * u - 2 * (u - 3 * v))
  (not_3_dvd_2 : ¬3 ∣ u - 3 * v) :
  (2 * u).coprime (u - 3 * v) :=
begin
  apply nat.coprime_of_dvd',
  intros k hkprime hkdvdleft hkdvdright,
  have kne2 : k ≠ 2,
  { rintro rfl, exact notdvd_2_2 hkdvdright },
  have kne3 : k ≠ 3,
  { rintro rfl, exact not_3_dvd_2 hkdvdright },
  have kdvdu : k ∣ u := dvd_mul_cancel_prime hkdvdleft kne2 nat.prime_two hkprime,
  have kdvdv : k ∣ v,
  { apply dvd_mul_cancel_prime _ kne3 nat.prime_three hkprime,
    apply dvd_mul_cancel_prime _ kne2 nat.prime_two hkprime,
    rw [←mul_assoc, hbbb],
    apply nat.dvd_sub' hkdvdleft,
    apply dvd_mul_of_dvd_right hkdvdright },
  have : k ∣ nat.gcd u v := nat.dvd_gcd kdvdu kdvdv,
  rwa huvcoprime at this
end

lemma gcd1_coprime13 (u v : ℕ)
  (huvcoprime : u.gcd v = 1)
  (this : ¬even (u + 3 * v))
  (not_3_dvd_2 : ¬3 ∣ u - 3 * v)
  (notdvd_3_3 : ¬3 ∣ u + 3 * v) :
  (2 * u).coprime (u + 3 * v) :=
begin
  apply nat.coprime_of_dvd',
  intros k hkprime hkdvdleft hkdvdright,
  have : k ≠ 2,
  { rintro rfl, contradiction },
  have : k ≠ 3,
  { rintro rfl, contradiction },
  have : k ∣ u := dvd_mul_cancel_prime hkdvdleft ‹_› nat.prime_two hkprime,
  have : k ∣ v,
  { have : 2 * u ≤ 2 * (u + 3 * v), linarith,
    apply dvd_mul_cancel_prime _ ‹_› nat.prime_three hkprime,
    apply dvd_mul_cancel_prime _ ‹_› nat.prime_two hkprime,
    have : 2 * (u + 3 * v) - 2 * u = 2 * (3 * v),
    { zify [this],
      ring },
    rw ←this,
    apply nat.dvd_sub' _ hkdvdleft,
    apply dvd_mul_of_dvd_right hkdvdright },
  have : k ∣ nat.gcd u v := nat.dvd_gcd ‹_› ‹_›,
  rwa huvcoprime at this,
end

lemma gcd1_coprime23 (u v : ℕ)
  (huvcoprime : u.gcd v = 1)
  (notdvd_2_2 : ¬2 ∣ u - 3 * v)
  (huadd_add_usub : 2 * u = u + 3 * v + (u - 3 * v))
  (huadd_sub_usub : 2 * 3 * v = u + 3 * v - (u - 3 * v))
  (notdvd_3_3 : ¬3 ∣ u + 3 * v) :
  (u - 3 * v).coprime (u + 3 * v) :=
begin
  apply nat.coprime_of_dvd',
  intros k hkprime hkdvdleft hkdvdright,
  have : k ≠ 2,
  { rintro rfl, contradiction },
  have : k ≠ 3,
  { rintro rfl, contradiction },
  have : k ∣ u,
  { refine dvd_mul_cancel_prime _ ‹_› nat.prime_two hkprime,
    rw huadd_add_usub,
    apply nat.dvd_add hkdvdright hkdvdleft },
  have : k ∣ v,
  { apply dvd_mul_cancel_prime _ ‹_› nat.prime_three hkprime,
    apply dvd_mul_cancel_prime _ ‹_› nat.prime_two hkprime,
    rw [←mul_assoc, huadd_sub_usub],
    apply nat.dvd_sub'; assumption },
  have : k ∣ nat.gcd u v := nat.dvd_gcd ‹_› ‹_›,
  rwa huvcoprime at this
end

lemma descent_gcd1 (a b c p q : ℕ)
  (hp : 0 < p)
  (hq : 0 < q)
  (hcoprime : p.gcd q = 1)
  (hodd : even p ↔ ¬even q)
  (hcube : 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
             2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
  (h : flt_coprime a b c 3)
  (hgcd : (2 * p).gcd (p ^ 2 + 3 * q ^ 2) = 1) :
  ∃ (a' b' c' : ℕ),
    0 < a' ∧ 0 < b' ∧ 0 < c' ∧
    a' ^ 3 * b' ^ 3 * c' ^ 3 ≤ 2 * p ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 2.
  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  -- 5.
  obtain ⟨r, hr⟩ : ∃ r, 2 * p * (p ^ 2 + 3 * q ^ 2) = r ^ 3,
  { rcases hcube with (_|_|_);
    [use a, use b, use c];
    exact hcube },
  have hposleft : 0 < 2 * p := nat.mul_pos zero_lt_two hp,
  have hposright : 0 < p ^ 2 + 3 * q ^ 2 := nat.add_pos_left (pow_pos hp 2) _,
  have hcubeleft : ∃ s, 2 * p = s ^ 3 := nat.eq_pow_of_mul_eq_pow hposleft hposright hgcd hr,
  have hcuberight : ∃ t, p ^ 2 + 3 * q ^ 2 = t ^ 3,
  { rw mul_comm at hr,
    rw nat.gcd_comm at hgcd,
    exact nat.eq_pow_of_mul_eq_pow hposright hposleft hgcd hr },
  obtain ⟨u, v, -, huv, hp, hq, huvcoprime, huvodd⟩ : ∃ u v,
    0 < v ∧
    3 * v < u ∧
    p = u ^ 3 - 9 * u * v ^ 2 ∧
    q = 3 * u ^ 2 * v - 3 * v ^ 3 ∧
    nat.gcd u v = 1 ∧
    (even u ↔ ¬even v) := obscure p q hp hq hcoprime hodd hcuberight,
  have upos : 0 < u := lt_of_le_of_lt (nat.zero_le _) huv,
  have hpfactor,
  { have : 9 * v ^ 2 = (3 * v) ^ 2,
    { zify, ring },
    have,
    calc u ^ 2 - 9 * v ^ 2
        = u ^ 2 - (3 * v) ^ 2 : by rw this
    ... = (u + 3 * v) * (u - 3 * v) : nat.pow_two_sub_pow_two _ _
    ... = (u - 3 * v) * (u + 3 * v) : mul_comm _ _,
    calc p
        = (u ^ 3 - 9 * u * v ^ 2) : by rw hp
    ... = (u * u ^ 2 - u * (9 * v ^ 2)) : by ring
    ... = (u * (u ^ 2 - 9 * v ^ 2)) : by rw ←nat.mul_sub_left_distrib
    ... = u * ((u - 3 * v) * (u + 3 * v)) : by rw this
    ... = u * (u - 3 * v) * (u + 3 * v) : by rw mul_assoc u _ _ },
  have,
  calc 2 * p
      = 2 * (u * (u - 3 * v) * (u + 3 * v)) : by rw hpfactor
  ... = (2 * u) * (u - 3 * v) * (u + 3 * v) : by ring,
  have : ¬even (u - 3 * v),
  { simp [le_of_lt ‹ 3 * v < u›, huvodd] with parity_simps },
  have : ¬even (u + 3 * v),
  { simp [huvodd] with parity_simps },
  have husub_le_uadd : (u - 3 * v) ≤ (u + 3 * v),
  { transitivity u,
    exact nat.sub_le u (3 * v),
    exact nat.le.intro rfl },
  have notdvd_2_2 : ¬(2 ∣ u - 3 * v),
  { exact ‹¬even (u - 3 * v)› },
  have huadd_add_usub : 2 * u = (u + 3 * v) + (u - 3 * v),
  { zify [(le_of_lt huv)],
    ring },
  have huadd_sub_usub : 2 * 3 * v = (u + 3 * v) - (u - 3 * v),
  { zify [(le_of_lt huv), husub_le_uadd],
    ring },
  have hccc : 2 * (u - 3 * v) ≤ 2 * u := nat.mul_le_mul (le_refl _) (nat.sub_le _ _),
  have hbbb : 2 * 3 * v = 2 * u - 2 * (u - 3 * v),
  { zify [(le_of_lt huv), husub_le_uadd, hccc],
    ring },
  have hddd : ¬(3 ∣ p),
  { intro H,
    have : 3 ∣ p ^ 2 + 3 * q ^ 2,
    { apply nat.dvd_add,
      { rw pow_two,
        apply dvd_mul_of_dvd_right H },
      { apply dvd_mul_right } },
    have : 3 ∣ 2 * p := dvd_mul_of_dvd_right H 2,
    have : 3 ∣ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) := nat.dvd_gcd ‹_› ‹_›,
    rw hgcd at this,
    have := nat.eq_one_of_dvd_one this,
    norm_num at this },
  have not_3_dvd_2 : ¬(3 ∣ (u - 3 * v)),
  { intro hd2,
    apply hddd,
    rw hpfactor,
    apply dvd_mul_of_dvd_left _,
    apply dvd_mul_of_dvd_right hd2 },
  have notdvd_3_3 : ¬(3 ∣ (u + 3 * v)),
  { intro hd3,
    apply hddd,
    rw hpfactor,
    apply dvd_mul_of_dvd_right hd3 },

  obtain ⟨s, hs⟩ := hcubeleft,
  obtain ⟨C, A, B, HCpos, HApos, HBpos, HC, HA, HB⟩ : ∃ X Y Z,
    0 < X ∧ 0 < Y ∧ 0 < Z ∧
    2 * u = X ^ 3 ∧ u - 3 * v = Y ^ 3 ∧ u + 3 * v = Z ^ 3,
  { apply cube_of_coprime,
    { exact nat.mul_pos zero_lt_two upos },
    { exact nat.sub_pos_of_lt huv },
    { exact nat.add_pos_left upos _ },
    { apply gcd1_coprime12 u v; assumption },
    { apply gcd1_coprime13 u v; assumption },
    { apply gcd1_coprime23 u v; assumption },
    { rw [←‹2 * p = _›, hs] } },

  refine ⟨A, B, C, HApos, HBpos, HCpos, _, _⟩,
  { rw [mul_comm, ←mul_assoc (C^3)],
    rw [←HA, ←HB, ←HC],
    rw ←‹2 * p = _› },
  { rw [←HA, ←HB, ←HC, add_comm, huadd_add_usub] },
end

lemma descent_gcd3 (a b c p q : ℕ)
  (hp : 0 < p)
  (hq : 0 < q)
  (hcoprime : p.gcd q = 1)
  (hodd : even p ↔ ¬even q)
  (hcube : 2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
             2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
               2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3)
  (h : flt_coprime a b c 3)
  (hgcd : (2 * p).gcd (p ^ 2 + 3 * q ^ 2) = 3) :
  ∃ (a' b' c' : ℕ),
    0 < a' ∧ 0 < b' ∧ 0 < c' ∧
    a' ^ 3 * b' ^ 3 * c' ^ 3 ≤ 2 * p ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  -- 1.
  have h3_dvd_p : 3 ∣ p,
  { apply dvd_mul_cancel_prime _ (by norm_num) nat.prime_two nat.prime_three,
    rw ← hgcd,
    apply nat.gcd_dvd_left },
  have h3_ndvd_q : ¬(3 ∣ q),
  { intro H,
    apply nat.prime.not_dvd_one nat.prime_three,
    conv_rhs { rw ←hcoprime },
    exact nat.dvd_gcd h3_dvd_p H },
  -- 2.
  obtain ⟨s, hs⟩ := h3_dvd_p,
  have hspos : 0 < s,
  { linarith },
  have hps : 2 * p * (p ^ 2 + 3 * q ^ 2) = 3 ^ 2 * 2 * s * (q ^ 2 + 3 * s ^ 2),
  calc 2 * p * (p ^ 2 + 3 * q ^ 2)
      = 2 * (3 * s) * ((3 * s) ^ 2 + 3 * q ^ 2) : by rw hs
  ... = _ : by ring,
  -- 3.
  have hcoprime' : nat.coprime s q,
  { apply nat.coprime_of_dvd',
    intros k hkprime hkdvdleft hkdvdright,
    have hkdvdp : k ∣ p,
    { rw hs,
      exact dvd_mul_of_dvd_right hkdvdleft 3 },
    rw ←hcoprime,
    exact nat.dvd_gcd hkdvdp hkdvdright },
  
  have hodd' : even q ↔ ¬even s,
  { have : even p ↔ even s,
    { simp [hs] with parity_simps },
    rw this at hodd,
    tauto },
  have hcoprime'' : nat.coprime (3^2 * 2 * s) (q ^ 2 + 3 * s ^ 2),
  { have : ¬(2 ∣ (q ^ 2 + 3 * s ^ 2)),
    { change ¬(even _),
      simp [hs, two_ne_zero, hodd'] with parity_simps },

    have : ¬(3 ∣ (q ^ 2 + 3 * s ^ 2)),
    { intro H,
      apply h3_ndvd_q,
      rw ←nat.dvd_add_iff_left (dvd_mul_right _ _) at H,
      exact nat.prime.dvd_of_dvd_pow nat.prime_three H },

    apply nat.coprime_of_dvd',
    intros k hkprime hkdvdleft hkdvdright,
    rw ←hcoprime'.gcd_eq_one,
    have hkne2 : k ≠ 2,
    { rintro rfl, contradiction },
    have hkne3 : k ≠ 3,
    { rintro rfl, contradiction },
    have : k ∣ s,
    { apply dvd_mul_cancel_prime _ ‹_› nat.prime_two hkprime,
      apply dvd_mul_cancel_prime _ ‹_› nat.prime_three hkprime,
      apply dvd_mul_cancel_prime _ ‹_› nat.prime_three hkprime,
      convert hkdvdleft using 1,
      ring },
    have : k ∣ q,
    { have : k ∣ 3 * s ^ 2 := dvd_mul_of_dvd_right (dvd_pow this two_ne_zero) _,
      rw ←nat.dvd_add_iff_left this at hkdvdright,
      exact hkprime.dvd_of_dvd_pow hkdvdright },
    exact nat.dvd_gcd ‹_› ‹_›,
  },
  -- 4.
  obtain ⟨r, hr⟩ : ∃ r, 2 * p * (p ^ 2 + 3 * q ^ 2) = r ^ 3,
  { rcases hcube with (_|_|_);
    [use a, use b, use c];
    exact hcube },
  have : 0 < 3 ^ 2 * 2 * s,
  { linarith },
  have : 0 < q ^ 2 + 3 * s ^ 2,
  { apply nat.add_pos_right,
    apply nat.mul_pos (by norm_num : 0 < 3) (pow_pos hspos _) },
  have hcubeleft : ∃ e, 3 ^ 2 * 2 * s = e ^ 3,
  { rw hps at hr,
    exact nat.eq_pow_of_mul_eq_pow ‹_› ‹_› hcoprime'' hr },
  have hcuberight : ∃ f, q ^ 2 + 3 * s ^ 2 = f ^ 3,
  { rw [hps, mul_comm] at hr,
    exact nat.eq_pow_of_mul_eq_pow ‹_› ‹_› hcoprime''.symm hr },

  -- 5.
  obtain ⟨u, v, hv, huv, hp, hq, huvcoprime, huvodd⟩ : ∃ u v,
    0 < v ∧
    3 * v < u ∧
    q = u ^ 3 - 9 * u * v ^ 2 ∧
    s = 3 * u ^ 2 * v - 3 * v ^ 3 ∧
    nat.gcd u v = 1 ∧
    (even u ↔ ¬even v) := obscure q s hq hspos hcoprime'.symm hodd' hcuberight,
  have hu : 0 < u := lt_of_le_of_lt (nat.zero_le _) huv,
  have huv' : v < u,
  { apply lt_of_le_of_lt _ huv,
    apply nat.le_mul_of_pos_left,
    norm_num },
  have huv'' : v ^ 3 < u ^ 2 * v,
  { rwa [pow_succ, mul_comm, mul_lt_mul_right hv, nat.pow_lt_iff_lt_left one_le_two] },
  have huv''' : 3 * v ^ 3 < 3 * u ^ 2 * v,
  { rwa [mul_assoc, mul_lt_mul_left (by norm_num : 0 < 3)] },
  have huv'''' : u - v ≤ u + v,
  { transitivity u,
    exact nat.sub_le u v,
    exact nat.le.intro rfl },

  -- 6.
  have haddodd : ¬even (u + v),
  { simp [huvodd] with parity_simps },
  have hsubodd : ¬even (u - v),
  { simp [huvodd, le_of_lt huv'] with parity_simps },

  have haddcoprime : nat.coprime (u + v) (2 * v),
  { apply nat.coprime_of_dvd',
    intros k hkprime hkdvdleft hkdvdright,
    have hkne2 : k ≠ 2,
    { rintro rfl, contradiction },
    have hkdvdright' : k ∣ v := dvd_mul_cancel_prime hkdvdright hkne2 nat.prime_two hkprime,
    rw [←huvcoprime],
    apply nat.dvd_gcd _ hkdvdright',
    rw [←nat.add_sub_cancel u v],
    exact nat.dvd_sub' hkdvdleft hkdvdright' },
  have hsubcoprime : nat.coprime (u - v) (2 * v),
  { apply nat.coprime_of_dvd',
    intros k hkprime hkdvdleft hkdvdright,
    have hkne2 : k ≠ 2,
    { rintro rfl, contradiction },
    have hkdvdright' : k ∣ v := dvd_mul_cancel_prime hkdvdright hkne2 nat.prime_two hkprime,
    rw [←huvcoprime],
    apply nat.dvd_gcd _ hkdvdright',
    rw [←nat.sub_add_cancel (le_of_lt huv')],
    exact nat.dvd_add hkdvdleft hkdvdright' },
  have haddsubcoprime : nat.coprime (u + v) (u - v),
  { apply nat.coprime_of_dvd',
    intros k hkprime hkdvdleft hkdvdright,
    rw [←huvcoprime],
    have hkne2 : k ≠ 2,
    { rintro rfl,
      exact haddodd hkdvdleft },
    apply nat.dvd_gcd,
    { apply dvd_mul_cancel_prime _ hkne2 nat.prime_two hkprime,
      have : 2 * u = (u + v) + (u - v),
      { zify [le_of_lt huv'], ring },
      rw this,
      exact dvd_add hkdvdleft hkdvdright },
    { apply dvd_mul_cancel_prime _ hkne2 nat.prime_two hkprime,
      have : 2 * v = (u + v) - (u - v),
      { zify [le_of_lt huv', huv''''], ring },
      rw this,
      exact nat.dvd_sub' hkdvdleft hkdvdright } },

  -- 7.
  obtain ⟨t, ht⟩ : ∃ t, 2 * v * (u - v) * (u + v) = t ^ 3,
  {
    obtain ⟨e, he⟩ := hcubeleft,
    obtain ⟨f, hf⟩ := hcuberight,
    have hxxx : 3 ^ 3 * (2 * (u ^ 2 * v - v ^ 3)) = e ^ 3,
    { rw [←he, hq, mul_assoc 3, ←nat.mul_sub_left_distrib],
      ring },
    have : 3 ∣ e,
    { rw ←nat.pow_dvd_pow_iff (by norm_num : 0 < 3),
      rw ←hxxx,
      exact dvd_mul_right _ _ },
    have : (e / 3) ^ 3 = e ^ 3 / 3 ^ 3 := div_pow' _ _ _ this,
    use e / 3,
    symmetry,
    calc (e / 3) ^ 3
        = e ^ 3 / 3 ^ 3 : this
    ... = (3 ^ 3 * (2 * (u ^ 2 * v - v ^ 3))) / 3 ^ 3 : by rw hxxx
    ... = ((2 * (u ^ 2 * v - v ^ 3)) * 3 ^ 3) / 3 ^ 3 : by rw mul_comm
    ... = 2 * (u ^ 2 * v - v ^ 3) : nat.mul_div_cancel _ (by norm_num : 0 < 3 ^ 3)
    ... = 2 * v * (u ^ 2 - v ^ 2) : by rw [mul_assoc, mul_comm v, nat.mul_sub_right_distrib, pow_succ' v]
    ... = 2 * v * (u - v) * (u + v) : by { rw nat.pow_two_sub_pow_two, ring }
  },
  obtain ⟨A, B, C, HApos, HBpos, HCpos, HA, HB, HC⟩ : ∃ X Y Z,
    0 < X ∧ 0 < Y ∧ 0 < Z ∧
    2 * v = X ^ 3 ∧ u - v = Y ^ 3 ∧ u + v = Z ^ 3,
  { apply cube_of_coprime,
    { exact nat.mul_pos zero_lt_two hv },
    { exact nat.sub_pos_of_lt huv' },
    { exact nat.add_pos_left hu _ },
    { exact hsubcoprime.symm },
    { exact haddcoprime.symm },
    { exact haddsubcoprime.symm },
    { exact ht } },

  refine ⟨A, B, C, HApos, HBpos, HCpos, _, _⟩,

  -- 9.
  { apply le_of_lt,
    calc A ^ 3 * B ^ 3 * C ^ 3
        = 2 * v * (u - v) * (u + v) : by rw [←HA, ←HB, ←HC]
    ... = 2 * (v * (u - v) * (u + v)) : by ring
    ... ≤ 3 * (v * (u - v) * (u + v)) : nat.mul_le_mul_right _ (by norm_num)
    ... = s : by {rw [hq], zify [le_of_lt huv', le_of_lt huv'''], ring }
    ... < 3 * s : by linarith
    ... = p : hs.symm
    ... < 2 * p : by linarith },

  -- 8.
  { calc A ^ 3 + B ^ 3
        = 2 * v + (u - v) : by rw [HA, HB]
    ... = u + v : by { zify [le_of_lt huv'], ring }
    ... = C ^ 3 : HC },
end

lemma descent
  (a b c : ℕ)
  (h : flt_coprime a b c 3) :
  ∃ a' b' c', 0 < a' ∧ 0 < b' ∧ 0 < c' ∧ (a' * b' * c' < a * b * c) ∧ a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 3.
  have := descent2 a b c h,
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube, haaa⟩ := this,

  suffices : ∃ a' b' c',
    0 < a' ∧ 0 < b' ∧ 0 < c' ∧
    a' ^ 3 * b' ^ 3 * c' ^ 3 ≤ 2 * p ∧
    a' ^ 3 + b' ^ 3 = c' ^ 3,
  { obtain ⟨a', b', c', ha', hb', hc', hsmaller, hsolution⟩ := this,
    refine ⟨a', b', c', ha', hb', hc', _, hsolution⟩,
    rw ←nat.pow_lt_iff_lt_left (by norm_num : 1 ≤ 3),
    iterate 4 {rw mul_pow},
    exact lt_of_le_of_lt hsmaller haaa },

  -- 4.
  cases gcd1or3 p q hp hq hcoprime hodd with hgcd hgcd,
  -- 5.
  { apply descent_gcd1 a b c p q hp hq hcoprime hodd hcube h hgcd },
  { apply descent_gcd3 a b c p q hp hq hcoprime hodd hcube h hgcd },
end

lemma flt_three
  (a b c : ℤ)
  (ha : a ≠ 0)
  (hb : b ≠ 0)
  (hc : c ≠ 0) :
  a ^ 3 + b ^ 3 ≠ c ^ 3 :=
begin
  suffices h : ∀ (k : ℕ) (a b c : ℤ), k = (a * b * c).nat_abs → a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 3 + b ^ 3 ≠ c ^ 3,
  { exact h (a * b * c).nat_abs a b c rfl ha hb hc },
  intro k,
  refine nat.strong_induction_on k _,
  intros k' IH x y z hk hpos H,
  obtain ⟨x'', y'', z'', hxle, hyle, hzle, hcoprime⟩ := exists_coprime x y z 3 hpos (by norm_num) H,
  obtain ⟨x', y', z', hx'pos, hy'pos, hz'pos, hsmaller, hsolution⟩ := descent x'' y'' z'' hcoprime,
  refine IH (x' * y' * z') _ _ _ _ rfl ⟨hx'pos, hy'pos, hz'pos⟩ hsolution,
  apply lt_of_lt_of_le hsmaller,
  rw hk,
  apply nat.mul_le_mul _ hzle,
  apply nat.mul_le_mul hxle hyle,
end
