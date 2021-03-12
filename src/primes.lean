import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import ring_theory.coprime
import ring_theory.int.basic
import tactic

section

variables {α : Type*} [ordered_semiring α] [nontrivial α] {a b c d : α}

@[field_simps] lemma three_ne_zero : (3:α) ≠ 0 :=
zero_lt_three.ne.symm

@[field_simps] lemma four_ne_zero : (4:α) ≠ 0 :=
zero_lt_four.ne.symm

end

lemma nat.mem_factors' {n p} (hn : 0 < n) : p ∈ nat.factors n ↔ nat.prime p ∧ p ∣ n :=
⟨λ h, ⟨nat.mem_factors h, (nat.mem_factors_iff_dvd hn (nat.mem_factors h)).mp h⟩,
 λ ⟨hprime, hdvd⟩, (nat.mem_factors_iff_dvd hn hprime).mpr hdvd⟩

lemma eq_pow
  {n p : ℕ}
  (hpos : 0 < n)
  (h : ∀ {d}, nat.prime d → d ∣ n → d = p) :
  n = p ^ n.factors.length :=
begin
  set k := n.factors.length,
  rw [←nat.prod_factors hpos],
  transitivity,
  {
    suffices : n.factors = list.repeat p k, { rw this },
    apply list.eq_repeat_of_mem,
    intros d hd,
    rw nat.mem_factors' hpos at hd,
    apply h hd.left hd.right,
  },
  { exact list.prod_repeat p k },
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
  {n : ℕ} (n2 : 2 ≤ n) : (∃ k : ℕ, n = 2 ^ k) ∨ ∃ p, nat.prime p ∧ p ∣ n ∧ odd p :=
begin
  rw or_iff_not_imp_right,
  intro H,
  push_neg at H,
  use n.factors.length,
  apply eq_pow,
  linarith,
  intros p hprime hdvd,
  apply hprime.eq_two_or_odd.resolve_right,
  rw ←nat.odd_iff,
  exact H p hprime hdvd,
end

lemma exists_prime_and_dvd'
  {n : ℕ} (n2 : 2 < n) : ∃ p, p ∣ n ∧ (p = 4 ∨ (nat.prime p ∧ p % 2 = 1)) :=
begin
  obtain ⟨k, h2⟩|⟨p, hp, hdvd, hodd⟩ := exists_odd_prime_and_dvd_or_two_pow n2.le,
  { refine ⟨4, _, _⟩,
    { use 2 ^ (k - 2),

      have h3 : 2 ≤ k,
      { rw h2 at n2,
        apply l0 n2 },

      calc n
          = 2 ^ k : h2
      ... = 2 ^ 2 * 2 ^ (k - 2) : (pow_mul_pow_sub _ h3).symm
      ... = 4 * 2 ^ (k - 2) : by norm_num },
    { left, refl } },
  { rw nat.odd_iff at hodd,
    have pnetwo : p ≠ 2,
    { rintro rfl,
      norm_num at hodd },
    exact ⟨p, hdvd, or.inr ⟨hp, hodd⟩⟩ },
end

theorem nat.eq_pow_of_mul_eq_pow {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
  (hab : nat.coprime a b) {k : ℕ} (h : a * b = c ^ k) : ∃ d, a = d ^ k :=
begin
  have ha' : associates.mk a ≠ 0,
  { intro H,
    rw [associates.mk_eq_zero] at H,
    exact ha.ne.symm H },
  have hb' : associates.mk b ≠ 0,
  { intro H,
    rw [associates.mk_eq_zero] at H,
    exact hb.ne.symm H },
  have hab' : ∀ (d : associates ℕ), d ∣ associates.mk a → d ∣ associates.mk b → ¬prime d,
  { intros d da db dprime,
    obtain ⟨d', rfl⟩ := associates.exists_rep d,
    rw associates.mk_dvd_mk at da db,
    rw [associates.prime_mk, ←nat.prime_iff_prime] at dprime,
    exact nat.not_coprime_of_dvd_of_dvd dprime.one_lt da db hab },
  have h' : associates.mk a * associates.mk b = (associates.mk c) ^ k,
  { rw [associates.mk_mul_mk, ←associates.mk_pow, h] },
  obtain ⟨d, hd⟩ := associates.eq_pow_of_mul_eq_pow ha' hb' hab' h',
  obtain ⟨d', rfl⟩ := associates.exists_rep d,
  use d',
  rw [←associated_iff_eq, ←associates.mk_eq_mk_iff_associated, hd, associates.mk_pow],
end

lemma dvd_mul_cancel_prime {p n k : ℕ}
  (h : k ∣ p * n)
  (hne : k ≠ p)
  (hp : nat.prime p)
  (hk : nat.prime k) : k ∣ n :=
begin
  rw hk.dvd_mul at h,
  cases h,
  { exfalso,
    rw nat.prime_dvd_prime_iff_eq hk hp at h,
    contradiction },
  { assumption },
end

lemma nat.even_pow' {m n : nat} (h : n ≠ 0) : even (m^n) ↔ even m :=
begin
  rw [nat.even_pow], tauto,
end

lemma int.even_pow' {m : ℤ} {n : ℕ} (h : n ≠ 0) : even (m^n) ↔ even m :=
begin
  rw [int.even_pow], tauto,
end

lemma gcd_eq_of_dvd
  (p q g : ℕ)
  (hp' : g ∣ p) (hq' : g ∣ q)
  (h : ∀ x, x ∣ p → x ∣ q → x ∣ g)
  : nat.gcd p q = g :=
begin
  apply nat.dvd_antisymm,
  { apply h,
    exact nat.gcd_dvd_left p q,
    exact nat.gcd_dvd_right p q},
  exact nat.dvd_gcd hp' hq',
end

lemma nat.pos_pow_iff {b n : ℕ} (h : 0 < n) : 0 < b ↔ 0 < b ^ n :=
begin
  rw [pos_iff_ne_zero, pos_iff_ne_zero, ne.def, ne.def, not_congr],
  apply (pow_eq_zero_iff h).symm,
  apply_instance,
end

theorem pos_pow_of_pos {b : ℕ} (n : ℕ) (h : 0 < b) : 0 < b^n := pow_pos h n

/-
theorem not_coprime_of_dvd_gcd {m n d : ℕ} (dgt1 : 1 < d) (H : d ∣ nat.gcd m n) :
  ¬ nat.coprime m n :=
λ (co : nat.gcd m n = 1),
not_lt_of_ge (nat.le_of_dvd zero_lt_one $ by rw ←co; exact H) dgt1
-/

theorem int.nat_abs_ne_zero {a : ℤ} : a.nat_abs ≠ 0 ↔ a ≠ 0 := not_congr int.nat_abs_eq_zero

-- Note eq_pow_two_mul_odd in archive/100-theorems-list/70_perfect_numbers.lean
lemma nat.split_factors
  {a b : ℕ}
  (a_pos : 0 < a)
  (one_lt_b : 1 < b) :
  ∃ k l : ℕ, a = b ^ k * l ∧ ¬(b ∣ l) :=
begin
  by_cases hdvd : b ∣ a,
  { revert a_pos hdvd,
    apply nat.strong_induction_on a,
    intros a' IH a'_pos hdvd,
    obtain ⟨c, hc⟩ := hdvd,
    have c_pos : 0 < c,
    { rw pos_iff_ne_zero,
      rintro rfl,
      rw mul_zero at hc,
      subst hc,
      exact lt_irrefl _ a'_pos },
    have hsmaller : c < a',
    { rw [hc, lt_mul_iff_one_lt_left c_pos],
      exact one_lt_b },
    by_cases H : b ∣ c,
    { obtain ⟨k', l', heqb, hnotdvd⟩ := IH c hsmaller c_pos H,
      refine ⟨k' + 1, l', _, hnotdvd⟩,
      rw [hc, heqb, pow_succ, mul_assoc] },
    { refine ⟨1, c, _, H⟩,
      rwa pow_one } },
  { refine ⟨0, a, _, hdvd⟩,
    rwa [pow_zero, one_mul] }
end

lemma nat.dvd_sub_of_mod_eq {a b c : ℕ} (h : a % b = c) : b ∣ a - c :=
begin
  have : c ≤ a,
  { rw ←h, exact nat.mod_le a b },
  rw [←int.coe_nat_dvd, int.coe_nat_sub this],
  apply int.dvd_sub_of_mod_eq,
  rw ←int.coe_nat_mod, rw h,
end

theorem nat.one_le_of_not_even {n : ℕ} (h : ¬even n) : 1 ≤ n :=
begin
  apply nat.succ_le_of_lt,
  rw pos_iff_ne_zero,
  rintro rfl,
  exact h nat.even_zero
end

lemma two_mul_add_one_iff_not_odd (n : ℕ) : ¬even n ↔ ∃ m, n = 2 * m + 1 :=
begin
  rw ←nat.odd_iff_not_even,
  refl,
end

lemma mod_four_of_odd {n : nat} (hodd: ¬even n) : ∃ m, n = 4 * m - 1 ∨ n = 4 * m + 1 :=
begin
  rw two_mul_add_one_iff_not_odd at hodd,
  obtain ⟨m, hm⟩ := hodd,
  by_cases even m,
  { obtain ⟨k, hk⟩ := h,
    use k,
    right,
    rw [hm, hk, ←mul_assoc],
    norm_num },
  { rw two_mul_add_one_iff_not_odd at h,
    obtain ⟨k, hk⟩ := h,
    use k + 1,
    left,
    rw [hm, hk],
    ring }
end

lemma mod_four_of_odd' {n : nat} (hodd: ¬even n) : ∃ m, n = 4 * m + 3 ∨ n = 4 * m + 1 :=
begin
  rw two_mul_add_one_iff_not_odd at hodd,
  obtain ⟨m, hm⟩ := hodd,
  by_cases even m,
  { obtain ⟨k, hk⟩ := h,
    use k,
    right,
    rw [hm, hk, ←mul_assoc],
    norm_num },
  { rw two_mul_add_one_iff_not_odd at h,
    obtain ⟨k, hk⟩ := h,
    use k,
    left,
    rw [hm, hk],
    ring, }
end

lemma int.mod_four_of_odd' {n : ℤ} (hodd: odd n) : ∃ m, n = 4 * m + 3 ∨ n = 4 * m + 1 :=
begin
  obtain ⟨m, hm⟩ := hodd,
  cases int.even_or_odd m with h h;
    obtain ⟨k, hk⟩ := h;
    use k;
    [right, left];
    rw [hm, hk];
    ring,
end

lemma int.four_dvd_add_or_sub_of_odd {a b : ℤ}
  (ha : odd a)
  (hb : odd b) :
  4 ∣ a + b ∨ 4 ∣ a - b :=
begin
  obtain ⟨m, hm⟩ := int.mod_four_of_odd' ha,
  obtain ⟨n, hn⟩ := int.mod_four_of_odd' hb,
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
    apply dvd_refl },
end

@[norm_cast]
lemma int.coe_nat_even {n : ℕ} : even (n : ℤ) ↔ even n :=
by { rw [int.even_iff, nat.even_iff], norm_cast }

@[norm_cast]
lemma int.coe_nat_odd {n : ℕ} : odd (n : ℤ) ↔ odd n :=
by { rw [int.odd_iff, nat.odd_iff], norm_cast }

lemma int.nat_abs_even {n : ℤ} : even n.nat_abs ↔ even n :=
begin
  by_cases hsign : 0 ≤ n,
  { convert int.coe_nat_even.symm,
    exact (int.nat_abs_of_nonneg hsign).symm },
  { rw [←int.coe_nat_even, int.of_nat_nat_abs_of_nonpos (le_of_not_le hsign), int.even_neg] },
end

lemma int.nat_abs_odd {n : ℤ} : odd n.nat_abs ↔ odd n :=
by rw [int.odd_iff_not_even, nat.odd_iff_not_even, int.nat_abs_even]

theorem nat.pow_two_sub_pow_two (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
by { simp only [pow_two], exact nat.mul_self_sub_mul_self_eq a b }

lemma div_pow' (n m k : nat) (h : m ∣ n) : (n / m) ^ k = (n ^ k) / (m ^ k) :=
begin
  by_cases H : m = 0,
  { subst H,
    by_cases G : k = 0,
    { subst G,
      rw [pow_zero, pow_zero, pow_zero, nat.div_one] },
    rw [←ne.def, ←pos_iff_ne_zero] at G,
    rw [zero_pow G, nat.div_zero, nat.div_zero, zero_pow G], },
  rw [←ne.def, ←pos_iff_ne_zero] at H,
  obtain ⟨d, hd⟩ := h,
  rw hd,
  rw mul_comm,
  rw mul_pow,
  rw nat.mul_div_cancel _ H,
  rw nat.mul_div_cancel _ (pow_pos H k),
end.

lemma int.div_pow {n m : int} (h : m ∣ n) (k : nat) : (n / m) ^ k = (n ^ k) / (m ^ k) :=
begin
  by_cases H : m = 0,
  { subst H,
    by_cases G : k = 0,
    { subst G,
      rw [pow_zero, pow_zero, pow_zero, int.div_one] },
    rw [←ne.def, ←pos_iff_ne_zero] at G,
    rw [zero_pow G, int.div_zero, int.div_zero, zero_pow G], },
  obtain ⟨d, hd⟩ := h,
  rw hd,
  rw mul_comm,
  rw mul_pow,
  rw int.mul_div_cancel _ H,
  rw int.mul_div_cancel _ (pow_ne_zero _ H),
end.

theorem nat.coprime.pow' {k l : ℕ} (m n : ℕ)
 (hm : m ≠ 0)
 (hn : n ≠ 0)
 (h : k ≠ 0 ∨ l ≠ 0) (H1 : nat.coprime (k ^ m) (l ^ n)) : nat.coprime k l :=
begin
  unfold nat.coprime at *,
  contrapose! H1,
  rw ←ne.def at *,
  apply ne_of_gt,
  apply lt_of_lt_of_le,
  { apply lt_of_le_of_ne _ H1.symm,
    rw [nat.succ_le_iff, pos_iff_ne_zero],
    intro H,
    obtain ⟨rfl, rfl⟩ := nat.gcd_eq_zero_iff.mp H,
    rw [or_self] at h,
    contradiction },
  { apply nat.le_of_dvd,
    { contrapose! h,
      rw [nat.le_zero_iff, nat.gcd_eq_zero_iff] at h,
      obtain ⟨hk, hl⟩ := h,
      split; apply pow_eq_zero; assumption },
    { apply nat.dvd_gcd; refine dvd_trans _ (dvd_pow (dvd_refl _) _),
      { exact nat.gcd_dvd_left _ _ },
      { exact hm },
      { exact nat.gcd_dvd_right _ _ },
      { exact hn } } }
end

section
variables {R : Type*} [comm_semiring R] {x y z : R}
variables {m n : ℕ}

lemma not_coprime_zero_zero [nontrivial R] : ¬ is_coprime (0 : R) 0 :=
by simp only [add_zero, is_coprime, exists_false, zero_ne_one, mul_zero, not_false_iff]

theorem is_coprime.of_pow_left (hm : m ≠ 0) (H : is_coprime (x ^ m) y) : is_coprime x y :=
by {
  rw [← finset.card_range m, ← finset.prod_const] at H,
have := is_coprime.of_prod_left H 0,
apply this,
simp only [finset.mem_range],
rwa pos_iff_ne_zero,
}

theorem is_coprime.of_pow_right (hm : m ≠ 0) (H : is_coprime x (y ^ m)) : is_coprime x y :=
by {
  rw [← finset.card_range m, ← finset.prod_const] at H,
have := is_coprime.of_prod_right H 0,
apply this,
simp only [finset.mem_range],
rwa pos_iff_ne_zero,
}

theorem is_coprime.of_pow
 (hm : m ≠ 0)
 (hn : n ≠ 0)
 (H1 : is_coprime (x ^ m) (y ^ n)) : is_coprime x y :=
(H1.of_pow_left hm).of_pow_right hn

lemma int.coprime_add_self
  { x y : ℤ }
  (h : is_coprime x y) :
  is_coprime x (x + y) :=
  
begin
  apply @is_coprime.of_add_mul_right_right _ _ x (x +  y) (-1),
  convert h,
  ring,
end

end
section
variables {R : Type*} [comm_ring R] {x y z : R}
variables {m n : ℕ}
lemma coprime_add_self'
  (h : is_coprime x y) :
  is_coprime x (x + y) :=
begin
  apply @is_coprime.of_add_mul_right_right _ _ x (x +  y) (-1),
  convert h,
  ring,
end
lemma coprime_add_self''
  (h : is_coprime x y) :
  is_coprime x (x + y) :=
begin
  convert is_coprime.mul_add_left_right h 1,
  rw mul_one,
end

lemma coprime_add_self_pow
  {n : ℕ}
  (hn : 0 < n)
  (hsoln : x ^ n + y ^ n = z ^ n)
  (hxx : is_coprime x y)
   : is_coprime x z :=
begin
  have hn' := pos_iff_ne_zero.mp hn,
  apply is_coprime.of_pow hn' hn',
  rw ←hsoln,

  apply coprime_add_self',
  exact is_coprime.pow hxx,
end
end

lemma coprime_add_self
  (a b : ℕ)
  (h : nat.coprime a b) :
  nat.coprime a (a + b) :=
begin
  apply nat.coprime_of_dvd',
  rintros k - a_1 a_2,
  rw ←h.gcd_eq_one,
  apply nat.dvd_gcd a_1 _,
  rw [←nat.add_sub_cancel b a, add_comm],
  apply nat.dvd_sub _ a_2 a_1 ,
  apply nat.le_add_right
end

lemma nat.coprime_add_self_pow
  {a b c n : ℕ}
  (hn : 0 < n)
  (hsoln : (a) ^ n + (b) ^ n = (c) ^ n)
  (hxx : (a).coprime (b))
   : (a).coprime (c) :=
begin
  have hn' := pos_iff_ne_zero.mp hn,
  apply nat.coprime.pow' n n hn' hn',
  { contrapose! hxx,
    obtain ⟨rfl, rfl⟩ := hxx,
    rw [zero_pow hn, zero_add] at hsoln,
    obtain rfl := pow_eq_zero hsoln,
    norm_num },
  rw ←hsoln,
  apply coprime_add_self,
  exact nat.coprime.pow n n hxx
end

@[parity_simps]
lemma int.nat_abs.even (p : ℤ ) : even p.nat_abs ↔ even p := int.coe_nat_dvd_left.symm

lemma nat.lt_mul_left (a b : nat) (h : 1 < b) (h' : 0 < a): a < b * a :=
begin
  convert nat.mul_lt_mul h (le_refl _) h',
  rw one_mul
end

lemma int.nat_abs_square (a : ℤ) : (a.nat_abs ^ 2 : ℤ) = a ^ 2 :=
begin
  rw [pow_two, pow_two],
  exact int.nat_abs_mul_self' a
end

theorem nat.dvd_sub' {k m n : ℕ} (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
begin
  by_cases H : n ≤ m,
  { --rwa [nat.dvd_add_iff_left h₂, nat.sub_add_cancel H]
    exact nat.dvd_sub H h₁ h₂ },
  { rw not_le at H,
    rw nat.sub_eq_zero_of_le H.le,
    exact dvd_zero k },
end

lemma nat.le_mul_of_one_le_left (a : ℕ) {b : ℕ} (h : 1 ≤ b) : a ≤ b * a :=
begin
  convert nat.mul_le_mul_right a h,
  rw one_mul,
end

lemma int.div_ne_zero_of_dvd {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hadvd: b ∣ a) : a / b ≠ 0 :=
begin
  obtain ⟨c, rfl⟩ := hadvd,
  rw [mul_comm, int.mul_div_cancel _ hb],
  rintro rfl,
  rw mul_zero at ha,
  exact ha rfl,
end

lemma int.prime_iff (a : ℤ) : prime a ↔ nat.prime a.nat_abs :=
begin
  rw nat.prime_iff_prime_int,
  refine prime_iff_of_associated _,
  refine dvd_dvd_iff_associated.mp _,
  split,
  refine int.coe_nat_dvd_right.mpr _,
  exact dvd_refl (int.nat_abs a),


  refine int.nat_abs_dvd.mpr _,
  exact dvd_refl (a),
end

lemma int.factor_div (a: ℤ) (x : ℕ)
  (hodd : odd x)
  (h0' : 0 < x) :
  ∃ (m c : ℤ), c + m * x = a ∧ 2 * c.nat_abs < x :=
begin
  set c : ℤ := a % x with hc,
  have hcnonneg : 0 ≤ c := int.mod_nonneg _ (int.coe_nat_ne_zero_iff_pos.mpr h0'),
  have : c < x := int.mod_lt_of_pos a (int.coe_nat_lt.mpr h0'),
  by_cases H : 2 * c < x,
  { refine ⟨a/x, c, _, _⟩,
    { rw [mul_comm], exact int.mod_add_div a x },
    { zify, rwa [int.nat_abs_of_nonneg hcnonneg] } },
  { push_neg at H,
    set c' : ℤ := c - x with hc',
    refine ⟨a / x + 1, c', _, _⟩,
    { rw [add_mul, one_mul, hc'],
      conv_rhs { rw ←int.mod_add_div a x },
      ring },
    { zify at ⊢ H,
      rw [hc', ←int.nat_abs_neg, neg_sub, int.nat_abs_of_nonneg (sub_nonneg_of_le this.le),
        mul_sub, sub_lt_iff_lt_add, two_mul, add_lt_add_iff_left, hc],
      apply lt_of_le_of_ne H,
      rw [nat.odd_iff_not_even, ←int.even_coe_nat] at hodd,
      contrapose! hodd with heqtwomul,
      exact ⟨_,  heqtwomul⟩ } },
end

theorem int.coprime_div_gcd_div_gcd {m n : ℤ} (H : int.gcd m n ≠ 0) :
  is_coprime (m / int.gcd m n) (n / int.gcd m n) :=
by rw [←int.gcd_eq_one_iff_coprime, int.gcd_div (int.gcd_dvd_left m n) (int.gcd_dvd_right m n),
    int.nat_abs_of_nat, nat.div_self (nat.pos_of_ne_zero H)]

lemma int.gcd_ne_zero_iff {i j : ℤ} : int.gcd i j ≠ 0 ↔ i ≠ 0 ∨ j ≠ 0 :=
begin
  convert not_congr int.gcd_eq_zero_iff,
  rw not_and_distrib,
end

section
variables {R : Type*} [comm_semiring R]

lemma is_coprime.is_unit_of_dvd' {a b x : R} (h : is_coprime a b) (ha : x ∣ a) (hb : x ∣ b) :
is_unit x :=
begin
  rw is_unit_iff_dvd_one,
  obtain ⟨c, d, h1⟩ := h,
  rw ←h1,
  apply dvd_add; { apply dvd_mul_of_dvd_right, assumption },
end

lemma is_coprime.is_unit_of_dvd'' {a b x : R} (h : is_coprime a b) (ha : x ∣ a) (hb : x ∣ b) :
is_unit x :=
begin
  rw is_unit_iff_dvd_one,
  obtain ⟨c, d, h1⟩ := h,
  rw ←h1,
  apply dvd_add; { apply dvd_mul_of_dvd_right, assumption },
end

end

section
variables {R : Type*} [comm_ring R]

lemma is_coprime.neg_left {a b : R} (h : is_coprime a b) : is_coprime (-a) b :=
begin
  obtain ⟨x, y, h⟩ := h,
  use [-x, y],
  simpa only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg] using h,
end

lemma is_coprime.neg_right {a b : R} (h : is_coprime a b) : is_coprime a (-b) :=
begin
  obtain ⟨x, y, h⟩ := h,
  use [x, -y],
  simpa only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg] using h,
end

lemma is_coprime.neg_neg {a b : R} (h : is_coprime a b) : is_coprime (-a) (-b) :=
h.neg_left.neg_right

end
section
theorem is_unit_of_pow {α} [comm_monoid α] {x : α} {n : ℕ} (hn : 0 < n)
  (h : is_unit (x ^ n)) : is_unit x
:=
begin
  cases n,
  { norm_num at hn },
  { apply is_unit_of_mul_is_unit_left h }
end

theorem of_irreducible_pow {α} [comm_monoid α] {x : α} {n : ℕ} (hn : 1 < n) :
  irreducible (x ^ n) → is_unit x
:=
begin
  intro h,
  rcases n with rfl|rfl|_,
  { norm_num at hn, contradiction },
  { norm_num at hn },
  { rw pow_succ at h,
    cases of_irreducible_mul h with hu hu,
    { assumption },
    { exact is_unit_of_pow (nat.succ_pos n) hu } },
end


variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [comm_cancel_monoid_with_zero α]


lemma not_prime_pow {x : α} {n : ℕ} (hn : 1 < n) : ¬ prime (x ^ n) :=
λ hp, hp.not_unit $ is_unit.pow _ $ of_irreducible_pow hn $ irreducible_of_prime hp

end

@[norm_cast]
lemma int.of_nat_is_unit {n : ℕ} : is_unit (n : ℤ) ↔ is_unit n :=
by rw [nat.is_unit_iff, is_unit_int, int.nat_abs_of_nat]

lemma int.prime.dvd_mul''  {m n p : ℤ}
  (hp : prime p) (h : p ∣ m * n) : p ∣ m ∨ p ∣ n :=
begin
  rw int.prime_iff at hp,
  rwa [←int.nat_abs_dvd_abs_iff, ←int.nat_abs_dvd_abs_iff, ←hp.dvd_mul , ←int.nat_abs_mul,
    int.nat_abs_dvd_abs_iff],
end

lemma two_not_cube (r : ℕ) : r ^ 3 ≠ 2 :=
begin
  have : 1 ≤ 3,
  { norm_num },
  apply monotone.ne_of_lt_of_lt_nat (nat.pow_left_strict_mono this).monotone 1; norm_num,
end

lemma int.lt_mul_self {a b : ℤ} (ha : 0 < a) (hb : 1 < b) : a < b * a :=
begin
  convert int.mul_lt_mul hb le_rfl ha (le_trans zero_le_one hb.le),
  rw one_mul,
end

lemma pow_two_neg (a : ℤ) : (-a) ^ 2 = a ^ 2 :=
begin
  exact neg_square a
end

theorem int.associated_iff {a b : ℤ} : associated a b ↔ a.nat_abs = b.nat_abs :=
begin
  rw [←dvd_dvd_iff_associated, ←int.nat_abs_dvd_abs_iff, ←int.nat_abs_dvd_abs_iff, dvd_dvd_iff_associated],
  exact associated_iff_eq,
end

theorem prime_dvd_prime_iff_eq {p q : ℤ} (pp : prime p) (qp : prime q) : p ∣ q ↔ associated p q :=
begin
  rw int.prime_iff at pp qp,
  rw ←int.nat_abs_dvd_abs_iff,
  rw int.associated_iff,
  split; intro H,
  {rwa nat.prime_dvd_prime_iff_eq pp qp at H},
  {rw H}
end

lemma int.is_unit_iff_nat_abs {x : ℤ} : is_unit x ↔ x.nat_abs = 1 :=
begin
  split; intro h,
  { obtain ⟨u, rfl⟩ := h,
    obtain (rfl|rfl) := int.units_eq_one_or u;
      simp only [units.coe_one, int.nat_abs_neg, units.coe_neg_one, int.nat_abs_one] },
  { rw [is_unit_iff_dvd_one, ←int.nat_abs_dvd_abs_iff, h, int.nat_abs_one] }
end

lemma int.is_unit_iff_abs {x : ℤ} : is_unit x ↔ abs x = 1 :=
by rw [int.is_unit_iff_nat_abs, int.abs_eq_nat_abs, ←int.coe_nat_one, int.coe_nat_inj']

lemma int.neg_prime {p : ℤ} (hp : prime p) : prime (-p) :=
by rwa [int.prime_iff, int.nat_abs_neg, ←int.prime_iff]

lemma int.abs_prime {p : ℤ} (hp : prime p) : prime (abs p) :=
by rwa [int.prime_iff, int.nat_abs_abs, ←int.prime_iff]

lemma int.abs_odd {p : ℤ} (hp : odd p) : odd (abs p) :=
by rwa [←int.nat_abs_odd, int.nat_abs_abs, int.nat_abs_odd]

lemma int.abs_iff (x : ℤ) : abs x = x ∨ abs x = -x :=
begin
  exact max_choice x (-x),
end

lemma int.abs_eq (x : ℤ) : x = abs x ∨ x = -abs x :=
begin
  cases int.abs_iff x with h h,
  { left, exact h.symm },
  { right, exact eq_neg_of_eq_neg h }
end

lemma int.abs_eq_abs_iff {a b : ℤ} (h : abs a = abs b) : a = b ∨ a = -b :=
begin
  cases int.abs_iff a with h1 h1;
  cases int.abs_iff b with h2 h2;
  rw [h1, h2] at h,
  { left, exact h },
  { right, exact h },
  { right, rwa [eq_neg_iff_eq_neg, eq_comm] },
  { left, rwa [eq_neg_iff_eq_neg, eq_comm, neg_neg] at h },
end

lemma int.nat_abs_eq_nat_abs_iff {a b : ℤ} (h : a.nat_abs = b.nat_abs) : a = b ∨ a = -b :=
begin
  apply int.abs_eq_abs_iff,
  rwa [int.abs_eq_nat_abs, int.abs_eq_nat_abs, int.coe_nat_inj'],
end

theorem int.exists_prime_and_dvd {n : ℤ} (n2 : 2 ≤ n.nat_abs) : ∃ p, prime p ∧ p ∣ n :=
begin
  obtain ⟨p, pp, pd⟩ := nat.exists_prime_and_dvd n2,
  exact ⟨p, nat.prime_iff_prime_int.mp pp, int.coe_nat_dvd_left.mpr pd⟩,
end

theorem int.is_coprime_of_dvd' {x y : ℤ}
  (z : ¬ (x = 0 ∧ y = 0))
  (H : ∀ z ∈ nonunits ℤ, z ≠ 0 → prime z → z ∣ x → ¬ z ∣ y) :
  is_coprime x y :=
begin
  rw [←int.gcd_eq_one_iff_coprime],
  simp only [int.gcd],
  change nat.coprime _ _,
  apply nat.coprime_of_dvd,
  intros k kprime ka kb,
  apply H k,
  { intro H,
    apply kprime.ne_one,
    rwa [int.is_unit_iff_nat_abs, int.nat_abs_of_nat] at H },
  { simp only [int.coe_nat_eq_zero, ne.def], exact kprime.ne_zero },
  { rwa ←nat.prime_iff_prime_int },
  { exact int.coe_nat_dvd_left.mpr ka },
  { exact int.coe_nat_dvd_left.mpr kb },
end

/-
lemma int.dvd_mul_cancel_prime {p n k : ℤ}
  (h : k ∣ p * n)
  (hne : k.nat_abs ≠ p.nat_abs)
  (hp : prime p)
  (hk : prime k) : k ∣ n :=
begin
  rw ←nat.prime_iff_prime_int at hp hk,
  cases hk.div_or_div h with h h,
  { exfalso,
    rw nat.prime_dvd_prime_iff_eq at h,
    contradiction },
  { assumption },
end
-/

theorem int.associated_pow_of_mul_eq_pow {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : is_coprime a b) {k : ℕ} (h : a * b = c ^ k) : ∃ d, associated a (d ^ k) :=
begin
  have ha' : associates.mk a ≠ 0,
  { rwa [ne.def, associates.mk_eq_zero] },
  have hb' : associates.mk b ≠ 0,
  { rwa [ne.def, associates.mk_eq_zero] },
  have hab' : ∀ (d : associates ℤ), d ∣ associates.mk a → d ∣ associates.mk b → ¬prime d,
  { intros d da db dprime,
    obtain ⟨d', rfl⟩ := associates.exists_rep d,
    rw associates.mk_dvd_mk at da db,
    rw [associates.prime_mk] at dprime,
    apply dprime.not_unit,
    exact is_coprime.is_unit_of_dvd' hab da db },
  have h' : associates.mk a * associates.mk b = (associates.mk c) ^ k,
  { rw [associates.mk_mul_mk, ←associates.mk_pow, h] },
  obtain ⟨d, hd⟩ := associates.eq_pow_of_mul_eq_pow ha' hb' hab' h',
  obtain ⟨d', rfl⟩ := associates.exists_rep d,
  rw [←associates.mk_pow, associates.mk_eq_mk_iff_associated, int.associated_iff] at hd,
  use d',
  rwa int.associated_iff
end

theorem int.eq_pow_of_mul_eq_pow_bit1 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : is_coprime a b) {k : ℕ} (h : a * b = c ^ (bit1 k)) : ∃ d, a = d ^ (bit1 k) :=
begin
  obtain ⟨d, hd⟩ := int.associated_pow_of_mul_eq_pow ha hb hab h,
  rw int.associated_iff at hd,
  obtain rfl|rfl := int.nat_abs_eq_nat_abs_iff hd,
  { use d, },
  { use -d, rw neg_pow_bit1 },
end
