import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import tactic

section

variables {α : Type*} [ordered_semiring α] [nontrivial α] {a b c d : α}

@[field_simps] lemma three_ne_zero : (3:α) ≠ 0 :=
zero_lt_three.ne.symm

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
  (hab : nat.coprime a b) {k : ℕ} (h : a * b = c ^ k) : ∃ d, a = d ^ k := sorry

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

lemma coprime_add_self_pow
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
