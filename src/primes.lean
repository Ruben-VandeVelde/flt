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

section comm_monoid_with_zero

variables {α : Type*} [comm_monoid_with_zero α]

@[simp] theorem associates.mk_ne_zero {a : α} : associates.mk a ≠ 0 ↔ a ≠ 0 :=
not_congr associates.mk_eq_zero

end comm_monoid_with_zero

theorem nat.eq_pow_of_mul_eq_pow {a b c : ℕ} (ha : 0 < a) (hb : 0 < b)
  (hab : nat.coprime a b) {k : ℕ} (h : a * b = c ^ k) : ∃ d, a = d ^ k :=
begin
  have ha' : associates.mk a ≠ 0,
  { rwa [associates.mk_ne_zero, ←pos_iff_ne_zero] },
  have hb' : associates.mk b ≠ 0,
  { rwa [associates.mk_ne_zero, ←pos_iff_ne_zero] },
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

lemma nat.even_pow' {m n : nat} (h : n ≠ 0) : even (m^n) ↔ even m :=
begin
  rw [nat.even_pow], tauto,
end

lemma int.even_pow' {m : ℤ} {n : ℕ} (h : n ≠ 0) : even (m^n) ↔ even m :=
begin
  rw [int.even_pow], tauto,
end

theorem int.nat_abs_ne_zero {a : ℤ} : a.nat_abs ≠ 0 ↔ a ≠ 0 := not_congr int.nat_abs_eq_zero

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
lemma int.odd_coe_nat {n : ℕ} : odd (n : ℤ) ↔ odd n :=
by { rw [int.odd_iff, nat.odd_iff], norm_cast }

@[parity_simps] lemma int.nat_abs_even {n : ℤ} : even n.nat_abs ↔ even n :=
int.coe_nat_dvd_left.symm

@[parity_simps] lemma int.nat_abs_odd {n : ℤ} : odd n.nat_abs ↔ odd n :=
by rw [int.odd_iff_not_even, nat.odd_iff_not_even, int.nat_abs_even]

section
variables {R : Type*} [comm_semiring R] {x y z : R}
variables {m n : ℕ}

lemma not_coprime_zero_zero [nontrivial R] : ¬ is_coprime (0 : R) 0 :=
by simp only [add_zero, is_coprime, exists_false, zero_ne_one, mul_zero, not_false_iff]

theorem is_coprime.of_pow_left (hm : 0 < m) (H : is_coprime (x ^ m) y) : is_coprime x y :=
begin
  rw [← finset.card_range m, ← finset.prod_const] at H,
  apply is_coprime.of_prod_left H 0,
  exact finset.mem_range.mpr hm,
end

theorem is_coprime.of_pow_right (hm : 0 < m) (H : is_coprime x (y ^ m)) : is_coprime x y :=
(is_coprime.of_pow_left hm H.symm).symm

theorem is_coprime.of_pow
 (hm : 0 < m)
 (hn : 0 < n)
 (H1 : is_coprime (x ^ m) (y ^ n)) : is_coprime x y :=
(H1.of_pow_left hm).of_pow_right hn

end
section
variables {R : Type*} [comm_ring R] {x y z : R}
variables {m n : ℕ}
lemma coprime_add_self'
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
  apply is_coprime.of_pow hn hn,
  rw ←hsoln,
  apply coprime_add_self',
  exact is_coprime.pow hxx,
end
end

lemma nat.lt_mul_of_one_lt_left {m n : ℕ} (hm : 0 < m) (hn : 1 < n) : m < n * m :=
begin
  convert nat.mul_lt_mul hn (le_refl _) hm,
  rw one_mul
end

lemma int.div_ne_zero_of_dvd {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hadvd: b ∣ a) : a / b ≠ 0 :=
begin
  obtain ⟨c, rfl⟩ := hadvd,
  rw [mul_comm, int.mul_div_cancel _ hb],
  rintro rfl,
  rw mul_zero at ha,
  exact ha rfl,
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

theorem int.coprime_div_gcd_div_gcd {m n : ℤ} (H : 0 < int.gcd m n) :
  is_coprime (m / int.gcd m n) (n / int.gcd m n) :=
by rw [←int.gcd_eq_one_iff_coprime, int.gcd_div (int.gcd_dvd_left m n) (int.gcd_dvd_right m n),
    int.nat_abs_of_nat, nat.div_self H]

lemma int.gcd_ne_zero_iff {i j : ℤ} : int.gcd i j ≠ 0 ↔ i ≠ 0 ∨ j ≠ 0 :=
iff.trans (not_congr int.gcd_eq_zero_iff) not_and_distrib

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

end

section
variables {R : Type*} [comm_ring R]

lemma is_coprime.neg_left {a b : R} (h : is_coprime a b) : is_coprime (-a) b :=
begin
  obtain ⟨x, y, h⟩ := h,
  use [-x, y],
  simpa only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg] using h,
end

lemma is_coprime.neg_left_iff (a b : R) : is_coprime (-a) b ↔ is_coprime a b :=
⟨λ h, (neg_neg a) ▸ is_coprime.neg_left h, is_coprime.neg_left⟩

lemma is_coprime.neg_right {a b : R} (h : is_coprime a b) : is_coprime a (-b) :=
begin
  obtain ⟨x, y, h⟩ := h,
  use [x, -y],
  simpa only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg] using h,
end

lemma is_coprime.neg_right_iff (a b : R) : is_coprime a (-b) ↔ is_coprime a b :=
⟨λ h, (neg_neg b) ▸ is_coprime.neg_right h, is_coprime.neg_right⟩

lemma is_coprime.neg_neg {a b : R} (h : is_coprime a b) : is_coprime (-a) (-b) :=
h.neg_left.neg_right

lemma is_coprime.neg_neg_iff (a b : R) : is_coprime (-a) (-b) ↔ is_coprime a b :=
(is_coprime.neg_left_iff _ _).trans (is_coprime.neg_right_iff _ _)

end
section
theorem is_unit_of_pow {α} [comm_monoid α] {x : α} {n : ℕ} (hn : 0 < n)
  (h : is_unit (x ^ n)) : is_unit x
:=
begin
  cases n,
  { norm_num at hn },
  { rw pow_succ at h,
    exact is_unit_of_mul_is_unit_left h }
end

theorem of_irreducible_pow {α} [comm_monoid α] {x : α} {n : ℕ} (hn : 1 < n) :
  irreducible (x ^ n) → is_unit x
:=
begin
  intro h,
  rcases n with rfl|rfl|_,
  { norm_num at hn },
  { norm_num at hn },
  { rw pow_succ at h,
    cases of_irreducible_mul h with hu hu,
    { assumption },
    { exact is_unit_of_pow (nat.succ_pos n) hu } },
end


variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [comm_cancel_monoid_with_zero α]


lemma pow_not_prime {x : α} {n : ℕ} (hn : 1 < n) : ¬ prime (x ^ n) :=
λ hp, hp.not_unit $ is_unit.pow _ $ of_irreducible_pow hn $ irreducible_of_prime hp

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
  rw ←int.nat_abs_pow,
  rw H,
  norm_num,
end

lemma int.lt_mul_self {a b : ℤ} (ha : 0 < a) (hb : 1 < b) : a < b * a :=
begin
  convert int.mul_lt_mul hb le_rfl ha (le_trans zero_le_one hb.le),
  rw one_mul,
end

-- todo square neg_square and neg_pow_bit0

theorem prime_dvd_prime_iff_eq {p q : ℤ} (pp : prime p) (qp : prime q) : p ∣ q ↔ associated p q :=
begin
  rw int.prime_iff_nat_abs_prime at pp qp,
  rw ←int.nat_abs_dvd_abs_iff,
  rw int.associated_iff_nat_abs,
  exact nat.prime_dvd_prime_iff_eq pp qp,
end

lemma int.is_unit_iff_abs {x : ℤ} : is_unit x ↔ abs x = 1 :=
by rw [int.is_unit_iff_nat_abs_eq, int.abs_eq_nat_abs, ←int.coe_nat_one, int.coe_nat_inj']

section
variables {α : Type*} [linear_ordered_add_comm_group α]

lemma abs_choice (x : α) : abs x = x ∨ abs x = -x := max_choice _ _

lemma abs_eq' (x : α) : x = abs x ∨ x = -abs x :=
begin
  obtain h|h := abs_choice x,
  { left, exact h.symm },
  { right, exact eq_neg_of_eq_neg h }
end

end

section
variables {α : Type*} [ring α]

lemma is_unit.neg_iff (u : α) : is_unit (-u) ↔ is_unit u :=
⟨λ h, neg_neg u ▸ h.neg, is_unit.neg⟩

end

section
variables {α : Type*} [comm_ring α]

lemma prime.neg {p : α} (hp : prime p) : prime (-p) :=
begin
  obtain ⟨h1, h2, h3⟩ := hp,
  exact ⟨neg_ne_zero.mpr h1, by rwa is_unit.neg_iff, by simpa [neg_dvd] using h3⟩
end

end

section
variables {α : Type*} [linear_ordered_comm_ring α]

lemma prime.abs {p : α} (hp : prime p) : prime (abs p) :=
begin
  obtain h|h := abs_choice p; rw h,
  { exact hp },
  { exact hp.neg }
end

end

lemma int.abs_odd {p : ℤ} (hp : odd p) : odd (abs p) :=
by rwa [←int.nat_abs_odd, int.nat_abs_abs, int.nat_abs_odd]

-- todo consider removing
lemma int.abs_eq_abs_iff {a b : ℤ} (h : abs a = abs b) : a = b ∨ a = -b :=
by rwa [←int.nat_abs_eq_nat_abs_iff, ←int.coe_nat_inj', ←int.abs_eq_nat_abs, ←int.abs_eq_nat_abs]

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
    rwa [int.is_unit_iff_nat_abs_eq, int.nat_abs_of_nat] at H },
  { simp only [int.coe_nat_eq_zero, ne.def], exact kprime.ne_zero },
  { rwa ←nat.prime_iff_prime_int },
  { exact int.coe_nat_dvd_left.mpr ka },
  { exact int.coe_nat_dvd_left.mpr kb },
end

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
  rw [←associates.mk_pow, associates.mk_eq_mk_iff_associated] at hd,
  exact ⟨d', hd⟩,
end

theorem int.eq_pow_of_mul_eq_pow_bit1_left {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : is_coprime a b) {k : ℕ} (h : a * b = c ^ (bit1 k)) : ∃ d, a = d ^ (bit1 k) :=
begin
  obtain ⟨d, hd⟩ := int.associated_pow_of_mul_eq_pow ha hb hab h,
  rw [int.associated_iff_nat_abs, int.nat_abs_eq_nat_abs_iff] at hd,
  obtain rfl|rfl := hd,
  { use d, },
  { use -d, rw neg_pow_bit1 },
end

theorem int.eq_pow_of_mul_eq_pow_bit1 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : is_coprime a b) {k : ℕ} (h : a * b = c ^ (bit1 k)) :
  (∃ d, a = d ^ (bit1 k)) ∧ (∃ e, b = e ^ (bit1 k)) :=
begin
  split,
  { exact int.eq_pow_of_mul_eq_pow_bit1_left ha hb hab h },
  { rw mul_comm at h,
    exact int.eq_pow_of_mul_eq_pow_bit1_left hb ha hab.symm h }
end

lemma int.dvd_mul_cancel_prime {p : ℕ} {n k : ℤ}
  (hne : k.nat_abs ≠ p)
  (hp : nat.prime p)
  (hk : prime k)
  (h : k ∣ p * n) : k ∣ n :=
begin
  apply (prime.div_or_div hk h).resolve_left,
  rw int.prime_iff_nat_abs_prime at hk,
  rwa [int.coe_nat_dvd_right, nat.prime_dvd_prime_iff_eq hk hp]
end

theorem int.prime.coprime_iff_not_dvd {p n : ℤ} (pp : prime p) : is_coprime p n ↔ ¬ p ∣ n :=
begin
  rw int.prime_iff_nat_abs_prime at pp,
  rw [←int.nat_abs_dvd_abs_iff, ←nat.prime.coprime_iff_not_dvd pp, ←int.gcd_eq_one_iff_coprime],
  refl,
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

lemma eq_of_associated_of_nonneg {a b : ℤ} (h : associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) : a = b :=
begin
  obtain (rfl|ha') := ha.eq_or_lt,
  { rw [eq_comm, ←associated_zero_iff_eq_zero], exact h.symm },
  { obtain ⟨u, rfl⟩ := h,
    have := u.is_unit,
    rw [int.is_unit_iff_abs, abs_of_nonneg (nonneg_of_mul_nonneg_left hb ha')] at this,
    rw [this, mul_one] }
end

lemma int.nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z :=
calc 0 ≤ (z.nat_abs : ℤ) : int.coe_zero_le _
... = normalize z : int.coe_nat_abs_eq_normalize _
... = z : hz

lemma int.factors_nonneg {z a : ℤ} (ha : a ∈ unique_factorization_monoid.factors z) : 0 ≤ a :=
int.nonneg_of_normalize_eq_self (unique_factorization_monoid.normalize_factor a ha)

lemma int.factors_eq' (z : ℤ) :
  ((unique_factorization_monoid.factors z).map int.nat_abs).map (coe : ℕ → ℤ)
  = unique_factorization_monoid.factors z :=
begin
  conv_rhs { rw ←multiset.map_id (unique_factorization_monoid.factors z) },
  rw multiset.map_map,
  apply multiset.map_congr,
  intros x hx,
  rw [id.def, function.comp_app, int.nat_abs_of_nonneg (int.factors_nonneg hx)],
end

lemma int.factors_eq (z : ℤ) :
  unique_factorization_monoid.factors z = multiset.map (int.of_nat_hom) (nat.factors z.nat_abs) :=
begin
  rw ←nat.factors_eq,
  rw ←multiset.rel_eq,
  have : multiset.rel associated (unique_factorization_monoid.factors z) (multiset.map (int.of_nat_hom : ℕ →* ℤ) (unique_factorization_monoid.factors z.nat_abs)),
  { apply prime_factors_unique unique_factorization_monoid.prime_of_factor,
    { intros x hx,
      obtain ⟨y, hy, rfl⟩ := multiset.mem_map.mp hx,
      simp only [ring_hom.coe_monoid_hom, ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat],
      rw [←nat.prime_iff_prime_int, ←irreducible_iff_nat_prime],
      exact unique_factorization_monoid.irreducible_of_factor _ hy },
    { by_cases hz: z = 0,
      { simp only [hz, unique_factorization_monoid.factors_zero, multiset.map_zero, int.nat_abs_zero] },
      apply associated.trans (unique_factorization_monoid.factors_prod hz),
      apply associated.trans (int.associated_nat_abs z),
      rw multiset.prod_hom,
      simp only [ring_hom.coe_monoid_hom, ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat,
        int.associated_iff_nat_abs, int.nat_abs_of_nat, ←associated_iff_eq],
      exact (unique_factorization_monoid.factors_prod (int.nat_abs_ne_zero_of_ne_zero hz)).symm } },
  apply multiset.rel.mono this,
  intros a ha b hb hab,
  apply eq_of_associated_of_nonneg hab (int.factors_nonneg ha),
  obtain ⟨b', hb', rfl⟩ := multiset.mem_map.mp hb,
  simp only [ring_hom.coe_monoid_hom, int.coe_nat_nonneg, ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat],
end

lemma pow_two_abs {R:Type*} [linear_ordered_ring R] (x : R) : abs x ^ 2 = x ^ 2 :=
pow_bit0_abs x 1
