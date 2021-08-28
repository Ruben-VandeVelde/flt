import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import ring_theory.coprime
import ring_theory.int.basic
import ring_theory.euclidean_domain
import ring_theory.noetherian
import ring_theory.principal_ideal_domain
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
    rw [associates.prime_mk, ←nat.prime_iff] at dprime,
    exact nat.not_coprime_of_dvd_of_dvd dprime.one_lt da db hab },
  have h' : associates.mk a * associates.mk b = (associates.mk c) ^ k,
  { rw [associates.mk_mul_mk, ←associates.mk_pow, h] },
  obtain ⟨d, hd⟩ := associates.eq_pow_of_mul_eq_pow ha' hb' hab' h',
  obtain ⟨d', rfl⟩ := associates.exists_rep d,
  use d',
  rw [←associated_iff_eq, ←associates.mk_eq_mk_iff_associated, hd, associates.mk_pow],
end

lemma int.four_dvd_add_or_sub_of_odd {a b : ℤ}
  (ha : odd a)
  (hb : odd b) :
  4 ∣ a + b ∨ 4 ∣ a - b :=
begin
  obtain ⟨m, rfl⟩ := ha,
  obtain ⟨n, rfl⟩ := hb,
  obtain h|h := int.even_or_odd (m + n),
  { right,
    rw [int.even_add, ←int.even_sub] at h,
    obtain ⟨k, hk⟩ := h,
    convert dvd_mul_right 4 k,
    rw [eq_add_of_sub_eq hk],
    ring },
  { left,
    obtain ⟨k, hk⟩ := h,
    convert dvd_mul_right 4 (k + 1),
    rw [eq_sub_of_add_eq hk],
    ring },
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

lemma int.div_ne_zero_of_dvd {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hadvd: b ∣ a) : a / b ≠ 0 :=
begin
  obtain ⟨c, rfl⟩ := hadvd,
  rw [mul_comm, int.mul_div_cancel _ hb],
  exact right_ne_zero_of_mul ha,
end

theorem int.coprime_div_gcd_div_gcd {m n : ℤ} (H : 0 < int.gcd m n) :
  is_coprime (m / int.gcd m n) (n / int.gcd m n) :=
by rw [←int.gcd_eq_one_iff_coprime, int.gcd_div (int.gcd_dvd_left m n) (int.gcd_dvd_right m n),
    int.nat_abs_of_nat, nat.div_self H]

lemma int.gcd_ne_zero_iff {i j : ℤ} : int.gcd i j ≠ 0 ↔ i ≠ 0 ∨ j ≠ 0 :=
iff.trans (not_congr int.gcd_eq_zero_iff) not_and_distrib

section
theorem is_unit.pow_iff {α} [comm_monoid α] {x : α} {n : ℕ} (hn : 0 < n) :
  is_unit (x ^ n) ↔ is_unit x :=
begin
  refine ⟨λ h, _, is_unit.pow n⟩,
  obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero hn.ne',
  rw pow_succ at h,
  exact is_unit_of_mul_is_unit_left h
end

theorem of_irreducible_pow {α} [comm_monoid α] {x : α} {n : ℕ} (hn : 1 < n) :
  irreducible (x ^ n) → is_unit x :=
begin
  intro h,
  obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero (zero_lt_one.trans hn).ne',
  rw nat.succ_lt_succ_iff at hn,
  obtain ⟨k, rfl⟩ := nat.exists_eq_succ_of_ne_zero hn.ne',
  rw pow_succ at h,
  cases of_irreducible_mul h with hu hu,
  { assumption },
  { rwa ←is_unit.pow_iff (nat.succ_pos _) },
end


variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables [comm_cancel_monoid_with_zero α]


lemma pow_not_prime {x : α} {n : ℕ} (hn : 1 < n) : ¬ prime (x ^ n) :=
λ hp, hp.not_unit $ is_unit.pow _ $ of_irreducible_pow hn $ hp.irreducible

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

-- todo square neg_square and neg_pow_bit0

lemma int.is_unit_iff_abs {x : ℤ} : is_unit x ↔ abs x = 1 :=
by rw [int.is_unit_iff_nat_abs_eq, int.abs_eq_nat_abs, ←int.coe_nat_one, int.coe_nat_inj']

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

theorem int.exists_prime_and_dvd {n : ℤ} (n2 : 2 ≤ n.nat_abs) : ∃ p, prime p ∧ p ∣ n :=
begin
  obtain ⟨p, pp, pd⟩ := nat.exists_prime_and_dvd n2,
  exact ⟨p, nat.prime_iff_prime_int.mp pp, int.coe_nat_dvd_left.mpr pd⟩,
end

theorem int.associated_pow_of_mul_eq_pow {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : is_coprime a b) {k : ℕ} (h : a * b = c ^ k) : ∃ d, associated a (d ^ k) :=
begin
  have : a.nat_abs * b.nat_abs = c.nat_abs ^ k,
  { rw [←int.nat_abs_mul, ←int.nat_abs_pow, h] },
  rw int.coprime_iff_nat_coprime at hab,
  obtain ⟨d, hd⟩ := nat.eq_pow_of_mul_eq_pow
    (int.nat_abs_pos_of_ne_zero ha) (int.nat_abs_pos_of_ne_zero hb) hab this,
  use d,
  rw [int.associated_iff_nat_abs, hd, int.nat_abs_pow, int.nat_abs_of_nat]
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
  apply (prime.dvd_or_dvd hk h).resolve_left,
  rw int.prime_iff_nat_abs_prime at hk,
  rwa [int.coe_nat_dvd_right, nat.prime_dvd_prime_iff_eq hk hp]
end

section

lemma irreducible_dvd_irreducible_iff_associated {α : Type*} [comm_cancel_monoid_with_zero α]
  {p q : α} (pp : irreducible p) (qp : irreducible q) :
  p ∣ q ↔ associated p q :=
⟨irreducible.associated_of_dvd pp qp, associated.dvd⟩

variables {R : Type*} [euclidean_domain R]

theorem prime_dvd_prime_iff_associated {p q : R} (pp : prime p) (qp : prime q) :
  p ∣ q ↔ associated p q :=
irreducible_dvd_irreducible_iff_associated pp.irreducible qp.irreducible

theorem is_coprime_of_dvd' {x y : R}
  (z : ¬ (x = 0 ∧ y = 0))
  (H : ∀ z : R, irreducible z → z ∣ x → ¬ z ∣ y) :
  is_coprime x y :=
begin
  apply is_coprime_of_dvd z,
  intros z znu znz zx zy,
  obtain ⟨i, h1, h2⟩ := wf_dvd_monoid.exists_irreducible_factor znu znz,
  apply H i h1;
  { apply dvd_trans h2, assumption },
end

theorem irreducible.coprime_iff_not_dvd {p n : R} (pp : irreducible p) : is_coprime p n ↔ ¬ p ∣ n :=
begin
  split,
  { intros co H,
    apply pp.not_unit,
    rw is_unit_iff_dvd_one,
    apply is_coprime.dvd_of_dvd_mul_left co,
    rw mul_one n,
    exact H },
  { intro nd,
    apply is_coprime_of_dvd',
    { rintro ⟨hp, -⟩,
      apply pp.ne_zero hp },
    rintro z zi zp zn,
    refine (nd $ dvd_trans (associated.dvd _) zn),
    exact (zi.associated_of_dvd pp zp).symm },
end

theorem prime.coprime_iff_not_dvd {p n : R} (pp : prime p) : is_coprime p n ↔ ¬ p ∣ n :=
pp.irreducible.coprime_iff_not_dvd

end

theorem int.is_coprime_of_dvd' {x y : ℤ}
  (z : ¬ (x = 0 ∧ y = 0))
  (H : ∀ z : ℤ, prime z → z ∣ x → ¬ z ∣ y) :
  is_coprime x y :=
is_coprime_of_dvd' z $ λ z zi, H z $ gcd_monoid.prime_of_irreducible zi

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
    rw [←int.nat_abs_of_nonneg (nonneg_of_mul_nonneg_left hb ha'),
      int.is_unit_iff_nat_abs_eq.mp u.is_unit, int.coe_nat_one, mul_one] }
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
