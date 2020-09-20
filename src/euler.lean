import data.int.basic
import data.int.parity
import data.nat.gcd
import data.pnat.basic
import tactic
import .primes

import algebra.associated

variables (α : Type*) [integral_domain α]
theorem eq_pow_of_mul_eq_pow {a b c : associates α} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) {k : ℕ} (h : a * b = c ^ k) :
  ∃ (d : associates α), a = d ^ k := sorry

/-
universe u

open nat
protected def strong_rec_on {p : nat → Sort u} (n : nat) (h : ∀ n, (∀ m, m < n → p m) → p n) : p n :=
suffices ∀ n m, m < n → p m, from this (succ n) n (lt_succ_self _),
begin
  intros n, induction n with n ih,
    {intros m h₁, exact absurd h₁ (not_lt_zero _)},
    {intros m h₁,
      apply or.by_cases (lt_or_eq_of_le (le_of_lt_succ h₁)),
        {intros, apply ih, assumption},
        {intros, subst m, apply h _ ih}}
end

lemma pnat.strong_induction_on {p : pnat → Prop} (n : pnat) (h : ∀ k, (∀ m, m < k → p m) → p k) : p n :=
begin
  induction n',

  suffices : ∀ n m, m < n → p m, from this (n + 1) n (nat.lt_succ_self _),
  intros n, induction (n : ℕ) with n ih,
  intros m h₁,
  apply h,
  intros k hk,
  {
    apply or.by_cases (lt_or_eq_of_le (le_of_lt_succ h₁)),
      {intros, apply ih, assumption},
      {intros, subst m, apply h _ ih}}
end
-/
lemma pnat.strong_induction_on {p : pnat → Prop} (n : pnat) (h : ∀ k, (∀ m, m < k → p m) → p k) : p n :=
begin
  let p' : nat → Prop := λ n, if h : 0 < n then p ⟨n, h⟩ else true,
  have : ∀ n', p' n',
  {
    intro n',
    refine nat.strong_induction_on n' _,
    intro k,
    dsimp [p'],
    split_ifs,
    {
      intros a,
      apply h,
      intros m hm,
      have := a m.1 hm,
      split_ifs at this,
      {
        convert this,
        simp only [subtype.coe_eta, subtype.val_eq_coe],
      },
      {exfalso,
      exact h_2 m.2}},
    {intros, trivial}    
  },
  have a := this n.1,
  dsimp [p'] at a,
  split_ifs at a,
  { convert a, simp only [subtype.coe_eta], },
  { exfalso, exact h_1 n.pos },
end.

example (a b : int) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := sq_sub_sq a b
example (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
begin
  rw nat.pow_two,
  rw nat.pow_two,
  exact nat.mul_self_sub_mul_self_eq a b,
end
theorem nat.sq_sub_sq (a b : nat) : a ^ 2 - b ^ 2 = (a + b) * (a - b) :=
nat.pow_two_sub_pow_two _ _

example (a b : nat) : (a + b) % 2 = (a + (b % 2)) % 2 := (nat.add_mod_mod a b 2).symm
--example (a b : nat) : (a - b) % 2 = (a - (b % 2)) % 2 := by library_search
example (P Q : Prop) (h: ¬(P ↔ Q)) : (P ↔ ¬Q) := by {tauto!,}
/-
begin
  zify,
  have : (_ : ℤ) = _ := nat.cast_sub h,
  rw this,
    rw ←sq_sub_sq,
    norm_cast,
end
  -/
example (d x n : nat) (h: 0 < n) : d ^ n ∣ x ^ n → d ∣ x := by refine (nat.pow_dvd_pow_iff h).mp

theorem coprime_div_gcd_div_gcd' {m n : ℕ} (H : 0 < nat.gcd m n) :
  nat.coprime (m / nat.gcd m n) (n / nat.gcd m n) :=
begin
  delta nat.coprime,
  rw nat.gcd_div (nat.gcd_dvd_left m n) (nat.gcd_dvd_right m n),
  rw nat.div_self H,
end

def flt_coprime
  (a b c n : ℕ) :=
  0 < a ∧ 0 < b ∧ 0 < c ∧ 
  a ^ n + b ^ n = c ^ n ∧ 
  nat.coprime a b ∧
  nat.coprime a c ∧
  nat.coprime b c

--example (d c : nat) (h : d ∣ c) : d ≤ c := by refine nat.le_of_dvd _ h
--example (c d n : nat) (h : d ∣ c) : c ^ n / d ^ n = (c / d) ^ n := by suggest
example (a b : nat) : a / b ≤ a := nat.div_le_self a b


lemma exists_coprime
  (a b c n : ℕ)
  (hpos : 0 < a ∧ 0 < b ∧ 0 < c)
  (hn : 0 < n)
  (h : a ^ n + b ^ n = c ^ n) :
  ∃ a' b' c', a' ≤ a ∧ b' ≤ b ∧ c' ≤ c ∧ flt_coprime a' b' c' n :=
begin
  by_cases h' : ¬nat.coprime a b ∨ ¬nat.coprime a c ∨ ¬nat.coprime b c,
  { 
    let d := nat.gcd a b,
    obtain ⟨ha : d ∣ a, hb : d ∣ b⟩ := nat.gcd_dvd a b,
    have hc : d ∣ c,
    { rw ←nat.pow_dvd_pow_iff hn,
      rw ←h,
      apply dvd_add; rw nat.pow_dvd_pow_iff hn; assumption },
    use [a / d, b / d, c / d],
    unfold flt_coprime,
    have hdpos : 0 < d := nat.gcd_pos_of_pos_left _ hpos.1,
    have hdnpos : 0 < d ^ n := nat.pow_pos hdpos n,
    have hsoln : (a / d) ^ n + (b / d) ^ n = (c / d) ^ n,
    { apply nat.eq_of_mul_eq_mul_right hdnpos,
      calc ((a / d) ^ n + (b / d) ^ n) * d ^ n
          = (a / d) ^ n * d ^ n + (b / d) ^ n * d ^ n : add_mul _ _ _
      ... = (a / d * d) ^ n  + (b / d) ^ n * d ^ n : by rw nat.mul_pow
      ... = (a / d * d) ^ n  + (b / d * d) ^ n : by rw nat.mul_pow (b / d)
      ... = a ^ n + b ^ n : by rw [nat.div_mul_cancel ha, nat.div_mul_cancel hb]
      ... = c ^ n : h
      ... = (c / d * d) ^ n : by rw [nat.div_mul_cancel hc]
      ... = (c / d) ^ n * d ^ n : by rw nat.mul_pow },
    have hsoln' : (a / d) ^ n = (c / d) ^ n - (b / d) ^ n,
    {
      rw ←hsoln,
      rw nat.add_sub_cancel,
    },
    have hsoln'' : (b / d) ^ n = (c / d) ^ n - (a / d) ^ n,
    {
      have := hsoln,
      rw add_comm at this,
      rw ←this,
      rw nat.add_sub_cancel,
    },
    refine ⟨_, _, _, _, _, _, _, _, _, _⟩,
    { apply nat.div_le_self },
    { apply nat.div_le_self },
    { apply nat.div_le_self },
    { refine nat.div_pos (nat.le_of_dvd hpos.1 ‹_›) hdpos },
    { refine nat.div_pos (nat.le_of_dvd hpos.2.1 ‹_›) hdpos },
    { refine nat.div_pos (nat.le_of_dvd hpos.2.2 ‹_›) hdpos },
    { exact hsoln },
    {exact nat.coprime_div_gcd_div_gcd hdpos,},
    { refine nat.coprime_of_dvd' _,
      intros,
      have : k ∣ (b / d),
      { rw ←nat.pow_dvd_pow_iff hn,
        rw hsoln'',
        apply nat.dvd_sub,
        { rw  ←hsoln,
          refine le_add_right _,
          refl },
        { rw nat.pow_dvd_pow_iff hn, assumption },
        { rw nat.pow_dvd_pow_iff hn, assumption } },
      have : k ∣ nat.gcd (a/d) (b/d),
      { exact nat.dvd_gcd a_1 this ,},
      convert this,
      symmetry,
      change nat.coprime _ _,
      exact coprime_div_gcd_div_gcd' hdpos },
    { refine nat.coprime_of_dvd' _,
      intros,
      have : k ∣ (a / d),
      { rw ←nat.pow_dvd_pow_iff hn,
        rw hsoln',
        apply nat.dvd_sub,
        { rw  ←hsoln,
          refine le_add_left _,
          refl },
        { rw nat.pow_dvd_pow_iff hn, assumption },
        { rw nat.pow_dvd_pow_iff hn, assumption } },
      have : k ∣ nat.gcd (a/d) (b/d),
      { exact nat.dvd_gcd this a_1,},
      convert this,
      symmetry,
      change nat.coprime _ _,
      exact coprime_div_gcd_div_gcd' hdpos },
  },
  { use [a, b, c], unfold flt_coprime, tauto },
end

example (a b : nat) (h : b ≤ a): a - (a - b) = b := nat.sub_sub_self h
example (a b c : nat) (h : b ≤ a) (h' : b ≤ c ): (a + c) - b = a + (c - b) := nat.add_sub_assoc h' a
--example (a b c : nat) (h : b ≤ a) (h' : a-b ≤ a+c ): (a + c) - (a - b) = c+ b := by suggest

lemma nat.pos_pow_iff {b : ℕ} (n : ℕ) (h : 0 < n) : 0 < b ↔ 0 < b ^ n :=
begin
  split,
  apply nat.pos_pow_of_pos,
  rw [nat.pos_iff_ne_zero, nat.pos_iff_ne_zero],
  contrapose!,
  rintro rfl,
  apply nat.zero_pow h,
end
lemma x {m n : ℕ} (h : 0 < n - m) : m < n :=
begin
  exact nat.lt_of_sub_pos h,
end

lemma descent1 (a b c : ℕ)
  (h : flt_coprime a b c 3) :
  ∃ (p q : ℕ),
    0 < p ∧
    0 < q ∧
    p.gcd q = 1 ∧
    (p.even ↔ ¬q.even) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) :=
begin
  sorry,
end

lemma descent11 {a b c d : ℕ} (h : d = a ∨ d = b ∨ d = c) : d ∣ (a * b * c) :=
begin
  rcases h with rfl | rfl | rfl,
  apply dvd_mul_of_dvd_left, apply dvd_mul_right,
  apply dvd_mul_of_dvd_left, apply dvd_mul_left,
  apply dvd_mul_left,
end

lemma descent12 {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
 (h : d = a ∨ d = b ∨ d = c) : d ≤ (a * b * c) :=
begin
  rcases h with rfl | rfl | rfl,
  { conv_lhs { rw ←mul_one d },
    apply nat.mul_le_mul _ hc,
    conv_lhs { rw ←mul_one d },
    apply nat.mul_le_mul_of_nonneg_left hb},
  { conv_lhs { rw ←mul_one d },
    apply nat.mul_le_mul _ hc,
    conv_lhs { rw ←one_mul d },
    apply nat.mul_le_mul_of_nonneg_right ha},
  { conv_lhs { rw ←one_mul d },
    apply nat.mul_le_mul_of_nonneg_right,
    change 0 < _,
    exact mul_pos ha hb },  
end

lemma descent2 (a b c : ℕ)
  (h : flt_coprime a b c 3) :
  ∃ (p q : ℕ),
    0 < p ∧
    0 < q ∧
    p.gcd q = 1 ∧
    (p.even ↔ ¬q.even) ∧
    (2 * p * (p ^ 2 + 3 * q ^ 2) = a ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = b ^ 3 ∨
     2 * p * (p ^ 2 + 3 * q ^ 2) = c ^ 3) ∧
    (2 * p < a ^ 3 * b ^ 3 * c ^ 3) :=
begin
  have := descent1 a b c h,
  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube⟩ := this,
  refine ⟨p, q, hp, hq, hcoprime, hodd, hcube, _⟩,
  have : 1 < (p ^ 2 + 3 * q ^ 2),
  { have : 0 < p ^ 2 := (nat.pos_pow_iff 2 (by norm_num)).mp hp,
    have : 0 < q ^ 2 := (nat.pos_pow_iff 2 (by norm_num)).mp hq,
    linarith },
  have : (2 * p) * 1 < 2 * p * (p ^ 2 + 3 * q ^ 2),
  { refine (mul_lt_mul_left _).mpr this,
    linarith },
  have := descent12 _ _ _ hcube,
  linarith,
  all_goals {
    rw ←nat.pos_pow_iff 3 (by norm_num),
    assumption,
  },

end

/-
lemma nat.pow_lt (a b n : ℕ) (h : 0 < n) : a < b ↔ a ^ n < b ^ n := begin
  split; intro h',
  { induction n,
    {norm_num at h},
    {
    rw pow_succ,
    rw pow_succ,

    apply nat.mul_lt_mul h',
    assumption},
  },

end
-/
lemma nat.pow_lt2 (a b : ℕ) : a < b ↔ a ^ 2 < b ^ 2 := begin
  rw [pow_two, pow_two],
  split,
  { intro h',
    apply nat.mul_lt_mul'; linarith,
  },
  { contrapose!,
    intro h',
    apply nat.mul_le_mul h' h',
  }

end
lemma nat.pow_lt3 (a b : ℕ) : a < b ↔ a ^ 3 < b ^ 3 := begin
  rw pow_succ a,
  rw pow_succ b,
  split,
  { intro h,
    have := (nat.pow_lt2 a b).mp h,
    apply nat.mul_lt_mul'; linarith,
  },
  {
    contrapose!,
    intro h',
    apply nat.mul_le_mul h',
    cases lt_or_eq_of_le h',
    { apply le_of_lt,
      rw ←nat.pow_lt2 b a,
      exact h },
    { subst h },
  }

end

lemma nat.even_pow' {m n : nat} (h : n ≠ 0) : nat.even (m^n) ↔ nat.even m :=
begin
  rw [nat.even_pow], tauto,
end
lemma gcd_eq_of_dvd
  (p q g : ℕ)
  (hp' : g ∣ p) (hq' : g ∣ q)
  (h : ∀ x, x ∣ p → x ∣ q → x ∣ g)
  : nat.gcd p q = g := begin
--    library_search,
    apply nat.dvd_antisymm,
    { apply h,
      exact nat.gcd_dvd_left p q,
      exact nat.gcd_dvd_right p q},
    exact nat.dvd_gcd hp' hq',
  end
  --by library_search
example
  (p q g : ℕ)
  (hp : 0 < p) (hq : 0 < q)
 : ∀ x, x ∣ p → x ∣ q → x ∣ nat.gcd p q := λ x, nat.dvd_gcd

lemma gcd1or3
  (p q : ℕ)
  (hp : 0 < p) (hq : 0 < q)
  (hparity : nat.even p ↔ ¬nat.even q) :
  nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 1 ∨ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 3 :=
begin
  let g := nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2),
  by_cases g = 3,
  { right, assumption },
  left,
  change nat.coprime _ _,
  apply nat.coprime_of_dvd',
  intros d hdleft hdright,
  have : d ≠ 2,
  {
    rintro rfl,
    change nat.even _ at hdright,
    simp [hparity, (dec_trivial : ¬ 2 = 0)] with parity_simps at hdright,
    assumption,
  },

/-

(1) Assume that there is a prime f which divides both 2p and p2 + 3q2.

(2) We know that it can't be 2 since p2 + 3q2 is odd since p,q have opposite parity.

(3) Let's assume that f is greater than 3. So that there exist P,Q such that:
2p = fP, p2 + 3q2 = Qf

(4) Now, f isn't 2 so we know that 2 must divide P so there exists a value H that is half of P and:
p = fH

(5) So combining the two equations, we get:
3q2 = Qf - p2 = Qf - f2H2 = f(Q - fH2)

(6) f doesn't divide 3 since it is greater than 3. So by Euclid's Lemma, it must divide q.

(7) But this contradicts p,q being coprime since it also divides p so we reject our assumption.

-/

--  obtain ⟨d, hd, hdleft, hdright⟩ := nat.prime.not_coprime_iff_dvd.mp h,


--  suffices h : g ≠ 1 → g ≠ 3 → prime g → false,
--  sorry,
/-
  by_cases g = 1,
  { left, assumption },
  right,
  apply gcd_eq_of_dvd,
  have : 3 ∣ g,
  {
    sorry,
  },
  obtain ⟨d, hd, hdleft, hdright⟩ := nat.prime.not_coprime_iff_dvd.mp h,
  have : d ∣ g, exact nat.dvd_gcd hdleft hdright,
  have : d ≠ 2,
  {
    rintro rfl,
    change nat.even _ at hdright,
    simp [hparity, (dec_trivial : ¬ 2 = 0)] with parity_simps at hdright,
    assumption,
  },
-/
/-
  have : ¬nat.even (p ^ 2 + 3 * q ^ 2),
  { simp [hparity, (dec_trivial : ¬ 2 = 0)] with parity_simps },
  have : ¬(2 ∣ (p ^ 2 + 3 * q ^ 2)) := sorry,

  },
  have : ∃ p, nat.prime p ∧ p ∣ g,
  refine nat.exists_prime_and_dvd  _,
  have : ∀ f, f ∣ (2 * p) ∧ f ∣ (p ^ 2 + 3 * q ^ 2) → f ≠ 2,
  sorry,
  have : ¬(2 ∣ g),
  {
    dsimp [g],
  },
-/
  sorry,
end

lemma factors
  (a b f : ℕ)
  (hcoprime : nat.gcd a b = 1)
  (hodd : ¬nat.even f)
  (hfactor : f ∣ (a ^ 2 + 3 * b ^ 2)) :
  ∃ c d, f = c ^ 2 + 3 * d ^ 2 := sorry

example (x y z : ℤ) : (x + y + z) ^ 3 =
  x ^ 3 + y ^ 3 + z ^ 3 + 3 * (x + y) * (x + z) * (y + z)
:= by ring

lemma obscure
  (p q : ℕ)
  (hp : 0 < p) (hq : 0 < q)
  (hcoprime : nat.gcd p q = 1)
  (hparity : nat.even p ↔ ¬nat.even q)
  (hcube : ∃ r, r ^ 3 = p ^ 2 + 3 * q ^ 2) :
  ∃ a b,
    3 * b < a ∧
    p = a ^ 3 - 9 * a * b ^ 2 ∧
    q = 3 * a ^ 2 * b - 3 * b ^ 3 ∧
    nat.gcd a b = 1 ∧
    (nat.even a ↔ ¬nat.even b) :=
begin
  -- (1)
  obtain ⟨u, hu⟩ := hcube,

  -- (2)
  have hodd : ¬nat.even u,
  { rw ←nat.even_pow' (dec_trivial : ¬ 3 = 0),
    rw hu,
    simp [(dec_trivial : ¬ 3 = 0)] with parity_simps,
    tauto },
  
  -- (3)
  have hfactor : u ∣ p ^ 2 + 3 * q ^ 2,
  { rw ←hu,
    refine dvd_pow (dvd_refl u) dec_trivial },
  obtain ⟨a, b, hab⟩ := factors p q u hcoprime hodd hfactor,

  have : (p ^ 2 + 3 * q ^ 2 : ℤ) = (a ^ 3 - 9 * a * b ^ 2) ^ 2 + 3 * (3 * a ^ 2 * b - 3 * b ^ 3) ^ 2,
  {
    zify at hu,
    zify at hab,
    rw [←hu, hab],
--    have A : 9 * a * b ^ 2 ≤ a ^ 3 := sorry, -- (3b)^2 ≤ a ^ 2
--    have B : 3 * b ^ 3 ≤ 3 * a ^ 2 * b := sorry, -- b ^ 2 ≤ a ^ 2
--    zify [A, B],
    ring,
  },

  use [a, b],
  refine ⟨_, _, _, _, _⟩,
  { sorry },


  -- (4)
  have : (a ^ 2 + 3 * b ^ 2) ^ 3 = (a ^ 2 + 3 * b ^ 2) * ((a ^ 2 - 3 * b ^ 2) ^ 2 + 3 * (2 * a * b) ^ 2),
  {
    have : 3 * b ^ 2 ≤ a ^ 2, 
    {sorry},
    zify [this],
    ring,
  },
/-
(4) Now, (a2 + 3b2)3 = (a2 + 3b2)[(a2 - 3b2)2 + 3(2ab)2]

    since (a2 + 3b2)2 = a4 + 6a2b2 + 9b4 =
    = a4 + 12a2b2 - 6a2b2 + 9b4 =
    (a2 - 3b2)2 + 3(2ab)2


(5) And, (a2 + 3b2)[(a2 - 3b2)2 + 3(2ab)2] =
[ a(a2 - 3b2) - 3b(2ab)]2 + 3[a(2ab)+b(a2-3b2)]2 [See here for the proof.]

(6) And: [ a(a2 - 3b2) - 3b(2ab)]2 + 3[a(2ab)+b(a2-3b2)]2 =
= [a3 - 3ab2 - 6ab2]2 + 3(2a2b + a2b - 3b3)2 =
=[a3 -9ab2]2 + 3(3a2b - 3b3)2.


(7) Which combined with step (1) gives us:
p2 + 3q2 = [a3 -9ab2]2 + 3(3a2b - 3b3)2

(8) Which means that we could define a,b such that:
p = a3 -9ab2.
q = 3a2b - 3b3.
gcd(a,b)=1 [since otherwise, any common factor would divide p and q].

(9) We also know that a,b have opposite parities since:

(a) If a,b are both odd, then, p is even since p = odd - odd and q is even since q = odd - odd which is impossible since p,q have opposite parities.

(b) If a,b are both even, then p is even since p = even - even and q is even since q = even - even which is impossible.
-/
  sorry,
end

lemma descent
  (a b c : ℕ)
  (h : flt_coprime a b c 3) :
--  (hpos : 0 < a ∧ 0 < b ∧ 0 < c)
--  (h : a ^ 3 + b ^ 3 = c ^ 3) :
  ∃ a' b' c', 0 < a' ∧ 0 < b' ∧ 0 < c' ∧ (a' * b' * c' < a * b * c) ∧ a' ^ 3 + b' ^ 3 = c' ^ 3 :=
begin
  -- 3.
  have := descent2 a b c h,
  obtain ⟨p, q, hp, hq, hcoprime, hodd, hcube, haaa⟩ := this,
  -- 2.
  obtain ⟨hapos, hbpos, hcpos, h, habcoprime, haccoprime, hbccoprime⟩ := h,
  -- 4.
  have hgcd : nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 1 ∨ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) = 3 := sorry,
  cases hgcd,
  -- 5.
  { have : ∃ s, 2 * p = s ^ 3 := sorry,
    have : ∃ t, p ^ 2 + 3 * q ^ 2 = t ^ 3 := sorry,
    have : ∃ u v,
      3 * v < u ∧
      p = u ^ 3 - 9 * u * v ^ 2 ∧
      q = 3 * u ^ 2 * v - 3 * v ^ 3 ∧
      nat.gcd u v = 1 ∧
      (nat.even u ↔ ¬nat.even v) := sorry,
    obtain ⟨u, v, huv, hp, hq, huvcoprime, huvodd⟩ := this,
    have,
    calc 9 * v ^ 2
        = 3 ^ 2 * v ^ 2 : by norm_num
    ... = (3 * v) ^ 2 : by rw nat.mul_pow,
    have,
    calc u ^ 2 - 9 * v ^ 2
        = u ^ 2 - (3 * v) ^ 2 : by rw this --congr_arg (has_sub.sub (u ^ 2)) (mul_pow 3 v)
    ... = (u + 3 * v) * (u - 3 * v) : nat.sq_sub_sq _ _
    ... = (u - 3 * v) * (u + 3 * v) : mul_comm _ _,
    have hpfactor,
    calc p
        = (u ^ 3 - 9 * u * v ^ 2) : by rw hp
    ... = (u ^ 3 - u * 9 * v ^ 2) : by ring
    ... = (u * u ^ 2 - u * 9 * v ^ 2) : by ring
    ... = (u * u ^ 2 - u * (9 * v ^ 2)) : by ring
    ... = (u * (u ^ 2 - 9 * v ^ 2)) : by rw ←nat.mul_sub_left_distrib
    ... = u * ((u - 3 * v) * (u + 3 * v)) : by rw this
    ... = u * (u - 3 * v) * (u + 3 * v) : by rw mul_assoc u _ _,
    have,
    calc 2 * p
        = 2 * (u * (u - 3 * v) * (u + 3 * v)) : by rw hpfactor
    ... = (2 * u) * (u - 3 * v) * (u + 3 * v) : by ring,
    have : ¬ nat.even (u - 3 * v),
    { rw [nat.even_sub (le_of_lt ‹ 3 * v < u›), nat.even_mul],
      norm_num,
      tauto,
    },
    have : ¬ nat.even (u + 3 * v),
    {
      rw [nat.even_add, nat.even_mul],
      norm_num,
      tauto,
    },
    have : ¬∃ d > 1, d ∣ (2 * u) ∧ d ∣ (u - 3 * v) ∧ d ∣ (u + 3 * v),
    { suffices : ¬∃ d > 1, nat.prime d ∧ d ∣ (2 * u) ∧ d ∣ (u - 3 * v) ∧ d ∣ (u + 3 * v),
      {
        contrapose! this,
        obtain ⟨d', hd'pos, hd'1, hd'2, hd'3⟩ := this,
        refine ⟨nat.min_fac d', _, _, _, _, _⟩,
        { apply lt_of_le_of_ne,
          { rw nat.succ_le_iff, apply nat.min_fac_pos },
          { symmetry, rw [ne.def, nat.min_fac_eq_one_iff], apply ne_of_gt hd'pos },
        },
        {apply nat.min_fac_prime, apply ne_of_gt hd'pos },
        all_goals { transitivity d', apply nat.min_fac_dvd, assumption },
      },
      have : ¬(2 ∣ (2 * u) ∧ 2 ∣ (u - 3 * v) ∧ 2 ∣ (u + 3 * v)),
      { rintro ⟨hd1, hd2, hd3⟩,
        exact ‹¬ nat.even (u - 3 * v)› hd2,
      },
      have : ¬(3 ∣ (2 * u) ∧ 3 ∣ (u - 3 * v) ∧ 3 ∣ (u + 3 * v)),
      { rintro ⟨hd1, hd2, hd3⟩,
        have : 3 ∣ p,
        { rw hpfactor,
          apply dvd_mul_of_dvd_right hd3,
        },
        have : 3 ∣ 2 * p := dvd_mul_of_dvd_right this 2,
        have : 3 ∣ p ^ 2 + 3 * q ^ 2,
        {
          apply nat.dvd_add,
          { rw nat.pow_two, apply dvd_mul_of_dvd_right, assumption, },
          apply dvd_mul_right,
        },
        have : 3 ∣ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) := nat.dvd_gcd ‹_› ‹_›,
        rw hgcd at this,
        have := nat.eq_one_of_dvd_one this,
        norm_num at this,
      },

      rintro ⟨d, hdpos, hdprime, hd1, hd2, hd3⟩,
      have : d ≠ 2,
      { rintro rfl,
        exact ‹¬ nat.even (u - 3 * v)› hd2,
      },
      have : d ≠ 3,
      { rintro rfl,
        have : 3 ∣ p,
        { rw hpfactor,
          apply dvd_mul_of_dvd_right hd3,
        },
        have : 3 ∣ 2 * p := dvd_mul_of_dvd_right this 2,
        have : 3 ∣ p ^ 2 + 3 * q ^ 2,
        {
          apply nat.dvd_add,
          { rw nat.pow_two, apply dvd_mul_of_dvd_right, assumption, },
          apply dvd_mul_right,
        },
        have : 3 ∣ nat.gcd (2 * p) (p ^ 2 + 3 * q ^ 2) := nat.dvd_gcd ‹_› ‹_›,
        rw hgcd at this,
        have := nat.eq_one_of_dvd_one this,
        norm_num at this,
      },
      -- (b) If any odd prime greater than 3 divides a - 3b and a + 3b,
      -- then it must divide a since 2a = a - 3b + a + 3b and
      -- it must divide b since 6b = a + 3b - (a - 3b).
      -- But this is impossible.
      have : d ∣ u,
      { have := (nat.prime.dvd_mul hdprime).mp hd1,
        cases this,
        {
          exfalso,
          have hdposs : 0 < 2 := by linarith,
          have := nat.le_of_dvd hdposs this_1,
          have : d  < 2 := lt_of_le_of_ne ‹_› ‹_›,
          linarith,
        },
        { assumption } },
      have : d ∣ v,
      {
        have : (u - 3 * v) ≤ (u + 3 * v),
        {
          transitivity u,
          exact nat.sub_le u (3 * v),
          exact nat.le.intro rfl,
        },
        have : 2 * 3 * v = (u + 3 * v) - (u - 3 * v),
        { symmetry,
          calc (u + 3 * v) - (u - 3 * v)
              = (3 * v + u) - (u - 3 * v) : by rw add_comm
          ... = 3 * v + (u - (u - 3 * v)) : nat.add_sub_assoc (nat.sub_le u (3 * v)) _
          ... = 3 * v + 3 * v : by rw nat.sub_sub_self (le_of_lt huv)
          ... = (3 + 3) * v : (add_mul _ _ _).symm
          ... = _ : by norm_num,
        },
        have : d ∣ 2 * 3 * v,
        {
          rw this,
          apply nat.dvd_sub ‹(u - 3 * v) ≤ (u + 3 * v)› ‹_› ‹_›,
        },
        have := (nat.prime.dvd_mul hdprime).mp this,
        cases this,
        { rw nat.prime.dvd_mul hdprime at this_1,
          cases this_1;
          {have := (nat.prime_dvd_prime_iff_eq hdprime (by norm_num : nat.prime _)).mp this_1,
          contradiction} },
        {assumption},
      },
      have : d ∣ nat.gcd u v := nat.dvd_gcd ‹_› ‹_›,
      rw huvcoprime at this,
      exact nat.prime.not_dvd_one hdprime this,
    },
    have : ∃ A B C, A ^ 3 = u - 3 * v ∧ B ^ 3 = u + 3 * v ∧ C ^ 3 = 2 * u := sorry,
    obtain ⟨A, B, C, HA, HB, HC⟩ := this, 
    use [A, B, C],
    refine ⟨_, _, _, _, _⟩,
    { rw [nat.pos_pow_iff 3 (by norm_num), HA],
      apply nat.sub_pos_of_lt,
      apply huv },
    { rw [nat.pos_pow_iff 3 (by norm_num), HB],
      rw nat.pos_iff_ne_zero,
      intro H,
      obtain ⟨rfl, HR⟩ := nat.eq_zero_of_add_eq_zero H,
      linarith },
    { rw [nat.pos_pow_iff 3 (by norm_num), HC],
      norm_num,
      rw nat.pos_iff_ne_zero,
      rintro rfl,
      rw nat.gcd_zero_left at huvcoprime,
      subst huvcoprime,
      norm_num at huv,
      },
    { rw nat.pow_lt3,
      iterate 4 {rw mul_pow},
      rw [mul_comm, ←mul_assoc (C^3)],
      rw [HA, HB, HC],
      rw ←‹2 * p = _›,
      assumption },
    { rw [HA, HB, HC],
      zify [le_of_lt huv],
      ring },
  },
  { --descent
    sorry },
end

-- lemma no_solutions' : ∀ x, ¬(∃ y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ x^4 = y^4 + z^2) :=
lemma flt_three
  (a b c : ℕ)
  (hpos : 0 < a ∧ 0 < b ∧ 0 < c) :
  a ^ 3 + b ^ 3 ≠ c ^ 3 :=
begin
  revert a b c,
  suffices h : ∀ k a b c : ℕ, k = a * b * c → (0 < a ∧ 0 < b ∧ 0 < c) → a ^ 3 + b ^ 3 ≠ c ^ 3,
  { intros a b c hpos,
    exact h (a * b * c) a b c rfl hpos },
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
  
/-
  revert a b c,
  suffices h : ∀ k a b c : ℕ, k = a ^ 3 * b ^ 3 * c ^ 3 → (0 < a ∧ 0 < b ∧ 0 < c) → a ^ 3 + b ^ 3 ≠ c ^ 3,
  { intros a b c hpos,
    exact h (a ^ 3 * b ^ 3 * c ^ 3) a b c rfl hpos },
  intro k,
  refine nat.strong_induction_on k _,
  intros k' IH x y z hk hpos H,
-/
/-
  let k' := a ^ 3 * b ^ 3 * c ^ 3,
-/
/-
  rw ne.def,
  revert b c,
  refine nat.strong_induction_on a _,
  intros x IH y z hpos H,
  obtain ⟨x'', y'', z'', hxle, hyle, hzle, hcoprime⟩ := exists_coprime x y z 3 hpos (by norm_num) H,
  obtain ⟨x', y', z', hx'pos, hy'pos, hz'pos, hsmaller, hsolution⟩ := descent x'' y'' z'' hcoprime,
  refine IH x' _ _ _ ⟨hx'pos, hy'pos, hz'pos⟩ hsolution,
--  linarith,
  sorry,
-/
end
