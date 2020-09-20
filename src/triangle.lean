import data.int.basic
import data.int.parity
import data.real.pi

lemma l2 (x y : ℤ) (h : is_coprime x y) :
  gcd (x ^ 2 + y ^ 2) (x ^ 2 - y ^ 2) = 1 ∨
  gcd (x ^ 2 + y ^ 2) (x ^ 2 - y ^ 2) = 2 :=
begin
  obtain ⟨a, b, hab⟩ := h,
  sorry
end

lemma l0 (P : nat → Prop) (h : ∀ m, P m → ∃ k, k < m ∧ P k) (n): ¬ P n := begin
  revert n,
  refine forall_not_of_not_exists _,
  intro hex,
  let S := { x : nat | P x },
  have : S.nonempty := hex,
  let inf := Inf S,
  obtain ⟨inf', hlt, hinf'⟩ := h inf (nat.Inf_mem hex),
  have := nat.not_mem_of_lt_Inf hlt,
  exact this hinf',
end.

--lemma l1 (α : Type*) (f : α → nat) (h: ∀ n, f (n + 1) < f n) : false.

lemma l1 (α : Type*) [nonempty α] (f : α → nat) (h: ∀ a, ∃ b, f b < f a) : false :=
begin
  let inf := infi f,
  have : inf ∈ set.range f,
  {
    apply nat.Inf_mem,
    exact set.range_nonempty f,
  },
  obtain ⟨b, hb⟩ := this,
  obtain ⟨c, hc⟩ := h b,
  rw hb at hc,
  suffices : inf ≤ f c, linarith,
  apply nat.Inf_le,
  exact set.mem_range_self c,
end.

lemma coprime_sq (a b : ℤ) (h : ∃ c, a * b = c ^ 2) (hcoprime : is_coprime a b) :
  ∃ d e, a = d ^ 2 ∧ b = e ^ 2 := sorry

lemma l3 (x y z : ℤ) (h : x ^ 4 - y ^ 4 = z ^ 2) : ∃ x' y' z', x' < x ∧ x' ^ 4 - y' ^ 4 = z' ^ 2 :=
begin
  have coprime : is_coprime x y := sorry, -- WLOG
  have : gcd (x ^ 2 + y ^ 2) (x ^ 2 - y ^ 2) = 1 ∨
         gcd (x ^ 2 + y ^ 2) (x ^ 2 - y ^ 2) = 2 := sorry,
  cases this,
  {
    have is_sq,
    calc (x ^ 2 + y ^ 2) * (x ^ 2 - y ^ 2)
        = x ^ 4 - y ^ 4 : by ring
    ... = z ^ 2 : h,
    have := coprime_sq _ _ ⟨_, is_sq⟩ _,
    swap,
    refine gcd_is_unit_iff.mp _,
    refine is_unit_int.mpr _,
    rw this,
    suggest,
    sorry},
  sorry
end

lemma triangle (x y z : ℤ) : x ^ 4 - y ^ 4 ≠ z ^ 2 :=
begin
  revert x y z,
  suffices : ¬ ∃ (x y z : ℤ), x ^ (4 : ℕ) - y ^ (4 : ℕ) = z ^ (2 : ℕ),
  { push_neg at this,
    apply this,
  },
  intro h,
  obtain ⟨x, y, z, h⟩ := h,

  sorry
end