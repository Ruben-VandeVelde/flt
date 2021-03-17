import data.multiset

section
variables {α : Type*} {β : Type*} {r p : α → β → Prop} {s : multiset α} { t : multiset β}
lemma multiset.rel.mono'
  (h : ∀(a ∈ s) (b ∈ t), r a b → p a b) (hst : multiset.rel r s t) : multiset.rel p s t :=
begin
  induction hst,
  case rel.zero { exact multiset.rel.zero },
  case rel.cons : a b s t hab hst ih {
    have := h a  (multiset.mem_cons_self _ _) b  (multiset.mem_cons_self _ _) hab,
    apply multiset.rel.cons this,
    apply ih,
    intros a' ha' b' hb' h',
    apply h _ (multiset.mem_cons_of_mem ha') _ (multiset.mem_cons_of_mem hb') h' }
end

lemma multiset.pow_count [comm_monoid α] (a : α) [decidable_eq α] :
  a ^ (multiset.count a s) = (multiset.filter (eq a) s).prod :=
begin
  rw ←multiset.prod_repeat,
  congr,
  symmetry,
  rw multiset.eq_repeat,
  split,
  { rw [←multiset.countp_eq_card_filter],
    refl },
  { intros b hb, 
    exact (multiset.of_mem_filter hb).symm },
end

lemma multiset.prod_nonneg [ordered_comm_semiring α] (f : multiset α) (h : ∀ a ∈ f, (0 : α) ≤ a) : 0 ≤ f.prod :=
begin
  revert h,
  refine f.induction_on _ _,
  { rintro -, simp only [multiset.prod_zero], exact zero_le_one },
  { intros a s hs ih,
    rw multiset.prod_cons,
    apply mul_nonneg,
    { exact ih _ (multiset.mem_cons_self _ _) },
    { apply hs,
      intros a ha,
      exact ih _ (multiset.mem_cons_of_mem ha) } }
end

lemma multiset.nsmul_repeat {a : α} (n m : ℕ) : n •ℕ (multiset.repeat a m) = multiset.repeat a (n * m) :=
begin
  by_cases hn : n = 0,
  { simp only [hn, zero_mul, zero_nsmul, multiset.repeat_zero] },
  rw multiset.eq_repeat,
  simp only [true_and, nat.cast_id, nsmul_eq_mul, multiset.card_repeat, eq_self_iff_true, add_monoid_hom.map_nsmul],
  intros b hb,
  rw multiset.mem_nsmul hn at hb,
  exact multiset.eq_of_mem_repeat hb,
end

-- multiset.count_smul → multiset.count_nsmul

lemma multiset.nsmul_cons (n : ℕ) (a : α) : n •ℕ (a ::ₘ s) = n •ℕ (↑[a]) +  n •ℕ s :=
begin
  induction n with n ih,
  { simp only [add_zero, zero_nsmul] },
  { rw nat.succ_eq_add_one,
    rw [add_nsmul, add_nsmul, one_nsmul, ih],
    rw [add_assoc, add_assoc],
    congr' 1,
    rw [one_nsmul, add_nsmul, one_nsmul, ←multiset.singleton_add],
    rw [add_comm _ s, ←add_assoc, add_comm], }
end
lemma multiset.nsmul_cons' (n : ℕ) (a : α) : n •ℕ (a ::ₘ s) = n •ℕ (a ::ₘ 0) +  n •ℕ s :=
multiset.nsmul_cons n a

lemma multiset.nsmul_filter (n : ℕ)
  (p : α → Prop) [decidable_pred p] :
  multiset.filter p (n •ℕ s) = n •ℕ multiset.filter p s :=
begin
  by_cases hn : n = 0,
  { simp only [hn, multiset.filter_zero, zero_nsmul] },
  refine s.induction_on _ _,
  { simp only [multiset.filter_zero, nsmul_zero] },
  { intros a ha ih,
    by_cases hp : p a,
    { simp only [hp, multiset.filter_cons_of_pos],
      rw multiset.nsmul_cons,
      rw multiset.nsmul_cons,
      rw multiset.filter_add,
      rw ih,
      congr,
      rw multiset.filter_eq_self,
      intros b hb,
      convert hp,
      rwa [multiset.mem_nsmul hn, multiset.mem_coe, list.mem_singleton] at hb },
    { rw [multiset.filter_cons_of_neg _ hp],
      rw multiset.nsmul_cons,
      rw multiset.filter_add,
      rw ih,
      convert zero_add _,
      rw multiset.filter_eq_nil,
      intros b hb,
      convert hp,
      rwa [multiset.mem_nsmul hn, multiset.mem_coe, list.mem_singleton] at hb } }
end

lemma prod_map_multiplicative {M N : Type*} [comm_monoid M] [comm_monoid N] {s : multiset M}
  {f : M → N} (fone : f 1 = 1) (fmul : ∀ a b, f (a * b) = f a * f b) :
  (s.map f).prod = f s.prod := 
begin
  refine multiset.induction_on s _ _,
  { simp only [multiset.prod_zero, fone, multiset.map_zero] },
  { intros a s ih,
    rw [multiset.map_cons, multiset.prod_cons, multiset.prod_cons, fmul, ih] },
end

end

section
variables {α : Type*} {β : Type*} {r p : α → β → Prop} {s : multiset α} { t : multiset β}
lemma multiset.count_map (b : β )
  [decidable_eq β]
  (f : α → β) :
  multiset.count b (s.map f) = multiset.countp (λ x, f x = b) s :=
begin
  refine s.induction_on _ _,
  { simp only [multiset.countp_zero, multiset.count_zero, multiset.map_zero] },
  { intros a ha ih,
    simp only [multiset.map_cons],
    by_cases hb : f a = b,
    { simp only [hb, add_left_inj, multiset.countp_cons_of_pos, multiset.count_cons_self, ih] },
    { rw [multiset.count_cons_of_ne (ne.symm hb)],
      simp only [hb, ih, multiset.countp_cons_of_neg, not_false_iff] } },
end

-- TODO: should be countp_congr?
lemma multiset.countp_eq (p1 p2 : α → Prop)
  [decidable_pred p1] [decidable_pred p2]
  (h : ∀ x ∈ s, p1 x ↔ p2 x) :
  multiset.countp p1 s = multiset.countp p2 s :=
begin
  revert h,
  refine s.induction_on _ _,
  { rintro -, simp only [multiset.countp_zero] },
  { intros a t ih h,
    specialize ih _,
    { intros x hx,
      apply h,
      rw multiset.mem_cons,
      right,
      assumption },
    { by_cases ha1 : p1 a,
      { have ha2 : p2 a,
        { rwa ←h a (multiset.mem_cons_self a t) },
        simp only [ha1, ha2, multiset.countp_cons_of_pos, ih] },
      { have ha2 : ¬p2 a,
        { rwa ←h a (multiset.mem_cons_self a t) },
        rw [multiset.countp_cons_of_neg _ ha1, multiset.countp_cons_of_neg _ ha2, ih] } } }
end

end

section
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {r : γ → δ → Prop}
lemma multiset.rel_map_iff {s : multiset α} {t : multiset β} {f : α → γ} {g : β → δ} :
  multiset.rel r (s.map f) (t.map g) ↔ multiset.rel (λa b, r (f a) (g b)) s t :=
by rw [multiset.rel_map_left, multiset.rel_map_right]
end

lemma multiset.filter_eq
  {α : Type*}
  [decidable_eq α]
  (s : multiset α)
  (b : α) :
  s.filter (eq b) = multiset.repeat b (multiset.count b s) :=
begin
  ext a,
  rw multiset.count_repeat,
  split_ifs with ha,
  { subst a,
    rw multiset.count_filter_of_pos rfl, },
  { rw multiset.count_filter_of_neg (ne.symm ha) }
end

lemma multiset.induction_on_repeat
  {α : Type*}
  [decidable_eq α]
  (s : multiset α)
  (P : multiset α → Prop)
  (h0 : P 0)
  (hnext : ∀ t {a}, a ∈ s → P t → P (t + multiset.repeat a (s.count a))) :
  P s :=
begin
  revert hnext,
  refine s.strong_induction_on _,
  clear s,
  intros s ih hnext,
  by_cases hs : s = 0,
  { simp only [hs, h0] },
  { obtain ⟨b, hb⟩ := multiset.exists_mem_of_ne_zero hs,
    rw ←multiset.filter_add_not (ne b) s,
    simp only [ne.def, not_not, multiset.filter_eq],
    convert hnext (multiset.filter (ne b) s) hb _,
    apply ih,
    { apply lt_of_le_of_ne (multiset.filter_le _ _),
      intro H,
      rw multiset.filter_eq_self at H,
      exact H b hb rfl },
    { intros t a h1 h2,
      rw multiset.count_filter_of_pos (multiset.of_mem_filter h1),
      exact hnext _ (multiset.mem_of_mem_filter h1) h2 } }
end

lemma multiset.exists_nsmul_of_dvd
  {α : Type*}
  [decidable_eq α]
  (s : multiset α)
  (k : ℕ)
  (h : ∀ x ∈ s, k ∣ multiset.count x s) :
  ∃ t : multiset α, s = k •ℕ t :=
begin
  obtain (rfl|hk) := (zero_le k).eq_or_lt,
  { use 0,
    simp only [nsmul_zero],
    apply multiset.eq_zero_of_forall_not_mem,
    intros x hx,
    have := h x hx,
    rw zero_dvd_iff at this,
    rw [←multiset.count_pos, this] at hx,
    exact lt_irrefl 0 hx },
  { refine s.induction_on_repeat _ _ _,
    { use 0, simp only [nsmul_zero, h] },
    { rintros t a ha ⟨u, hu⟩,
      use u + multiset.repeat a (s.count a / k),
      obtain ⟨n, hn⟩ := h a ha,
      rw [nsmul_add, multiset.nsmul_repeat, hu, hn, nat.mul_div_right _ hk] } }
end
