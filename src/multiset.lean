import data.multiset

variables {α : Type*} {β : Type*} {r p : α → β → Prop} {s : multiset α} { t : multiset β}

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

lemma multiset.pow_count [comm_monoid α] (a : α) [decidable_eq α] :
  a ^ (multiset.count a s) = (multiset.filter (eq a) s).prod :=
by rw [multiset.filter_eq, multiset.prod_repeat]

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
    specialize ih (λ x hx, h _ (multiset.mem_cons_of_mem hx)),
    rw [multiset.countp_cons, multiset.countp_cons, ih],
    obtain ⟨h1, h2⟩|⟨h1, h2⟩ := iff_iff_and_or_not_and_not.mp (h a (multiset.mem_cons_self a t));
    simp only [h1, h2, if_congr, if_true, if_false, add_left_inj, eq_self_iff_true] }
end
