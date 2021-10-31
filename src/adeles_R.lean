import algebraic_geometry.prime_spectrum
import ring_theory.dedekind_domain
import topology.algebra.localization
import topology.algebra.nonarchimedean.adic_topology
import topology.algebra.uniform_ring

noncomputable theory

--TODO : PR
section localization

variables {R : Type*} [comm_ring R] [topological_space R] (M : submonoid R)
lemma localization.continuous : continuous (localization.monoid_of M).to_fun := 
ring_topology.coinduced_continuous _
end localization

open function set
open_locale big_operators

variables (R K : Type*) [integral_domain R] [is_dedekind_domain R] [field K] [algebra R K]
  [is_fraction_ring R K] 

-- Note : not the maximal spectrum if R is a field
def maximal_spectrum := {v : prime_spectrum R // v.as_ideal ≠ 0 }

variable (v : maximal_spectrum R)

instance ts : topological_space R := ideal.adic_topology v.val.as_ideal
instance tr : @topological_ring R (ts R v) _ := infer_instance
instance tg : @topological_add_group R (ts R v) _ := infer_instance
instance us : @uniform_space R := @topological_add_group.to_uniform_space R _ (ts R v) (tg R v)
instance ug : @uniform_add_group R (us R v) _ := 
@topological_add_group_is_uniform R _ (ts R v) (tg R v)

def R_v := @uniform_space.completion R (us R v)
instance R_v.comm_ring : comm_ring (R_v R v) := 
@uniform_space.completion.comm_ring R _ (us R v) (ug R v) (tr R v)
instance : has_lift_t R (@uniform_space.completion R (us R v)) := infer_instance
instance R_v.has_lift_t : has_lift_t R (R_v R v) := uniform_space.completion.has_lift_t R v
instance R_v.uniform_space := @uniform_space.completion.uniform_space R (us R v)
instance R_v.topological_space := 
@uniform_space.to_topological_space (R_v R v) (R_v.uniform_space R v)
instance R_v.topological_ring := 
@uniform_space.completion.top_ring_compl R _ (us R v) (tr R v) (ug R v)

section ufd

variables {α : Type*} [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α]
lemma unique_factorization_monoid.high_pow_not_dvd {a : α} (ha : a ≠ 0) {b : α} (hb : prime b) :
  ∃ n : ℕ, ¬ b^n ∣ a := 
begin
  classical,
  obtain ⟨f, hf⟩ := wf_dvd_monoid.exists_factors a ha,
  use f.card + 1,
  rw ← unique_factorization_monoid.irreducible_iff_prime at hb,
  by_contradiction h_div,
  cases h_div with c hc,
  have hc_ne_zero : c ≠ 0,
  { by_contradiction hc_zero,
    rw not_not at hc_zero,
    rw [hc_zero, mul_zero] at hc,
    exact ha hc },
  obtain ⟨fc, hfc⟩ := wf_dvd_monoid.exists_factors c hc_ne_zero,
  let fbc := (multiset.repeat b (f.card + 1)) + fc,
  have hfbc_card : fbc.card = f.card + 1 + fc.card,
  { rw [multiset.card_add, multiset.card_repeat], },
  have hfbc : (∀ (x : α), x ∈ fbc → irreducible x) ∧ associated fbc.prod a,
  { split,
    { intros x hx,
      rw multiset.mem_add at hx,
      cases hx,
      { rwa (multiset.eq_of_mem_repeat hx) },
      { exact hfc.1 x hx, } },
    { rw [multiset.prod_add, multiset.prod_repeat, hc],
      exact associated.mul_left _ hfc.2 }},
  have h_rel :  multiset.rel associated f fbc,
  { apply unique_factorization_monoid.factors_unique hf.1 hfbc.1,
    exact associated.trans hf.2 (associated.symm hfbc.2) },
  have h_lt : f.card < fbc.card,
  { calc f.card < f.card + 1 : lt_add_one _
            ... ≤ f.card + 1 + fc.card : le_self_add
            ... = fbc.card : by rw hfbc_card },
  exact ne_of_lt h_lt (multiset.card_eq_card_of_rel h_rel),
end

end ufd

instance dedekind_domain.is_Hausdorff : is_Hausdorff v.val.as_ideal R := 
{ haus' := λ x hx, 
  begin
    by_cases hx_zero : x = 0,
    { exact hx_zero },
    { simp_rw [smodeq.zero, algebra.id.smul_eq_mul, ideal.mul_top, ← ideal.dvd_span_singleton] 
        at hx,
      have h_ne_bot : (ideal.span{x}) ≠ ⊥,
      { rw [ne.def, ideal.span_singleton_eq_bot], exact hx_zero},
      obtain ⟨n, hn⟩ := unique_factorization_monoid.high_pow_not_dvd h_ne_bot 
        (ideal.prime_of_is_prime v.property v.val.property),
      exact absurd (hx n) hn }
  end }

instance ss : @separated_space R (us R v) := 
begin
  apply topological_add_group.separated_of_zero_sep,
  intros x hx,
  have : ∃ (n : ℕ), x ∉ v.val.as_ideal^n,
  { by_contradiction h_not_Haus,
    have h_Haus := is_Hausdorff.haus (dedekind_domain.is_Hausdorff R v) x,
    rw not_exists_not at h_not_Haus,
    simp_rw [smodeq.zero, algebra.id.smul_eq_mul, ideal.mul_top] at h_Haus,
    exact hx (h_Haus h_not_Haus) },
  cases this with n hn,
  use (v.val.as_ideal^n : ideal R),
  split,
  { rw filter.has_basis.mem_iff (ideal.has_basis_nhds_zero_adic v.val.as_ideal),
    exact ⟨n, trivial, rfl.subset⟩ },
  { exact hn },
end

def R_hat := (Π (v : maximal_spectrum R), (R_v R v))
instance : comm_ring (R_hat R) := pi.comm_ring

def inj_R_v : R → R_v R v := λ r, by { rw R_v, exact r }
def inj_R : R → (R_hat R) := λ r v, inj_R_v R v r

lemma inj_R_v.injective : injective (inj_R_v R v) :=
begin
  intros x y hxy,
  have h_inj : function.injective (coe : R → (R_v R v)) :=
    @uniform_embedding.inj R _ (us R v) _ coe 
      (@uniform_space.completion.uniform_embedding_coe R (us R v) (ss R v)),
  exact (h_inj) hxy,
end

def diag_R : submonoid (R_hat R) := 
{ carrier  := (inj_R  R) '' set.compl {0},
  one_mem' := ⟨1, set.mem_compl_singleton_iff.mpr one_ne_zero, rfl⟩,
  mul_mem' := 
  begin
    rintros a b ⟨za, hza, rfl⟩ ⟨zb, hzb, rfl⟩,
    use [za*zb, mul_ne_zero hza hzb], 
    ext v,
    exact @uniform_space.completion.coe_mul R _ (us R v) (tr R v) _ _,
  end }

def finite_adele_ring := localization (diag_R R)

instance : comm_ring (finite_adele_ring R) := localization.comm_ring
instance : algebra (R_hat R) (finite_adele_ring R) := localization.algebra
instance : is_localization (diag_R R) (finite_adele_ring R):= localization.is_localization

lemma preimage_diag_R (x : diag_R R) : ∃ r : R, r ≠ 0 ∧ inj_R R r = (x : R_hat R) := x.property

instance ts_frac : topological_space (fraction_ring R) := 
@localization.topological_space R _ (ts R v) _
instance tr_frac : @topological_ring (fraction_ring R) (ts_frac R v) _ := infer_instance
instance tg_frac : @topological_add_group (fraction_ring R) (ts_frac R v) _ := infer_instance
instance us_frac : @uniform_space (fraction_ring R) :=
@topological_add_group.to_uniform_space (fraction_ring R) _ (ts_frac R v) (tg_frac R v)
instance ug_frac : @uniform_add_group (fraction_ring R) (us_frac R v) _ :=
@topological_add_group_is_uniform (fraction_ring R) _ (ts_frac R v) (tg_frac R v)

def K_v : Type* := fraction_ring (R_v R v)
instance K_v.comm_ring : comm_ring (K_v R v) := localization.comm_ring

instance : algebra (R_v R v) (fraction_ring (R_v R v)) := by apply_instance
instance K_v.algebra : algebra (R_v R v) (K_v R v) := fraction_ring.algebra R v 

instance : is_fraction_ring (R_v R v) (fraction_ring (R_v R v)) := by apply_instance
instance K_v.is_fraction_ring : is_fraction_ring (R_v R v) (K_v R v) :=
fraction_ring.is_fraction_ring R v

def K_v.ring_hom : R_v R v  →+* K_v R v := 
(K_v.algebra R v).to_ring_hom

def K_hat := (Π (v : maximal_spectrum R), (K_v R v))
instance K_hat.comm_ring : comm_ring (K_hat R) := pi.comm_ring

def group_hom_prod : add_monoid_hom (R_hat R) (K_hat R) := 
{ to_fun    := (λ x v, (K_v.ring_hom R v) (x v)),
  map_zero' := by { ext v, rw [pi.zero_apply, pi.zero_apply, ring_hom.map_zero] },
  map_add'  := λ x y, by { ext v, rw [pi.add_apply, pi.add_apply, ring_hom.map_add] }}

def hom_prod : ring_hom (R_hat R) (K_hat R)  := 
{ to_fun   := (λ x v, (K_v.ring_hom R v) (x v)),
  map_one' := by { ext v, rw [pi.one_apply, pi.one_apply, ring_hom.map_one] },
  map_mul' := λ x y, by {ext p, rw [pi.mul_apply, pi.mul_apply, ring_hom.map_mul] },
  ..group_hom_prod R}

lemma K_v.ring_hom.injective : injective (K_v.ring_hom R v) :=
begin
  have h_alg_map : (K_v.ring_hom R v) = algebra_map (R_v R v) (K_v R v) := rfl,
  rw h_alg_map, 
  apply is_localization.injective (K_v R v) (rfl.subset),
  exact localization.is_localization,
end

lemma hom_prod.inj : injective (hom_prod R) := 
begin
  rw ring_hom.injective_iff,
  intros r hr,
  rw hom_prod at hr, rw [ring_hom.coe_mk] at hr,
  ext v,
  have h_arg : K_v.ring_hom R v (r v) = K_v.ring_hom R v 0,
  { have : K_v.ring_hom R v (r v) = (λ (v : maximal_spectrum R), K_v.ring_hom R v (r v)) v := rfl,
    rw [this, hr, pi.zero_apply, ring_hom.map_zero], },
  have h_inj : injective (K_v.ring_hom R v) := K_v.ring_hom.injective R v,
  exact h_inj h_arg,
end

lemma integral_domain.mem_non_zero_divisors {r : R} (hr : r ≠ 0) : 
  r ∈ non_zero_divisors R := λ s hs,  or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero hs) hr

lemma image_non_zero_divisors {r : R} (hr : r ∈ non_zero_divisors R) : 
  ((coe : R → R_v R v) r) ∈ non_zero_divisors (R_v R v) := sorry

lemma non_zero_divisor_is_unit {r : R} (hr : r ≠ 0) : is_unit (K_v.ring_hom R v
  ((coe : R → R_v R v) r)) :=
is_localization.map_units (K_v R v) (⟨((coe : R → R_v R v) r),
  (image_non_zero_divisors R v (integral_domain.mem_non_zero_divisors R hr))⟩ :
  non_zero_divisors (R_v R v))

lemma hom_prod_diag_unit : ∀ x : (diag_R R), is_unit (hom_prod R x) :=
begin
  rintro ⟨x, r, hr_compl, hrx⟩,
  rw [compl_eq_compl, mem_compl_eq, mem_singleton_iff] at hr_compl,
  rw [is_unit_iff_exists_inv, subtype.coe_mk, ← hrx],
  use (λ v, localization.mk 1 ⟨((coe : R → R_v R v) r), 
    image_non_zero_divisors R v (integral_domain.mem_non_zero_divisors R hr_compl)⟩),
  ext v,
  rw [hom_prod, ring_hom.coe_mk, pi.mul_apply, pi.one_apply, inj_R],
  dsimp only, rw inj_R_v, dsimp only,
  have h_simp : (K_v.ring_hom R v) ((coe : R → R_v R v) r) = 
    localization.mk ((coe : R → R_v R v) r) 1 := rfl,
  rw [eq_mpr_eq_cast, cast_eq, h_simp, localization.mk_mul, mul_one, one_mul,
    localization.mk_eq_mk', is_localization.mk'_self],
end

def map_to_K_hat (x : finite_adele_ring R) : K_hat R := 
is_localization.lift (hom_prod_diag_unit R) x

lemma restricted_image (x : finite_adele_ring R) : 
  set.finite({ v : maximal_spectrum R | ¬ is_localization.is_integer (R_v R v) (map_to_K_hat R x v)}) := 
begin
  set supp := { v : maximal_spectrum R | ¬ is_localization.is_integer (R_v R v) (map_to_K_hat R x v)} with hsupp,
  obtain ⟨r, d', hx⟩ := is_localization.mk'_surjective (diag_R R) x,
  obtain ⟨d, hd_ne_zero, hd_inj⟩ := d'.property,
  have hd : ideal.span{d} ≠ (0 : ideal R),
  { rw [ideal.zero_eq_bot, ne.def, ideal.span_singleton_eq_bot],
    exact hd_ne_zero, },
  obtain ⟨f, h_irred, h_assoc⟩:= wf_dvd_monoid.exists_factors (ideal.span{d}) hd,
  have hsubset : supp ⊆ { v : maximal_spectrum R | v.val.as_ideal ∣ ideal.span({d})} := sorry,
  apply finite.subset _ hsubset,
  have h_bound := finite.intro (unique_factorization_monoid.fintype_subtype_dvd (ideal.span{d}) hd),
  sorry
end

def finite_adele_ring' :=
{ x : (Π v : (maximal_spectrum R), K_v R v) //
  ∀ᶠ (v : maximal_spectrum R) in filter.cofinite, is_localization.is_integer (R_v R v) (x v) }

lemma restr_add (x y : finite_adele_ring' R) : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  is_localization.is_integer (R_v R v) ((x.val + y.val) v) :=
begin
  cases x with x hx,
  cases y with y hy,
  rw filter.eventually_cofinite at hx hy ⊢,
  have h_subset : {x_1 : maximal_spectrum R | ¬is_localization.is_integer (R_v R x_1)
    (((⟨x, hx⟩ : finite_adele_ring' R).val + (⟨y, hy⟩ : finite_adele_ring' R).val) x_1)} ⊆
    {x_1 : maximal_spectrum R | ¬is_localization.is_integer (R_v R x_1) (x x_1)} ∪
    {x_1 : maximal_spectrum R | ¬is_localization.is_integer (R_v R x_1) (y x_1)},
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq],
    rw mem_set_of_eq at hv,
    by_contradiction h,
    push_neg at h,
    exact hv (is_localization.is_integer_add h.1 h.2),},
  exact finite.subset (finite.union hx hy) h_subset,
end

def add' (x y : finite_adele_ring' R) : finite_adele_ring' R := ⟨x.val + y.val, restr_add R x y⟩

lemma restr_zero : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  is_localization.is_integer (R_v R v) (0 : K_v R v) := 
begin
  rw filter.eventually_cofinite,
  have h_empty : {x : maximal_spectrum R | ¬is_localization.is_integer (R_v R x) (0 : K_v R x)} = ∅,
  { ext v, rw mem_empty_eq, split; intro hv,
    { rw mem_set_of_eq at hv, exact hv (is_localization.is_integer_zero), },
    { exfalso, exact hv }},
  rw h_empty,
  exact finite_empty,
end

lemma restr_neg (x : finite_adele_ring' R) : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  is_localization.is_integer (R_v R v) (-x.val v) := 
begin
  cases x with x hx,
  have h : ∀ (v : maximal_spectrum R), is_localization.is_integer (R_v R v) (-x v) ↔
    is_localization.is_integer (R_v R v) (x v),
  { intro v,
    rw [is_localization.is_integer, is_localization.is_integer],
    simp only [ring_hom.mem_range],
    split; 
    rintro ⟨r, hr⟩; use -r; 
    rw ring_hom.map_neg,
    { exact neg_eq_iff_neg_eq.mp (eq.symm hr) },
    { exact neg_inj.mpr hr }},
  simp_rw h,
  exact hx,
end

def neg' (x : finite_adele_ring' R) : finite_adele_ring' R := ⟨-x.val, restr_neg R x⟩

lemma restr_mul (x y : finite_adele_ring' R) : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  is_localization.is_integer (R_v R v) ((x.val * y.val) v) :=
begin
  cases x with x hx,
  cases y with y hy,
  rw filter.eventually_cofinite at hx hy ⊢,
  have h_subset : {x_1 : maximal_spectrum R | ¬is_localization.is_integer (R_v R x_1)
    (((⟨x, hx⟩ : finite_adele_ring' R).val * (⟨y, hy⟩ : finite_adele_ring' R).val) x_1)} ⊆
    {x_1 : maximal_spectrum R | ¬is_localization.is_integer (R_v R x_1) (x x_1)} ∪
    {x_1 : maximal_spectrum R | ¬is_localization.is_integer (R_v R x_1) (y x_1)},
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq],
    rw mem_set_of_eq at hv,
    by_contradiction h,
    push_neg at h,
    exact hv (is_localization.is_integer_mul h.1 h.2),},
  exact finite.subset (finite.union hx hy) h_subset,
end

lemma restr_one : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  is_localization.is_integer (R_v R v) (1 : K_v R v) := 
begin
  rw filter.eventually_cofinite,
  have h_empty : {x : maximal_spectrum R | ¬is_localization.is_integer (R_v R x) (1 : K_v R x)} = ∅,
  { ext v, rw mem_empty_eq, split; intro hv,
    { rw mem_set_of_eq at hv, exact hv (is_localization.is_integer_one) },
    { exfalso, exact hv }},
  rw h_empty,
  exact finite_empty,
end

instance : add_comm_group (finite_adele_ring' R) := 
{ add          := λ x y, ⟨x.val + y.val, restr_add R x y⟩,
  add_assoc    := λ x y z,
  by { rw [subtype.mk_eq_mk, subtype.val_eq_coe], exact add_assoc _ _ _ },
  zero         := ⟨0, restr_zero R⟩,
  zero_add     := λ x, by { simp_rw [zero_add, subtype.val_eq_coe, subtype.coe_eta] },
  add_zero     := λ x, by { simp_rw [add_zero, subtype.val_eq_coe, subtype.coe_eta] },
  neg          := λ x, ⟨-x.val, restr_neg R x⟩,
  add_left_neg := λ x, by { unfold_projs, simp_rw [subtype.mk_eq_mk, add_left_neg], refl },
  add_comm     := λ x y, by { unfold_projs, simp_rw [subtype.mk_eq_mk, add_comm], }}

instance : comm_ring (finite_adele_ring' R) := {
  mul           := λ x y, ⟨x.val * y.val, restr_mul R x y⟩,
  mul_assoc     := λ x y z,
  by { rw [subtype.mk_eq_mk, subtype.val_eq_coe], exact mul_assoc _ _ _ },
  one           := ⟨1, restr_one R⟩,
  one_mul       := λ x, by { simp_rw [one_mul, subtype.val_eq_coe, subtype.coe_eta] },
  mul_one       := λ x, by { simp_rw [mul_one, subtype.val_eq_coe, subtype.coe_eta] },
  left_distrib  := λ x y z, by {unfold_projs, simp_rw [subtype.mk_eq_mk, left_distrib]},
  right_distrib := λ x y z, by {unfold_projs, simp_rw [subtype.mk_eq_mk, right_distrib]},
  mul_comm      := λ x y, by { unfold_projs, simp_rw [subtype.mk_eq_mk, mul_comm]},
  ..(finite_adele_ring'.add_comm_group R)}

def finite_adele.hom : (finite_adele_ring R) →+* (finite_adele_ring' R) := { to_fun := sorry,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }
  
def finite_adele.inv : (finite_adele_ring' R) →+* (finite_adele_ring R) := { to_fun := sorry,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

lemma finite_adele.hom_inv_id : (finite_adele.inv R).comp (finite_adele.hom R) = ring_hom.id (finite_adele_ring R) := sorry

lemma finite_adele.inv_hom_id : (finite_adele.hom R).comp (finite_adele.inv R) = ring_hom.id (finite_adele_ring' R) := sorry

def finite_adele.eq_defs : ring_equiv (finite_adele_ring R) (finite_adele_ring' R) :=
  ring_equiv.of_hom_inv (finite_adele.hom R) (finite_adele.inv R) (finite_adele.hom_inv_id R) (finite_adele.inv_hom_id R)
