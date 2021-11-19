import adeles_R

noncomputable theory
open_locale big_operators classical

variables (R : Type) (K : Type) [comm_ring R] [is_domain R] [is_dedekind_domain R] [field K]
  [algebra R K] [is_fraction_ring R K] (v : maximal_spectrum R)

open set function

/-! Finite ideles of R -/
def finite_idele_group' := units (finite_adele_ring' R K)

--instance : topological_space I_Q_f := units.topological_space
instance : group (finite_idele_group' R K) := units.group
--instance : topological_group I_Q_f := units.topological_group

--private def map_val : units K → finite_adele_ring' R K := λ x, inj_K R K x.val
--private def map_inv : units K → finite_adele_ring' R K := λ x, inj_K R K x.inv

lemma right_inv (x : units K) : inj_K R K x.val * inj_K R K x.inv = 1 := 
begin
  rw [← inj_K.map_mul, units.val_eq_coe, units.inv_eq_coe_inv, units.mul_inv],
  exact inj_K.map_one R K
end

lemma left_inv (x : units K) : inj_K R K x.inv * inj_K R K x.val = 1 := 
by rw [mul_comm, right_inv]

def inj_units_K : units K → finite_idele_group' R K := 
λ x, ⟨inj_K R K x.val, inj_K R K x.inv, right_inv R K x, left_inv R K x⟩

@[simp]
lemma inj_units_K.map_one : inj_units_K R K 1 = 1 := 
by {rw inj_units_K, simp only [inj_K.map_one], refl,}

@[simp]
lemma inj_units_K.map_mul (x y : units K) : 
  inj_units_K R K (x*y) = (inj_units_K R K x) * (inj_units_K R K y) := 
begin
  rw inj_units_K, ext v,
  simp_rw [units.val_eq_coe, units.coe_mul, units.coe_mk, inj_K.map_mul],
end

def inj_units_K.group_hom : monoid_hom (units K) (finite_idele_group' R K) := 
{ to_fun    := inj_units_K R K,
  map_one' := inj_units_K.map_one R K,
  map_mul'  := inj_units_K.map_mul R K, }

-- We need to assume that the maximal spectrum of R is nonempty (i.e., R is not a field) for this to
-- work 
lemma inj_units_K.injective [inh : inhabited (maximal_spectrum R)] : 
  injective (inj_units_K.group_hom R K) :=
begin
  rw monoid_hom.injective_iff,
  intros x hx,
  rw [inj_units_K.group_hom, monoid_hom.coe_mk, inj_units_K, ← units.eq_iff, units.coe_mk,
    units.val_eq_coe] at hx,
  rw ← units.eq_iff,
  exact (inj_K.injective R K) hx,
end

lemma prod_val_inv_eq_one (x : finite_idele_group' R K) : 
  (x.val.val v) * (x.inv.val v) = 1  :=
begin
  rw [ ← pi.mul_apply, mul_apply_val, units.val_inv, subtype.val_eq_coe, ← one_def,
    subtype.coe_mk, pi.one_apply],
end

lemma v_comp.ne_zero (x : finite_idele_group' R K) :
  (x.val.val v) ≠ 0 := left_ne_zero_of_mul_eq_one (prod_val_inv_eq_one R K v x)

lemma valuation_val_inv (x : finite_idele_group' R K) :
  (valued.v (x.val.val v)) * (valued.v (x.inv.val v)) = 1 :=
by rw [← valuation.map_mul, prod_val_inv_eq_one, valuation.map_one]

lemma restricted_product (x : finite_idele_group' R K) :
  finite ({ v : maximal_spectrum R | (¬ (x.val.val v) ∈ R_v K v) } ∪ 
    { v : maximal_spectrum R | ¬ (x.inv.val v) ∈ R_v K v }) :=
finite.union x.val.property x.inv.property

lemma finite_exponents (x : finite_idele_group' R K) :
  finite { v : maximal_spectrum R | valued.v (x.val.val v) ≠ 1 } :=
begin
  have h_subset : { v : maximal_spectrum R | valued.v (x.val.val v) ≠ 1 } ⊆ 
  { v : maximal_spectrum R | ¬ (x.val.val v) ∈ R_v K v } ∪ 
  { v : maximal_spectrum R | ¬ (x.inv.val v) ∈ R_v K v },
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq, K_v.is_integer, K_v.is_integer],
    rw mem_set_of_eq at hv,
    cases (lt_or_gt_of_ne hv) with hlt hgt,
    { right,
      have h_one : (valued.v (x.val.val v)) * (valued.v (x.inv.val v)) = 1 :=
      valuation_val_inv R K v x,
      have h_inv : 1 < (valued.v (x.inv.val v)),
      { have hx : (valued.v (x.val.val v)) ≠ 0,
        { rw [valuation.ne_zero_iff],
          exact left_ne_zero_of_mul_eq_one (prod_val_inv_eq_one R K v x),},
        rw mul_eq_one_iff_inv_eq₀ hx at h_one,
        rw [← h_one, ← with_zero.inv_one, inv_lt_inv₀ (ne.symm zero_ne_one) hx],
        exact hlt, },
      exact not_le.mpr h_inv,},
    { left, exact not_le.mpr hgt, }},
  exact finite.subset (restricted_product R K x) h_subset,
end

def with_zero.to_integer {x : with_zero (multiplicative ℤ )} (hx : x ≠ 0) : ℤ :=
multiplicative.to_add (classical.some (with_zero.ne_zero_iff_exists.mp hx))

def finite_idele.to_add_valuations (x : finite_idele_group' R K) : Π (v : maximal_spectrum R), ℤ :=
λ v, -(with_zero.to_integer ((valuation.ne_zero_iff valued.v).mpr (v_comp.ne_zero R K v x)))

lemma finite_idele.to_add_valuations.map_one : 
  finite_idele.to_add_valuations R K (1 : finite_idele_group' R K) = 
    λ (v : maximal_spectrum R), (0 : ℤ) :=
begin
  rw finite_idele.to_add_valuations,
  ext v,
  rw [with_zero.to_integer, ← to_add_one, ← to_add_inv],
  apply congr_arg multiplicative.to_add,
  rw [inv_eq_one, ← with_zero.coe_inj, classical.some_spec
  (with_zero.to_integer._proof_1 (finite_idele.to_add_valuations._proof_1 R K 1 v))],
  exact valuation.map_one _,
end

lemma finite_idele.to_add_valuations.map_mul (x y : finite_idele_group' R K) : 
finite_idele.to_add_valuations R K (x * y) = 
(finite_idele.to_add_valuations R K x) + (finite_idele.to_add_valuations R K y) :=
begin
  rw [finite_idele.to_add_valuations, finite_idele.to_add_valuations, 
    finite_idele.to_add_valuations],
  ext v,
  simp only [pi.add_apply],
  rw [← neg_add, neg_inj, with_zero.to_integer, with_zero.to_integer, with_zero.to_integer,
    ← to_add_mul],
  apply congr_arg,
  rw [← with_zero.coe_inj, with_zero.coe_mul,
    classical.some_spec (with_zero.to_integer._proof_1 _),
    classical.some_spec (with_zero.to_integer._proof_1 _),
    classical.some_spec (with_zero.to_integer._proof_1 _)],
  exact valuation.map_mul valued.v _ _,
end

lemma finite_support (x : finite_idele_group' R K ) : (mul_support (λ (v : maximal_spectrum R), 
  (v.val.as_ideal : 
    fractional_ideal (non_zero_divisors R) K) ^ finite_idele.to_add_valuations R K x v)).finite
:= 
begin
  have h_subset :
    {v : maximal_spectrum R | (v.val.as_ideal : fractional_ideal (non_zero_divisors R) K) ^ 
      finite_idele.to_add_valuations R K x v ≠ 1} ⊆
    { v : maximal_spectrum R | valued.v (x.val.val v) ≠ 1 },
  { intros v,
    rw mem_set_of_eq, rw mem_set_of_eq,
    contrapose!,
    intro hv,
    suffices : finite_idele.to_add_valuations R K x v = 0,
    { rw this, exact zpow_zero _ },
    rw finite_idele.to_add_valuations,
    simp only [with_zero.to_integer],
    rw [← to_add_one, ← to_add_inv],
    apply congr_arg,
    rw [inv_eq_one, ← with_zero.coe_inj, classical.some_spec (with_zero.to_integer._proof_1 _)],
    exact hv, },
  exact finite.subset (finite_exponents R K x) h_subset,
end

lemma finite_support' (x : finite_idele_group' R K ) : (mul_support (λ (v : maximal_spectrum R), 
  (v.val.as_ideal : 
    fractional_ideal (non_zero_divisors R) K) ^ -finite_idele.to_add_valuations R K x v)).finite
:= 
begin
  have h : {v : maximal_spectrum R | (v.val.as_ideal : fractional_ideal (non_zero_divisors R) K) ^ 
    -finite_idele.to_add_valuations R K x v ≠ 1} =
    {v : maximal_spectrum R | (v.val.as_ideal : fractional_ideal (non_zero_divisors R) K) ^ 
      finite_idele.to_add_valuations R K x v ≠ 1},
  { ext v,
    rw [mem_set_of_eq, mem_set_of_eq, ne.def, ne.def, zpow_neg₀, inv_eq_one₀], },
  rw [mul_support, h],
  exact finite_support R K x,
end

def map_to_fractional_ideals.val :
  (finite_idele_group' R K) → (fractional_ideal (non_zero_divisors R) K) := λ x,
∏ᶠ (v : maximal_spectrum R), (v.val.as_ideal : fractional_ideal (non_zero_divisors R) K)^
  (finite_idele.to_add_valuations R K x v)
  
def map_to_fractional_ideals.inv :
  (finite_idele_group' R K) → (fractional_ideal (non_zero_divisors R) K) := λ x,
∏ᶠ (v : maximal_spectrum R), (v.val.as_ideal : fractional_ideal (non_zero_divisors R) K)^
  (-finite_idele.to_add_valuations R K x v)

def map_to_fractional_ideals' : monoid_hom
  (finite_idele_group' R K)  (fractional_ideal (non_zero_divisors R) K) := 
  { to_fun := map_to_fractional_ideals.val R K, 
  map_one' := begin
    rw map_to_fractional_ideals.val,
    simp_rw [finite_idele.to_add_valuations.map_one, zpow_zero, finprod_one],
  end,
  map_mul' := λ x y,
  begin
    rw map_to_fractional_ideals.val, 
    dsimp only,
    rw finite_idele.to_add_valuations.map_mul,
    simp_rw pi.add_apply,
    rw ← finprod_mul_distrib (finite_support R K x) (finite_support R K y),
    apply finprod_congr,
    intro v,
    rw zpow_add₀,
    { rw [ne.def, fractional_ideal.coe_ideal_eq_zero_iff],
      exact v.property },
  end}

lemma finite_idele.to_add_valuations.mul_inv (x : finite_idele_group' R K): 
  map_to_fractional_ideals.val R K x * map_to_fractional_ideals.inv R K x = 1 := 
begin
  rw [map_to_fractional_ideals.val, map_to_fractional_ideals.inv],
  dsimp only,
  rw ← finprod_mul_distrib (finite_support R K x) (finite_support' R K x),
  rw ← finprod_one,
  apply finprod_congr ,
  intro v,
  rw ← zpow_add₀,
  rw [add_right_neg, zpow_zero],
  { rw [ne.def, fractional_ideal.coe_ideal_eq_zero_iff],
      exact v.property },
end

lemma finite_idele.to_add_valuations.inv_mul (x : finite_idele_group' R K): 
  map_to_fractional_ideals.inv R K x * map_to_fractional_ideals.val R K x = 1 := 
begin
  rw mul_comm,
  exact finite_idele.to_add_valuations.mul_inv R K x,
end

def map_to_fractional_ideals.def :
  (finite_idele_group' R K) → (units (fractional_ideal (non_zero_divisors R) K)) := λ x,
⟨map_to_fractional_ideals.val R K x, map_to_fractional_ideals.inv R K x, 
  finite_idele.to_add_valuations.mul_inv R K x, finite_idele.to_add_valuations.inv_mul R K x⟩

def map_to_fractional_ideals : monoid_hom
  (finite_idele_group' R K)  (units (fractional_ideal (non_zero_divisors R) K)) := 
{ to_fun := map_to_fractional_ideals.def R K,
map_one' := by {
  rw map_to_fractional_ideals.def,
  dsimp only,
  rw [← units.eq_iff, units.coe_mk, units.coe_one, map_to_fractional_ideals.val],
  simp_rw [finite_idele.to_add_valuations.map_one, zpow_zero, finprod_one],
},
map_mul' := λ x y,
begin
  rw map_to_fractional_ideals.def, 
  dsimp only,
  rw [← units.eq_iff, units.coe_mul, units.coe_mk, units.coe_mk, units.coe_mk],
  rw map_to_fractional_ideals.val, dsimp only,
  rw finite_idele.to_add_valuations.map_mul,
  simp_rw pi.add_apply,
  rw ← finprod_mul_distrib (finite_support R K x) (finite_support R K y),
  apply finprod_congr,
  intro v,
  rw zpow_add₀,
  { rw [ne.def, fractional_ideal.coe_ideal_eq_zero_iff],
    exact v.property },
end}

theorem associates.count_ne_zero_iff_dvd {α : Type*} [comm_cancel_monoid_with_zero α]
  [dec_irr : Π (p : associates α), decidable (irreducible p)] [unique_factorization_monoid α] 
  [nontrivial α] [dec : decidable_eq α] {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) :
  (associates.mk p).count (associates.mk a).factors ≠ 0 ↔ p ∣ a :=
begin
  rw ← associates.mk_le_mk_iff_dvd_iff,
  split; intro h,
  { exact associates.le_of_count_ne_zero (associates.mk_ne_zero.mpr ha0) 
    ((associates.irreducible_mk p).mpr hp) h, },
  { rw [← pow_one (associates.mk p), associates.prime_pow_dvd_iff_le
    (associates.mk_ne_zero.mpr ha0)  ((associates.irreducible_mk p).mpr hp)] at h,
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one h), }
end

variables {R K}
lemma associates.finite_factors (I : ideal R) (hI : I ≠ 0) :
  ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  ((associates.mk v.val.as_ideal).count (associates.mk I).factors : ℤ) = 0 :=
begin
  have h_supp : {v : maximal_spectrum R |
    ¬((associates.mk v.val.as_ideal).count (associates.mk I).factors : ℤ) = 0} =
    { v : maximal_spectrum R | v.val.as_ideal ∣ I },
  { ext v,
    rw mem_set_of_eq, rw mem_set_of_eq,
    rw [int.coe_nat_eq_zero, subtype.val_eq_coe],
    exact associates.count_ne_zero_iff_dvd hI (ideal.irreducible_of_maximal v),},
  rw [filter.eventually_cofinite, h_supp],
  exact ideal.finite_factors I hI,
end

lemma val_property {a : Π v : maximal_spectrum R, K_v K v}
  (ha : ∀ᶠ v : maximal_spectrum R in filter.cofinite, valued.v (a v) = 1)
  (h_ne_zero : ∀ v : maximal_spectrum R, a v ≠ 0) :
  ∀ᶠ v : maximal_spectrum R in filter.cofinite, a v ∈ R_v K v :=
begin
  rw filter.eventually_cofinite at ha ⊢,
  simp_rw K_v.is_integer,
  have h_subset : {x : maximal_spectrum R | ¬valued.v (a x) ≤ 1} ⊆ 
    {x : maximal_spectrum R | ¬valued.v (a x) = 1},
  { intros v hv,
    exact ne_of_gt (not_le.mp hv), },
  exact finite.subset ha h_subset,
end

lemma inv_property {a : Π v : maximal_spectrum R, K_v K v}
  (ha : ∀ᶠ v : maximal_spectrum R in filter.cofinite, valued.v (a v) = 1)
  (h_ne_zero : ∀ v : maximal_spectrum R, a v ≠ 0) :
  ∀ᶠ v : maximal_spectrum R in filter.cofinite, (a v)⁻¹ ∈ R_v K v :=
begin
  rw filter.eventually_cofinite at ha ⊢,
  simp_rw [K_v.is_integer, not_le],
  have h_subset : {x : maximal_spectrum R | 1 < valued.v (a x)⁻¹} ⊆ 
    {x : maximal_spectrum R | ¬valued.v (a x) = 1},
  { intros v hv,
    rw [mem_set_of_eq, valuation.map_inv] at hv ,
    rw [mem_set_of_eq, ← inv_inj₀, inv_one],
    exact ne_of_gt hv, },
  exact finite.subset ha h_subset,
end

lemma right_inv' {a : Π v : maximal_spectrum R, K_v K v}
  (ha : ∀ᶠ v : maximal_spectrum R in filter.cofinite, valued.v (a v) = 1)
  (h_ne_zero : ∀ v : maximal_spectrum R, a v ≠ 0)  :
  (⟨a, val_property ha h_ne_zero⟩ : finite_adele_ring' R K) *
  ⟨(λ v : maximal_spectrum R, (a v)⁻¹), inv_property ha h_ne_zero⟩ = 1 := 
begin
  ext v,
  unfold_projs,
  simp only [mul'],
  rw [subtype.coe_mk, subtype.coe_mk, pi.mul_apply, if_neg (h_ne_zero v)],
  apply mul_hat_inv_cancel,
  exact h_ne_zero v,
end

lemma left_inv' {a : Π v : maximal_spectrum R, K_v K v}
  (ha : ∀ᶠ v : maximal_spectrum R in filter.cofinite, valued.v (a v) = 1)
  (h_ne_zero : ∀ v : maximal_spectrum R, a v ≠ 0) :
  (⟨(λ v : maximal_spectrum R, (a v)⁻¹), inv_property ha h_ne_zero⟩ : finite_adele_ring' R K) *
  ⟨a, val_property ha h_ne_zero⟩ = 1 := 
by { rw mul_comm, exact right_inv' ha h_ne_zero}

def prod_to_idele (a : Π v : maximal_spectrum R, K_v K v)
  (ha : ∀ᶠ v : maximal_spectrum R in filter.cofinite, valued.v (a v) = 1)
  (h_ne_zero : ∀ v : maximal_spectrum R, a v ≠ 0) :
  finite_idele_group' R K :=
⟨⟨a, val_property ha h_ne_zero⟩, ⟨(λ v : maximal_spectrum R, (a v)⁻¹), inv_property ha h_ne_zero⟩,
    right_inv' ha h_ne_zero, left_inv' ha h_ne_zero⟩


lemma idele.finite_mul_support (I : ideal R) (hI : I ≠ 0):
  (mul_support (λ (v : maximal_spectrum R), 
  (v.val.as_ideal : fractional_ideal (non_zero_divisors R) K)^
  ((associates.mk v.val.as_ideal).count (associates.mk I).factors : ℤ))).finite := 
begin
  have h_subset : {v : maximal_spectrum R | 
    (v.val.as_ideal : fractional_ideal (non_zero_divisors R) K) ^
    ((associates.mk v.val.as_ideal).count (associates.mk I).factors : ℤ) ≠ 1} ⊆ 
    {v : maximal_spectrum R | 
    ((associates.mk v.val.as_ideal).count (associates.mk I).factors : ℤ) ≠ 0},
  { intros v hv,
    rw mem_set_of_eq at hv ⊢,
    intro h_zero,
    have hv' : (v.val.as_ideal : fractional_ideal (non_zero_divisors R) K)^
      ((associates.mk v.val.as_ideal).count (associates.mk I).factors : ℤ) = 1,
    { rw [h_zero, zpow_zero _],},
    exact hv hv', },
  exact finite.subset (filter.eventually_cofinite.mp (associates.finite_factors I hI)) h_subset,
end

lemma idele.finite_mul_support' (I : ideal R) (hI : I ≠ 0):
  (mul_support (λ (v : maximal_spectrum R), 
  v.val.as_ideal^(associates.mk v.val.as_ideal).count (associates.mk I).factors)).finite := 
begin
  have h_subset : {v : maximal_spectrum R | 
    v.val.as_ideal^
    (associates.mk v.val.as_ideal).count (associates.mk I).factors ≠ 1} ⊆ 
    {v : maximal_spectrum R | 
    ((associates.mk v.val.as_ideal).count (associates.mk I).factors : ℤ) ≠ 0},
  { intros v hv,
    rw mem_set_of_eq at hv ⊢,
    intro h_zero,
    rw int.coe_nat_eq_zero at h_zero,
    have hv' : v.val.as_ideal^
      (associates.mk v.val.as_ideal).count (associates.mk I).factors = 1,
    { rw [h_zero, pow_zero _],},
    exact hv hv', },
  exact finite.subset (filter.eventually_cofinite.mp (associates.finite_factors I hI)) h_subset,
end

lemma idele.finite_mul_support_inv (I : ideal R) (hI : I ≠ 0):
  (mul_support (λ (v : maximal_spectrum R), 
  (v.val.as_ideal : fractional_ideal (non_zero_divisors R) K)^
  -((associates.mk v.val.as_ideal).count (associates.mk I).factors : ℤ))).finite := 
begin
  rw mul_support, 
  simp_rw [zpow_neg₀, ne.def, inv_eq_one₀],
  exact idele.finite_mul_support I hI,
end

lemma map_to_fractional_ideals.inv_eq_inv (x : finite_idele_group' R K) (I : units (fractional_ideal (non_zero_divisors R) K))
  (hxI : map_to_fractional_ideals.val R K (x) = I.val) : 
  map_to_fractional_ideals.inv R K (x) = I.inv := 
begin
  have h_inv : I.val * (map_to_fractional_ideals.inv R K (x)) = 1,
  { rw ← hxI, exact finite_idele.to_add_valuations.mul_inv R K _ },
  exact eq_comm.mp (units.inv_eq_of_mul_eq_one h_inv),
end

lemma fractional_ideal.factor_ne_zero {I : fractional_ideal (non_zero_divisors R) K} {a: R}
  {J: ideal R} (hI_ne_zero : I ≠ 0) 
  (haJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  J ≠ 0 :=
begin
  by_contradiction hJ_zero,
  rw [hJ_zero, ideal.zero_eq_bot, fractional_ideal.coe_to_fractional_ideal_bot, mul_zero] at haJ,
  exact hI_ne_zero haJ,
end

lemma associates.factors_eq_none_iff_zero {α : Type*} [comm_cancel_monoid_with_zero α] 
  [unique_factorization_monoid α] [nontrivial α] [dec : decidable_eq α]
  [dec' : decidable_eq (associates α)] {a : associates α} : 
  a.factors = option.none ↔ a = 0 :=
begin
  split; intro h,
    { rw [← associates.factors_prod a, associates.factor_set.prod_eq_zero_iff], exact h,},
    { rw h, exact associates.factors_0 }
end

lemma associates.factors_eq_some_iff_ne_zero {α : Type*} [comm_cancel_monoid_with_zero α] 
  [unique_factorization_monoid α] [nontrivial α] [dec : decidable_eq α]
  [dec' : decidable_eq (associates α)] {a : associates α} : 
  (∃ (s : multiset {p : associates α // irreducible p}), a.factors = some s) ↔ a ≠ 0 :=
begin
  rw [← option.is_some_iff_exists, ← option.ne_none_iff_is_some, ne.def, ne.def,
    associates.factors_eq_none_iff_zero],
end

lemma associates.eq_factors_of_eq_counts {α : Type*} [comm_cancel_monoid_with_zero α] 
  [unique_factorization_monoid α] [nontrivial α] [dec : decidable_eq α]
  [dec' : decidable_eq (associates α)]{a b : associates α} (ha : a ≠ 0) (hb : b ≠ 0)
  (h :  ∀ (p : associates α) (hp : irreducible p), p.count a.factors = p.count b.factors) :
  a.factors = b.factors := 
begin
  obtain ⟨sa, h_sa⟩ := associates.factors_eq_some_iff_ne_zero.mpr ha,
  obtain ⟨sb, h_sb⟩ := associates.factors_eq_some_iff_ne_zero.mpr hb,
  rw [h_sa, h_sb] at h ⊢,
  rw option.some_inj,
  have h_count :  ∀ (p : associates α) (hp : irreducible p), sa.count ⟨p, hp⟩ = sb.count ⟨p, hp⟩,
  { intros p hp, rw [← associates.count_some, ← associates.count_some, h p hp], },
  apply multiset.to_finsupp.injective,
  ext ⟨p, hp⟩,
  rw [multiset.to_finsupp_apply, multiset.to_finsupp_apply, h_count p hp],
end

theorem associates.eq_of_eq_counts {α : Type*} [comm_cancel_monoid_with_zero α] [nontrivial α]
  [unique_factorization_monoid α] [dec : decidable_eq α] [dec' : decidable_eq (associates α)]
  {a b : associates α} (ha : a ≠ 0) (hb  : b ≠ 0)
  (h :  ∀ (p : associates α), irreducible p → p.count a.factors = p.count b.factors) : a = b := 
associates.eq_of_factors_eq_factors (associates.eq_factors_of_eq_counts ha hb h)


lemma finprod_mem_dvd' {α : Type*} {N : Type*} [comm_monoid N] {f : α → N} (a : α)
  (hf : finite (mul_support f)) :
  f a * (∏ᶠ i ∈ (mul_support f) \ {a}, f i) = ∏ᶠ i, f i  := 
begin
  sorry
end

lemma prime.exists_mem_finprod_dvd {α : Type*} {N : Type*} [comm_monoid_with_zero N] {f : α → N} 
  {p : N} (hp : prime p) (hf : finite (mul_support f)) :
  p ∣  ∏ᶠ i, f i →  ∃ (a : α), p ∣ f a := 
begin
  rw finprod_eq_prod _ hf,
  intro h,
  obtain ⟨a, -, ha_dvd⟩ := prime.exists_mem_finset_dvd hp h,
  exact ⟨a, ha_dvd⟩,
end

lemma ideal.finprod_not_dvd (I : ideal R) (hI : I ≠ 0) : 
¬ (v.val.as_ideal)^
  ((associates.mk v.val.as_ideal).count (associates.mk I).factors + 1) ∣
    (∏ᶠ (v : maximal_spectrum R), (v.val.as_ideal)^
      (associates.mk v.val.as_ideal).count (associates.mk I).factors) :=
begin
  have h_ne_zero : v.val.as_ideal ^
    (associates.mk v.val.as_ideal).count (associates.mk I).factors ≠ 0,
  { apply pow_ne_zero _ v.property, },

  have h_dvd := finprod_mem_dvd' v (idele.finite_mul_support' I hI),
  simp only [mem_singleton_iff, mem_mul_support, ne.def, mem_diff] at h_dvd,
  rw ← h_dvd,
  rw pow_add, rw pow_one,
  intro h_contr,
  rw mul_dvd_mul_iff_left h_ne_zero at h_contr,
  have hv_prime : prime v.val.as_ideal := ideal.prime_of_is_prime v.property v.val.property,

  have h_finite : finite (mul_support (λ (v : maximal_spectrum R), v.val.as_ideal^
    (associates.mk v.val.as_ideal).count (associates.mk I).factors) \ {v}),
  { apply finite.subset (idele.finite_mul_support' I hI) (diff_subset _ _), },
  rw finprod_mem_eq_finite_to_finset_prod _ h_finite at h_contr,
  obtain ⟨w, hw, hvw'⟩ := prime.exists_mem_finset_dvd hv_prime h_contr,
  have hw_prime : prime w.val.as_ideal := ideal.prime_of_is_prime w.property w.val.property,
  rw [finite.mem_to_finset, mem_diff, mem_singleton_iff] at hw,
  dsimp only at hvw',
  have hvw := prime.dvd_of_dvd_pow hv_prime hvw',
  rw prime.dvd_prime_iff_associated hv_prime hw_prime at hvw,
  rw associated_iff_eq at hvw,
  have hv' : v.val.as_ideal = v.val.val := rfl,
  have hw' : w.val.as_ideal = w.val.val := rfl,
  rw [hv', hw', subtype.val_eq_coe, subtype.val_eq_coe, subtype.val_eq_coe, subtype.val_eq_coe]
    at hvw,
  exact hw.2 (eq.symm (subtype.coe_injective(subtype.coe_injective hvw))),
end

lemma ideal.finprod_count (I : ideal R) (hI : I ≠ 0) :
(associates.mk v.val.as_ideal).count (associates.mk (∏ᶠ (v : maximal_spectrum R), (v.val.as_ideal)^
    (associates.mk v.val.as_ideal).count (associates.mk I).factors)).factors = 
    (associates.mk v.val.as_ideal).count (associates.mk I).factors :=
begin
  have h_ne_zero : associates.mk (∏ᶠ (v : maximal_spectrum R), v.val.as_ideal ^ 
    (associates.mk v.val.as_ideal).count (associates.mk I).factors) ≠ 0,
  { rw associates.mk_ne_zero, sorry},
  have hv : irreducible (associates.mk v.val.as_ideal) := associates.irreducible_of_maximal v,
  have h_dvd : (v.val.as_ideal)^(associates.mk v.val.as_ideal).count (associates.mk I).factors ∣
    (∏ᶠ (v : maximal_spectrum R), (v.val.as_ideal)^
      (associates.mk v.val.as_ideal).count (associates.mk I).factors) :=
  finprod_mem_dvd _ (idele.finite_mul_support' I hI),
  have h_not_dvd : ¬ (v.val.as_ideal)^
  ((associates.mk v.val.as_ideal).count (associates.mk I).factors + 1) ∣
    (∏ᶠ (v : maximal_spectrum R), (v.val.as_ideal)^
      (associates.mk v.val.as_ideal).count (associates.mk I).factors) := sorry,
  rw ← associates.mk_dvd_mk at h_dvd h_not_dvd,
  rw associates.dvd_eq_le at h_dvd h_not_dvd,
  rw associates.mk_pow at h_dvd h_not_dvd,
  rw associates.prime_pow_dvd_iff_le h_ne_zero hv at h_dvd h_not_dvd,
  rw not_le at h_not_dvd,
  exact nat.eq_of_le_of_lt_succ h_dvd h_not_dvd,
end

lemma ideal.factorization (I : ideal R) (hI : I ≠ 0) :
  ∏ᶠ (v : maximal_spectrum R), (v.val.as_ideal)^
    (associates.mk v.val.as_ideal).count (associates.mk I).factors = I := 
begin
  rw ← associated_iff_eq,
  rw ← associates.mk_eq_mk_iff_associated,
  apply associates.eq_of_eq_counts,
  sorry,
  sorry,
  intros v hv,
  /- by_cases hv_zero : v = 0,
  { rw hv_zero, 
    have : (associates.mk 0).count (associates.mk I).factors = 0,
    { sorry,},
    sorry,
  }, -/
  { obtain ⟨J, hJv⟩ := associates.exists_rep v,
    --obtain ⟨J, hJ_ne_zero, hJv⟩ := associates.exists_non_zero_rep hv_zero,
    rw ← hJv at hv,
    rw associates.irreducible_mk at hv,
    have hJ_ne_zero : J ≠ 0 := irreducible.ne_zero hv,
    rw unique_factorization_monoid.irreducible_iff_prime at hv,
    rw ← hJv,
    --set w : maximal_spectrum R := ⟨⟨J, ideal.is_prime_of_prime hv⟩, hJ_ne_zero⟩,
    /- have : J = w.val.as_ideal := rfl,
    rw this, -/
    apply ideal.finprod_count ⟨⟨J, ideal.is_prime_of_prime hv⟩, hJ_ne_zero⟩ I hI,},
end
--set_option profiler true
lemma map_to_fractional_ideals.surjective : surjective (map_to_fractional_ideals R K) :=
begin
  rintro ⟨I, I_inv, hval_inv, hinv_val⟩,
  obtain ⟨a, J, ha, haJ⟩ := fractional_ideal.exists_eq_span_singleton_mul I,
  set a_val := λ v : maximal_spectrum R, 
    ((associates.mk v.val.as_ideal).count (associates.mk (ideal.span{a} : ideal R)).factors : ℤ)
    with ha_val,
  set J_val := λ v : maximal_spectrum R, 
    ((associates.mk v.val.as_ideal).count (associates.mk J).factors : ℤ) with hJ_val,
  set unif  := λ v : maximal_spectrum R, (coe : K → (K_v K v))
    (classical.some (adic_valuation.exists_uniformizer K v)) with h_unif,
  set ad := λ v : maximal_spectrum R,
    (unif v)^(J_val v - a_val v) with h_ad,
  have had_unit : ∀ᶠ v : maximal_spectrum R in filter.cofinite, valued.v (ad v) = 1 := sorry,
  have h_ne_zero : ∀ v : maximal_spectrum R, ad v ≠ 0 := sorry,
  use prod_to_idele ad had_unit h_ne_zero,

  rw map_to_fractional_ideals,
  simp only [map_to_fractional_ideals.def, monoid_hom.coe_mk],
  have ha_prod : fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ = 
    ∏ᶠ (v : maximal_spectrum R), ↑(v.val.as_ideal)^(-a_val v) := sorry,
  have hJ_prod : (J : fractional_ideal (non_zero_divisors R) K) = 
    ∏ᶠ (v : maximal_spectrum R), ↑(v.val.as_ideal)^(J_val v) := sorry,
  have H : map_to_fractional_ideals.val R K (prod_to_idele ad had_unit h_ne_zero) = I,
  { simp only [map_to_fractional_ideals.val, finite_idele.to_add_valuations],
    rw [haJ, ha_prod, hJ_prod],
    simp_rw with_zero.to_integer,
    rw ← finprod_mul_distrib,
    apply finprod_congr,
    intro v,
    rw ← zpow_add₀ ((@fractional_ideal.coe_ideal_ne_zero_iff R _ K _ _ _ _).mpr v.property),
    have hv : valued.v (ad v) ≠ 0 := sorry,
    have h_simp : (prod_to_idele ad had_unit h_ne_zero).val.val v = ad v := rfl,
    have h : multiplicative.to_add (classical.some (with_zero.to_integer._proof_1 hv))
     = a_val v - J_val v ,
     { have hx := classical.some_spec (with_zero.to_integer._proof_1 hv),
        simp_rw [valuation.map_zpow, valued_K_v.def, h_unif, valued.extension_extends,
        v_valued_K.def, classical.some_spec (adic_valuation.exists_uniformizer K v), 
        ← with_zero.coe_zpow] at hx ⊢,
        rw with_zero.coe_inj at hx,
        rw [hx, ← of_add_zsmul, to_add_of_add, algebra.id.smul_eq_mul, mul_neg_eq_neg_mul_symm, 
          mul_one, neg_sub],},
    
      simp_rw h_simp,
      rw [h, neg_sub, sub_eq_neg_add],
      { apply idele.finite_mul_support_inv (ideal.span{a} : ideal R), 
      rw [ideal.zero_eq_bot, ne.def, ideal.span_singleton_eq_bot],
      exact ha },
      { exact idele.finite_mul_support J 
      (fractional_ideal.factor_ne_zero (left_ne_zero_of_mul_eq_one hval_inv) haJ),}
    },
  exact ⟨H, map_to_fractional_ideals.inv_eq_inv _ ⟨I, I_inv, hval_inv, hinv_val⟩ H⟩,
end
set_option profiler false