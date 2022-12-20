/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import ring_theory.dedekind_domain.factorization
import topology.algebra.uniform_group

/-!
# Factorization of fractional ideals of Dedekind domains
Every nonzero fractional ideal `I` of a Dedekind domain `R` can be factored as a product 
`∏_v v^{n_v}` over the maximal ideals of `R`, where the exponents `n_v` are integers. We define 
`fractional_ideal.count K v I` (abbreviated as `val_v(I)` in the documentation) to be `n_v`, and we 
prove some of its properties. If `I = 0`, we define `val_v(I) = 0`.

## Main definitions
- `fractional_ideal.count` : If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of 
  `R` such that `I = a⁻¹J`, then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we
  set `val_v(I) = 0`. 

## Main results
- `ideal.factorization` : The ideal `I` equals the finprod `∏_v v^(val_v(I))`.
- `fractional_ideal.factorization` : If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an
ideal of `R` such that `I = a⁻¹J`, then `I` is equal to the product `∏_v v^(val_v(J) - val_v(a))`. 
- `fractional_ideal.factorization_principal` : For a nonzero `k = r/s ∈ K`, the fractional ideal 
`(k)` is equal to the product `∏_v v^(val_v(r) - val_v(s))`. 
- `fractional_ideal.finite_factors` : If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many
  maximal ideals of `R`.

## Implementation notes
Since we are only interested in nonzero fractional ideals, we chose to define `val_v(I) = 0` so that
every `val_v` is in `ℤ` and we can avoid having to use `with_top ℤ`.

## Tags
dedekind domain, fractional ideal, factorization
-/

noncomputable theory
open_locale big_operators classical

open set function unique_factorization_monoid is_dedekind_domain
  is_dedekind_domain.height_one_spectrum

/-! ### Factorization of fractional ideals of Dedekind domains -/

variables {A : Type*} [comm_ring A] (B : submonoid A) (C : Type*) [comm_ring C] [algebra A C]

/-- If a prime `p` divides a `finprod`, then it must divide one of its factors. -/
lemma prime.exists_mem_finprod_dvd {α : Type*} {N : Type*} [comm_monoid_with_zero N] {f : α → N} 
  {p : N} (hp : prime p) (hf : (mul_support f).finite) :
  p ∣  ∏ᶠ i, f i →  ∃ (a : α), p ∣ f a := 
begin
  rw finprod_eq_prod _ hf,
  intro h,
  obtain ⟨a, -, ha_dvd⟩ := prime.exists_mem_finset_dvd hp h,
  exact ⟨a, ha_dvd⟩,
end

variables {R : Type*} {K : Type*} [comm_ring R] [field K] [algebra R K] 

/-- The discrete topology on the units of the fractional ideals. -/
instance ufi_ts : topological_space (units (fractional_ideal (non_zero_divisors R) K)) := ⊥

/-- The units of the fractional ideals with the discrete topology are a topological group.  -/
instance ufi_tg : topological_group (units (fractional_ideal (non_zero_divisors R) K)) := 
{ continuous_mul := continuous_of_discrete_topology,
  continuous_inv := continuous_of_discrete_topology, }

instance ufi_us : uniform_space (units (fractional_ideal (non_zero_divisors R) K)) := 
topological_group.to_uniform_space _

instance ufi_ug : uniform_group (units (fractional_ideal (non_zero_divisors R) K)) := 
topological_comm_group_is_uniform

variables [is_fraction_ring R K]

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `J` is nonzero. -/
lemma fractional_ideal.ideal_factor_ne_zero {I : fractional_ideal (non_zero_divisors R) K}
  (hI : I ≠ 0) {a : R} {J : ideal R} 
  (haJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  J ≠ 0 :=
begin
  intro h, 
  rw [h, ideal.zero_eq_bot, fractional_ideal.coe_to_fractional_ideal_bot, mul_zero] at haJ, 
  exact hI haJ,
end

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `a` is nonzero. -/
lemma fractional_ideal.constant_factor_ne_zero {I : fractional_ideal (non_zero_divisors R) K}
  (hI : I ≠ 0) {a : R} {J : ideal R} 
  (haJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  (ideal.span{a} : ideal R) ≠ 0 :=
begin
  intro h,
  rw [ideal.zero_eq_bot, ideal.span_singleton_eq_bot] at h,
  rw [h, ring_hom.map_zero, inv_zero, fractional_ideal.span_singleton_zero, zero_mul] at haJ,
  exact hI haJ,
end

open is_dedekind_domain

variables [is_domain R] [is_dedekind_domain R] (v : height_one_spectrum R)


/-- Only finitely many maximal ideals of `R` divide a given nonzero principal ideal. -/
lemma finite_factors (d : R) (hd : (ideal.span{d} : ideal R) ≠ 0) : 
  {v : height_one_spectrum R | v.as_ideal ∣ (ideal.span({d}) : ideal R)}.finite := 
ideal.finite_factors hd


/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `I` is equal to the product `∏_v v^(val_v(J) - val_v(a))`. -/
lemma fractional_ideal.factorization (I : fractional_ideal (non_zero_divisors R) K) (hI : I ≠ 0) 
  {a : R} {J : ideal R} 
  (haJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  ∏ᶠ (v : height_one_spectrum R), (v.as_ideal : fractional_ideal (non_zero_divisors R) K)^
    ((associates.mk v.as_ideal).count (associates.mk J).factors - 
    (associates.mk v.as_ideal).count (associates.mk (ideal.span{a})).factors : ℤ) = I := 
begin
  have hJ_ne_zero : J ≠ 0 := fractional_ideal.ideal_factor_ne_zero hI haJ,
  have hJ := ideal.finprod_height_one_spectrum_factorization_coe J hJ_ne_zero,
  have ha_ne_zero : ideal.span{a} ≠ 0 := fractional_ideal.constant_factor_ne_zero hI haJ,
  have ha := ideal.finprod_height_one_spectrum_factorization_coe (ideal.span{a} : ideal R) 
    ha_ne_zero,
  rw [haJ, ← fractional_ideal.div_span_singleton, fractional_ideal.div_eq_mul_inv,
    ← fractional_ideal.coe_ideal_span_singleton, ← hJ, ← ha, ← finprod_inv_distrib],
  simp_rw ← zpow_neg,
  rw ← finprod_mul_distrib,
  apply finprod_congr,
  intro v,
  rw [← zpow_add₀ ((@fractional_ideal.coe_ideal_ne_zero_iff R _ K _ _ _ _).mpr v.ne_bot),
    sub_eq_add_neg],
  apply ideal.finite_mul_support_coe hJ_ne_zero, 
  apply ideal.finite_mul_support_inv ha_ne_zero, 
  { apply_instance },
end

/-- For a nonzero `k = r/s ∈ K`, the fractional ideal `(k)` is equal to the product 
`∏_v v^(val_v(r) - val_v(s))`. -/
lemma fractional_ideal.factorization_principal (I : fractional_ideal (non_zero_divisors R) K) 
  (hI : I ≠ 0) (k : K) (hk : I = fractional_ideal.span_singleton (non_zero_divisors R) k) :
  ∏ᶠ (v : height_one_spectrum R), (v.as_ideal : fractional_ideal (non_zero_divisors R) K)^
    ((associates.mk v.as_ideal).count (associates.mk (ideal.span 
    {classical.some (is_localization.mk'_surjective (non_zero_divisors R) k)} : ideal R)).factors - 
    (associates.mk v.as_ideal).count (associates.mk (ideal.span { (classical.some
    (classical.some_spec (is_localization.mk'_surjective (non_zero_divisors R) k)) :
    ↥(non_zero_divisors R))} : ideal R)).factors : ℤ) = I := 
begin
  set n : R := classical.some(is_localization.mk'_surjective (non_zero_divisors R) k) with hn,
  set d : ↥(non_zero_divisors R) := (classical.some (classical.some_spec
    (is_localization.mk'_surjective (non_zero_divisors R) k))) with hd,
  have hd_ne_zero : (algebra_map R K) (d : R) ≠ 0 := map_ne_zero_of_mem_non_zero_divisors
    _ (is_fraction_ring.injective R K) d.property,
  have haJ' : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) d)⁻¹ *
    ↑(ideal.span {n} : ideal R),
  { rw [hk, fractional_ideal.coe_ideal_span_singleton,
      fractional_ideal.span_singleton_mul_span_singleton],
    apply congr_arg,
    rw [eq_inv_mul_iff_mul_eq₀ hd_ne_zero, mul_comm,
      ← is_localization.eq_mk'_iff_mul_eq, eq_comm],
    exact classical.some_spec (classical.some_spec (is_localization.mk'_surjective
      (non_zero_divisors R) k)), },
exact fractional_ideal.factorization I hI haJ',
end

variables (K)

/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that `I = a⁻¹J`,
then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we set `val_v(I) = 0`. -/
def fractional_ideal.count (I : fractional_ideal (non_zero_divisors R) K) : ℤ := 
dite (I = 0) (λ (hI : I = 0), 0) (λ hI : ¬ I = 0, 
let a := classical.some (fractional_ideal.exists_eq_span_singleton_mul I) in let 
J := classical.some (classical.some_spec (fractional_ideal.exists_eq_span_singleton_mul I))
in ((associates.mk v.as_ideal).count (associates.mk J).factors - 
    (associates.mk v.as_ideal).count (associates.mk (ideal.span{a})).factors : ℤ))

/-- `val_v(I)` does not depend on the choice of `a` and `J` used to represent `I`. -/
lemma fractional_ideal.count_well_defined  {I : fractional_ideal (non_zero_divisors R) K}
  (hI : I ≠ 0)  {a : R} {J : ideal R} 
  (h_aJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  fractional_ideal.count K v I = ((associates.mk v.as_ideal).count (associates.mk J).factors - 
    (associates.mk v.as_ideal).count (associates.mk (ideal.span{a})).factors : ℤ) :=
begin
  set a₁ := classical.some (fractional_ideal.exists_eq_span_singleton_mul I) with h_a₁,
  set J₁ := classical.some (classical.some_spec (fractional_ideal.exists_eq_span_singleton_mul I))
    with h_J₁,
  have h_a₁J₁ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a₁)⁻¹ *
    ↑J₁ :=
(classical.some_spec (classical.some_spec (fractional_ideal.exists_eq_span_singleton_mul I))).2,
  have h_a₁_ne_zero : a₁ ≠ 0 :=
  (classical.some_spec (classical.some_spec (fractional_ideal.exists_eq_span_singleton_mul I))).1,
  have h_J₁_ne_zero : J₁ ≠ 0 := fractional_ideal.ideal_factor_ne_zero hI h_a₁J₁,
  have h_a_ne_zero : ideal.span{a} ≠ 0 := fractional_ideal.constant_factor_ne_zero hI h_aJ,
  have h_J_ne_zero : J ≠ 0 := fractional_ideal.ideal_factor_ne_zero hI h_aJ,
  have h_a₁' : fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a₁) ≠ 0,
  { rw [ne.def, fractional_ideal.span_singleton_eq_zero_iff, ← (algebra_map R K).map_zero,
      injective.eq_iff (is_localization.injective K (le_refl (non_zero_divisors R)))],
    exact h_a₁_ne_zero,},
  have h_a' : fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a) ≠ 0,
  { rw [ne.def, fractional_ideal.span_singleton_eq_zero_iff, ← (algebra_map R K).map_zero,
      injective.eq_iff (is_localization.injective K (le_refl (non_zero_divisors R)))],
    rw [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot] at h_a_ne_zero,
    exact h_a_ne_zero,},
  have hv : irreducible (associates.mk v.as_ideal),
  { rw associates.irreducible_mk,
    exact v.irreducible, },
  rw [h_a₁J₁, ← fractional_ideal.div_span_singleton, ← fractional_ideal.div_span_singleton,
    div_eq_div_iff h_a₁' h_a', ← fractional_ideal.coe_ideal_span_singleton,
    ← fractional_ideal.coe_ideal_span_singleton, ← fractional_ideal.coe_ideal_mul,
    ← fractional_ideal.coe_ideal_mul] at h_aJ,
  rw [fractional_ideal.count, dif_neg hI, sub_eq_sub_iff_add_eq_add, ← int.coe_nat_add,
    ← int.coe_nat_add, int.coe_nat_inj', ← associates.count_mul _ _ hv, 
    ← associates.count_mul _ _ hv, associates.mk_mul_mk, associates.mk_mul_mk, 
    fractional_ideal.coe_ideal_injective h_aJ],
  { rw [ne.def, associates.mk_eq_zero], exact h_J_ne_zero },
  { rw [ne.def, associates.mk_eq_zero, ideal.zero_eq_bot, ideal.span_singleton_eq_bot],
    exact h_a₁_ne_zero, },
  { rw [ne.def, associates.mk_eq_zero], exact h_J₁_ne_zero },
  { rw [ne.def, associates.mk_eq_zero], exact h_a_ne_zero },
end

/-- For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. -/
lemma fractional_ideal.count_mul {I I' : fractional_ideal (non_zero_divisors R) K} (hI : I ≠ 0) 
  (hI' : I' ≠ 0) : fractional_ideal.count K v (I*I')  = fractional_ideal.count K v (I) + 
  fractional_ideal.count K v (I') :=
begin
  have hv : irreducible (associates.mk v.as_ideal),
  { apply v.associates_irreducible },
  obtain ⟨a, J, ha, haJ⟩ := fractional_ideal.exists_eq_span_singleton_mul I,
  have ha_ne_zero : associates.mk (ideal.span {a} : ideal R) ≠ 0,
  { rw [ne.def, associates.mk_eq_zero, ideal.zero_eq_bot, ideal.span_singleton_eq_bot], exact ha },
  have hJ_ne_zero : associates.mk J ≠ 0,
  { rw [ne.def, associates.mk_eq_zero], exact fractional_ideal.ideal_factor_ne_zero hI haJ },
  obtain ⟨a', J', ha', haJ'⟩ := fractional_ideal.exists_eq_span_singleton_mul I',
  have ha'_ne_zero : associates.mk (ideal.span {a'} : ideal R) ≠ 0,
  { rw [ne.def, associates.mk_eq_zero, ideal.zero_eq_bot, ideal.span_singleton_eq_bot], exact ha' },
  have hJ'_ne_zero : associates.mk J' ≠ 0,
  { rw [ne.def, associates.mk_eq_zero], exact fractional_ideal.ideal_factor_ne_zero hI' haJ' },
  have h_prod : I*I' = fractional_ideal.span_singleton (non_zero_divisors R)
    ((algebra_map R K) (a*a'))⁻¹ * ↑(J*J'),
    { rw [haJ, haJ', mul_assoc, mul_comm ↑J, mul_assoc, ← mul_assoc, 
      fractional_ideal.span_singleton_mul_span_singleton, 
      fractional_ideal.coe_ideal_mul, ring_hom.map_mul, mul_inv, mul_comm ↑J] },
  rw [fractional_ideal.count_well_defined K v hI haJ, 
    fractional_ideal.count_well_defined K v hI' haJ',
    fractional_ideal.count_well_defined K v (mul_ne_zero hI hI') h_prod,
    ← associates.mk_mul_mk, associates.count_mul hJ_ne_zero hJ'_ne_zero hv,
    ← ideal.span_singleton_mul_span_singleton, ← associates.mk_mul_mk,
    associates.count_mul ha_ne_zero ha'_ne_zero hv],
  push_cast,
  ring,
end

/-- For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. If `I` or `I'` is zero, then
`val_v(I*I') = 0`. -/
lemma fractional_ideal.count_mul' (I I' : fractional_ideal (non_zero_divisors R) K) :
  fractional_ideal.count K v (I*I')  = (if I ≠ 0 ∧ I' ≠ 0 then  fractional_ideal.count K v (I) + 
    fractional_ideal.count K v (I') else 0) := 
begin
  split_ifs,
  { exact fractional_ideal.count_mul K v h.1 h.2 },
  { push_neg at h,
    by_cases hI : I = 0,
    { rw [hI, zero_mul, fractional_ideal.count, dif_pos (eq.refl _)], },
    { rw [(h hI), mul_zero, fractional_ideal.count, dif_pos (eq.refl _)], }}
end

/-- val_v(0) = 0. -/
lemma fractional_ideal.count_zero : 
  fractional_ideal.count K v (0 : fractional_ideal (non_zero_divisors R) K) = 0 :=
by rw [fractional_ideal.count, dif_pos (eq.refl _)]

/-- val_v(1) = 0. -/
lemma fractional_ideal.count_one : 
  fractional_ideal.count K v (1 : fractional_ideal (non_zero_divisors R) K) = 0 :=
begin
  have h_one : (1 : fractional_ideal (non_zero_divisors R) K) = fractional_ideal.span_singleton
    (non_zero_divisors R) ((algebra_map R K) (1))⁻¹ * ↑(1 : ideal R),
  { rw [(algebra_map R K).map_one, ideal.one_eq_top, fractional_ideal.coe_ideal_top, mul_one,
      inv_one, fractional_ideal.span_singleton_one], },
  rw [fractional_ideal.count_well_defined K v one_ne_zero h_one, ideal.span_singleton_one,
    ideal.one_eq_top, sub_self],
end

/-- For every `n ∈ ℕ` and every ideal `I`, `val_v(I^n) = n*val_v(I)`. -/
lemma fractional_ideal.count_pow (n : ℕ) (I : fractional_ideal (non_zero_divisors R) K) : 
  fractional_ideal.count K v (I^n) = n * fractional_ideal.count K v I :=
begin
  induction n with n h,
  { rw [pow_zero, int.coe_nat_zero, zero_mul, fractional_ideal.count_one] },
  { rw pow_succ, rw fractional_ideal.count_mul',
    by_cases hI : I = 0,
    { have h_neg : ¬ (I ≠ 0 ∧ I ^ n ≠ 0),
      { rw [not_and, not_not, ne.def], intro h, exact absurd hI h, },
      rw [if_neg h_neg, hI, fractional_ideal.count_zero, mul_zero], },
    { rw [if_pos (and.intro hI (pow_ne_zero n hI)), h, nat.succ_eq_add_one], ring, }},
end

/--`val_v(v) = 1`, when `v` is regarded as a fractional ideal. -/
lemma fractional_ideal.count_self : 
  fractional_ideal.count K v (v.as_ideal : fractional_ideal (non_zero_divisors R) K)  = 1 :=
begin
  have hv : (v.as_ideal : fractional_ideal (non_zero_divisors R) K) ≠ 0,
  { rw fractional_ideal.coe_ideal_ne_zero_iff,
    exact v.ne_bot  },
  have h_self : (v.as_ideal : fractional_ideal (non_zero_divisors R) K) = 
    fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) 1)⁻¹ * 
    ↑(v.as_ideal),
  { rw [(algebra_map R K).map_one, inv_one, fractional_ideal.span_singleton_one, one_mul], },
  have hv_irred : irreducible (associates.mk v.as_ideal),
  { apply v.associates_irreducible },
  rw [fractional_ideal.count_well_defined K v hv h_self, associates.count_self hv_irred,
    ideal.span_singleton_one, ← ideal.one_eq_top, associates.mk_one, associates.factors_one,
    associates.count_zero hv_irred, int.coe_nat_zero, sub_zero, int.coe_nat_one],
end

/--`val_v(v) = n` for every `n ∈ ℕ`. -/
lemma fractional_ideal.count_pow_self (n : ℕ) : 
  fractional_ideal.count K v ((v.as_ideal : fractional_ideal (non_zero_divisors R) K)^n) = n := 
by rw [fractional_ideal.count_pow, fractional_ideal.count_self, mul_one]

/--`val_v(I⁻ⁿ) = -val_v(Iⁿ)` for every `n ∈ ℤ`. -/
lemma fractional_ideal.count_inv (n : ℤ) (I : fractional_ideal (non_zero_divisors R) K) : 
  fractional_ideal.count K v (I^-n) = - fractional_ideal.count K v (I^n) := 
begin
  by_cases hI : I = 0,
  {by_cases hn : n = 0,
    { rw [hn, neg_zero, zpow_zero, fractional_ideal.count_one, neg_zero], },
    { rw [hI, zero_zpow n hn, zero_zpow (-n) (neg_ne_zero.mpr hn), fractional_ideal.count_zero,
        neg_zero], }},
  { rw [eq_neg_iff_add_eq_zero,
    ←  fractional_ideal.count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
    ← zpow_add₀ hI, neg_add_self, zpow_zero],
    exact fractional_ideal.count_one K v, }
end

/--`val_v(Iⁿ) = n*val_v(I)` for every `n ∈ ℤ`. -/
lemma fractional_ideal.count_zpow (n : ℤ) (I : fractional_ideal (non_zero_divisors R) K) : 
  fractional_ideal.count K v (I^n) = n * fractional_ideal.count K v I := 
begin
  cases n,
  { rw [int.of_nat_eq_coe, zpow_coe_nat],
    exact fractional_ideal.count_pow K v n I, },
  { rw [int.neg_succ_of_nat_coe, fractional_ideal.count_inv, zpow_coe_nat, 
      fractional_ideal.count_pow], ring, }
end

/--`val_v(v) = n` for every `n ∈ ℤ`. -/
lemma fractional_ideal.count_zpow_self (n : ℤ) : 
  fractional_ideal.count K v
  ((v.as_ideal : fractional_ideal (non_zero_divisors R) K)^n) = n := 
by rw [fractional_ideal.count_zpow, fractional_ideal.count_self, mul_one]

/-- If `v ≠ w` are two maximal ideals of `R`, then `val_v(w) = 0`. -/
lemma fractional_ideal.count_maximal_coprime (w : height_one_spectrum R) (hw : w ≠ v) :
  fractional_ideal.count K v (w.as_ideal : fractional_ideal (non_zero_divisors R) K) = 0 := 
begin
  have hw_fact : (w.as_ideal : fractional_ideal (non_zero_divisors R) K) =
   fractional_ideal.span_singleton
    (non_zero_divisors R) ((algebra_map R K) (1))⁻¹ * ↑(w.as_ideal),
  { rw [(algebra_map R K).map_one, inv_one, fractional_ideal.span_singleton_one, one_mul], },
  have hw_ne_zero : (w.as_ideal : fractional_ideal (non_zero_divisors R) K) ≠ 0,
  { rw fractional_ideal.coe_ideal_ne_zero_iff,
    exact w.ne_bot  },
  have hv : irreducible (associates.mk v.as_ideal) := 
  by apply v.associates_irreducible,
  have hw' : irreducible (associates.mk w.as_ideal) := 
  by apply w.associates_irreducible,
  rw [fractional_ideal.count_well_defined K v hw_ne_zero hw_fact, ideal.span_singleton_one,
    ← ideal.one_eq_top, associates.mk_one, associates.factors_one, associates.count_zero hv,
    int.coe_nat_zero, sub_zero, int.coe_nat_eq_zero, ← pow_one (associates.mk w.as_ideal),
    associates.factors_prime_pow hw', associates.count_some hv, multiset.repeat_one, 
    multiset.count_eq_zero, multiset.mem_singleton],
  simp only [subtype.val_eq_coe],
  rw [associates.mk_eq_mk_iff_associated, associated_iff_eq, ← height_one_spectrum.ext_iff],
  exact ne.symm hw,
end

/-- `val_v(∏_{w ≠ v} w^{exps w}) = 0`. -/
lemma fractional_ideal.count_finprod_coprime (exps : height_one_spectrum R → ℤ) :
  fractional_ideal.count K v (∏ᶠ (w : height_one_spectrum R) (H : w ≠ v), ↑(w.as_ideal) ^ exps w) = 0 :=
begin
  apply finprod_mem_induction (λ I, fractional_ideal.count K v I = 0),
  { exact fractional_ideal.count_one K v },
  { intros I I' hI hI',
    by_cases h : I ≠ 0 ∧ I' ≠ 0,
    { rw [fractional_ideal.count_mul' K v, if_pos h, hI, hI', add_zero] },
    { rw [fractional_ideal.count_mul' K v, if_neg h], }},
  { intros w hw,
    rw [fractional_ideal.count_zpow, fractional_ideal.count_maximal_coprime K v w hw, mul_zero] }
end

/-- If `exps` is finitely supported, then `val_v(∏_w w^{exps w}) = exps v`. -/
lemma fractional_ideal.count_finprod (exps : height_one_spectrum R → ℤ)
(h_exps : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, exps v = 0 ) :
fractional_ideal.count K v (∏ᶠ (v : height_one_spectrum R), 
  (v.as_ideal : fractional_ideal (non_zero_divisors R) K)^(exps v)) = exps v :=
begin
  have h_supp : (mul_support (λ (i : height_one_spectrum R), ↑(i.as_ideal) ^ exps i)).finite,
  { have h_subset : {v : height_one_spectrum R | 
      (v.as_ideal : fractional_ideal (non_zero_divisors R) K) ^ exps v ≠ 1} ⊆ 
      {v : height_one_spectrum R | exps v ≠ 0},
    { intros v hv,
      by_contradiction h,
      rw [mem_set_of_eq, not_not] at h,
      rw [mem_set_of_eq, h, zpow_zero] at hv,
      exact hv (eq.refl 1),},
    exact finite.subset h_exps h_subset, },
    rw [← mul_finprod_cond_ne v h_supp, fractional_ideal.count_mul, 
      fractional_ideal.count_zpow_self, fractional_ideal.count_finprod_coprime, add_zero],
  { apply zpow_ne_zero, 
    exact fractional_ideal.coe_ideal_ne_zero_iff.mpr v.ne_bot, },
  { rw [finprod_cond_ne _ _ h_supp, finset.prod_ne_zero_iff],
    intros w hw,
    apply zpow_ne_zero, 
    exact fractional_ideal.coe_ideal_ne_zero_iff.mpr w.ne_bot, }
end

variable {K}
/-- If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many maximal ideals of `R`. -/
lemma fractional_ideal.finite_factors {I : fractional_ideal (non_zero_divisors R) K} (hI : I ≠ 0)
  {a : R} {J : ideal R} 
  (haJ : I = fractional_ideal.span_singleton (non_zero_divisors R) ((algebra_map R K) a)⁻¹ * ↑J) :
  ∀ᶠ v : height_one_spectrum R in filter.cofinite,
  (((associates.mk v.as_ideal).count (associates.mk J).factors : ℤ) - 
    ((associates.mk v.as_ideal).count (associates.mk (ideal.span {a})).factors) = 0) :=
begin
  have ha_ne_zero : ideal.span{a} ≠ 0 := fractional_ideal.constant_factor_ne_zero hI haJ,
  have hJ_ne_zero : J ≠ 0 := fractional_ideal.ideal_factor_ne_zero hI haJ,
  rw filter.eventually_cofinite,
  have h_subset : {v : height_one_spectrum R | ¬((associates.mk v.as_ideal).count 
    (associates.mk J).factors : ℤ) - 
    ↑((associates.mk v.as_ideal).count (associates.mk (ideal.span {a})).factors) = 0} ⊆ 
    {v : height_one_spectrum R | v.as_ideal ∣ J} ∪ 
    {v : height_one_spectrum R | v.as_ideal ∣ (ideal.span {a})},
  { intros v hv,
    have hv_irred : irreducible v.as_ideal := v.irreducible,
    by_contradiction h_nmem,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq] at h_nmem,
    push_neg at h_nmem,  
    rw [← associates.count_ne_zero_iff_dvd ha_ne_zero hv_irred, not_not, 
    ← associates.count_ne_zero_iff_dvd hJ_ne_zero hv_irred, not_not] 
      at h_nmem,
    rw [mem_set_of_eq, h_nmem.1, h_nmem.2, sub_self] at hv,
    exact hv (eq.refl 0), },
  exact finite.subset (finite.union 
    (ideal.finite_factors (fractional_ideal.ideal_factor_ne_zero hI haJ)) 
    (ideal.finite_factors (fractional_ideal.constant_factor_ne_zero hI haJ)))
    h_subset,
end