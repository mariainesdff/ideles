/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import adeles_R

/-!
# The finite idèle group of a Dedekind domain
We define the finite idèle group of a Dedekind domain `R` and show that if `R` has Krull dimension 
1, then there is an injective group homomorphism from the units of the field of fractions of `R` to 
its finite adèle ring.

We prove that there is a continuous surjective group homomorphism from the finite idèle group of `R`
to the group of invertible fractional ideals of `R` and compute the kernel of this map.

## Main definitions
- `finite_idele_group'` : The finite idèle group of `R`, defined as unit group of `A_R_f R`.
- `inj_units_K` : The diagonal inclusion of `K*` in `finite_idele_group' R K`.
- `map_to_fractional_ideals` : The group homomorphism from `finite_idele_group' R K` to the group
  of `Fr(R)` of invertible fractional_ideals of `R` sending a finite idèle `x` to the product 
  `∏_v v^(val_v(x_v))`, where `val_v` denotes the additive `v`-adic valuation.

## Main results
- `inj_units_K.group_hom` : `inj_units_K` is a group homomorphism.
- `inj_units_K.injective` : `inj_units_K` is injective for every Dedekind domain of Krull 
  dimension 1.
- `map_to_fractional_ideals.surjective` : `map_to_fractional_ideals` is surjective.
- `map_to_fractional_ideals.continuous` : `map_to_fractional_ideals` is continuous when the group
  of fractional ideals is given the discrete topology.
- `map_to_fractional_ideals.mem_kernel_iff` : A finite idèle `x` is in the kernel of 
`map_to_fractional_ideals` if and only if `|x_v|_v = 1` for all `v`. 

## Implementation notes
As in `adeles_R`, we are only interested on Dedekind domains of Krull dimension 1.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite idèle group, dedekind domain, fractional ideal
-/

noncomputable theory
open_locale big_operators classical


open set function is_dedekind_domain

variables (R : Type) (K : Type) [comm_ring R] [is_domain R] [is_dedekind_domain R] [field K]
  [algebra R K] [is_fraction_ring R K] (v : height_one_spectrum R)


/-! ### The finite idèle group of a Dedekind domain -/

/--The finite idèle group of `R` is the unit group of its finite adèle ring. -/
def finite_idele_group' := units (finite_adele_ring' R K)

instance : topological_space (finite_idele_group' R K) := units.topological_space
instance : comm_group (finite_idele_group' R K) := units.comm_group
instance : topological_group (finite_idele_group' R K) := units.topological_group
instance : uniform_space (finite_idele_group' R K) := topological_group.to_uniform_space _
instance : uniform_group (finite_idele_group' R K) := topological_comm_group_is_uniform

lemma right_inv (x : units K) : inj_K R K x.val * inj_K R K x.inv = 1 := 
begin
  rw [← inj_K.map_mul, units.val_eq_coe, units.inv_eq_coe_inv, units.mul_inv],
  exact inj_K.map_one R K
end

lemma left_inv (x : units K) : inj_K R K x.inv * inj_K R K x.val = 1 := 
by rw [mul_comm, right_inv]

/-- The diagonal inclusion `k ↦ (k)_v` of `K*` into the finite idèle group of `R`. -/
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

/-- The map `inj_units_K` is a group homomorphism. -/
def inj_units_K.group_hom : monoid_hom (units K) (finite_idele_group' R K) := 
{ to_fun   := inj_units_K R K,
  map_one' := inj_units_K.map_one R K,
  map_mul' := inj_units_K.map_mul R K, }

/-- If `height_one_spectrum R` is nonempty, then `inj_units_K` is injective. Note that the
nonemptiness hypothesis is satisfied for every Dedekind domain that is not a field. -/
lemma inj_units_K.injective [inh : inhabited (height_one_spectrum R)] : 
  injective (inj_units_K.group_hom R K) :=
begin
  rw ← monoid_hom.ker_eq_bot_iff,
  ext x,
  rw [monoid_hom.mem_ker, subgroup.mem_bot, inj_units_K.group_hom, monoid_hom.coe_mk, inj_units_K,
    ← units.eq_iff, units.coe_mk, units.val_eq_coe, ← units.eq_iff],
  exact injective.eq_iff (inj_K.injective R K),
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
  (valued.v (x.val.val v) : (with_zero (multiplicative ℤ))) * (valued.v (x.inv.val v)) = 1 :=
by rw [← valuation.map_mul, prod_val_inv_eq_one, valuation.map_one]

lemma valuation_inv (x : finite_idele_group' R K) :
  (valued.v (x.inv.val v)) = (valued.v (x.val.val v))⁻¹ :=
begin
  rw [← mul_one (valued.v (x.val.val v))⁻¹,eq_inv_mul_iff_mul_eq₀, valuation_val_inv],
  { exact (valuation.ne_zero_iff _).mpr (v_comp.ne_zero R K v x) } 
end

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
`x_v ∉ R_v` or `x⁻¹_v ∉ R_v`. -/ 
lemma restricted_product (x : finite_idele_group' R K) :
  ({ v : height_one_spectrum R | (¬ (x.val.val v) ∈ v.adic_completion_integers K) } ∪ 
    { v : height_one_spectrum R | ¬ (x.inv.val v) ∈ v.adic_completion_integers K }).finite :=
finite.union x.val.property x.inv.property

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
`|x_v|_v ≠ 1`. -/ 
lemma finite_exponents (x : finite_idele_group' R K) : set.finite
  { v : height_one_spectrum R | (valued.v (x.val.val v) : with_zero (multiplicative ℤ)) ≠ 1 } :=
begin
  have h_subset : { v : height_one_spectrum R |
    (valued.v (x.val.val v) : with_zero (multiplicative ℤ)) ≠ 1 } ⊆ 
  { v : height_one_spectrum R | ¬ (x.val.val v) ∈ v.adic_completion_integers K } ∪ 
  { v : height_one_spectrum R | ¬ (x.inv.val v) ∈ v.adic_completion_integers K },
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq, adic_completion.is_integer,
      adic_completion.is_integer],
    rw mem_set_of_eq at hv,
    cases (lt_or_gt_of_ne hv) with hlt hgt,
    { right,
      have h_one : (valued.v (x.val.val v) : (with_zero (multiplicative ℤ))) *
        (valued.v (x.inv.val v)) = 1 :=valuation_val_inv R K v x,
      have h_inv : (1 : with_zero (multiplicative ℤ)) < (valued.v (x.inv.val v)),
      { have hx : (valued.v (x.val.val v) : with_zero (multiplicative ℤ)) ≠ 0,
        { rw [valuation.ne_zero_iff],
          exact left_ne_zero_of_mul_eq_one (prod_val_inv_eq_one R K v x),},
        rw mul_eq_one_iff_inv_eq₀ hx at h_one,
        rw [← h_one, ← inv_one, inv_lt_inv₀ (ne.symm zero_ne_one) hx],
        exact hlt, },
      exact not_le.mpr h_inv,},
    { left, exact not_le.mpr hgt, }},
  exact finite.subset (restricted_product R K x) h_subset,
end

/-- For any `k ∈ K*` and any maximal ideal `v` of `R`, the valuation `|k|_v` is nonzero. -/
lemma units.valuation_ne_zero {k : K} (hk : k ≠ 0) : 
(valued.v ((coe : K → (v.adic_completion K)) k) : with_zero (multiplicative ℤ)) ≠ 0 := 
begin
  rw [valuation.ne_zero_iff, ← uniform_space.completion.coe_zero,
    injective.ne_iff uniform_space.completion.coe_inj],
  exact hk,
  apply_instance,
end

/-- The integer number corresponding to a nonzero `x` in `with_zero (multiplicative ℤ)`. -/
def with_zero.to_integer {x : with_zero (multiplicative ℤ)} (hx : x ≠ 0) : ℤ :=
multiplicative.to_add (classical.some (with_zero.ne_zero_iff_exists.mp hx))

/-- Given a finite idèle `x`, for each maximal ideal `v` of `R` we obtain an integer that 
represents the additive `v`-adic valuation of the component `x_v` of `x`. -/
def finite_idele.to_add_valuations (x : finite_idele_group' R K) : 
  Π (v : height_one_spectrum R), ℤ :=
λ v, -(with_zero.to_integer ((valuation.ne_zero_iff valued.v).mpr (v_comp.ne_zero R K v x)))

lemma finite_idele.to_add_valuations.map_one : 
  finite_idele.to_add_valuations R K (1 : finite_idele_group' R K) = 
    λ (v : height_one_spectrum R), (0 : ℤ) :=
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

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
the additive `v`-adic valuation of `x_v` is nonzero. -/ 
lemma finite_add_support (x : finite_idele_group' R K ) : 
  ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, finite_idele.to_add_valuations R K x v = 0 := 
begin
  have h := finite_exponents R K x,
  rw finite_idele.to_add_valuations,
  simp_rw [neg_eq_zero, with_zero.to_integer],
  have h_subset : {v : height_one_spectrum R | ¬multiplicative.to_add (classical.some 
    (with_zero.to_integer._proof_1 ((valued.v.ne_zero_iff ).mpr (v_comp.ne_zero R K v x)))) = 0} 
    ⊆ {v : height_one_spectrum R | (valued.v (x.val.val v) : with_zero (multiplicative ℤ)) ≠ 1},
  { intros v hv,
    set y := (classical.some (with_zero.to_integer._proof_1 
      ((valued.v.ne_zero_iff ).mpr (v_comp.ne_zero R K v x)))) with hy,
    rw mem_set_of_eq,
    by_contradiction h,
    have y_spec := classical.some_spec
      (with_zero.to_integer._proof_1 ((valued.v.ne_zero_iff ).mpr (v_comp.ne_zero R K v x))),
    rw [← hy, h, ← with_zero.coe_one, with_zero.coe_inj] at y_spec,
    simp_rw [← to_add_one] at hv,
    rw [mem_set_of_eq, ← hy, y_spec] at hv,
    exact hv (eq.refl _), },
  exact finite.subset (finite_exponents R K x) h_subset
end

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
`v^(finite_idele.to_add_valuations R K x v)` is not the fractional ideal `(1)`.  -/ 
lemma finite_support (x : finite_idele_group' R K ) : (mul_support (λ (v : height_one_spectrum R), 
  (v.as_ideal : 
    fractional_ideal (non_zero_divisors R) K) ^ finite_idele.to_add_valuations R K x v)).finite := 
begin
  have h_subset :
    {v : height_one_spectrum R | (v.as_ideal : fractional_ideal (non_zero_divisors R) K) ^ 
      finite_idele.to_add_valuations R K x v ≠ 1} ⊆
    { v : height_one_spectrum R | (valued.v (x.val.val v) : with_zero (multiplicative ℤ)) ≠ 1 },
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

/-- For any finite idèle `x`, there are finitely many maximal ideals `v` of `R` for which
`v^-(finite_idele.to_add_valuations R K x v)` is not the fractional ideal `(1)`.  -/ 
lemma finite_support' (x : finite_idele_group' R K ) : 
  (mul_support (λ (v : height_one_spectrum R), (v.as_ideal : 
    fractional_ideal (non_zero_divisors R) K) ^ -finite_idele.to_add_valuations R K x v)).finite := 
begin
  have h : {v : height_one_spectrum R | (v.as_ideal : fractional_ideal (non_zero_divisors R) K) ^ 
    -finite_idele.to_add_valuations R K x v ≠ 1} =
    {v : height_one_spectrum R | (v.as_ideal : fractional_ideal (non_zero_divisors R) K) ^ 
      finite_idele.to_add_valuations R K x v ≠ 1},
  { ext v,
    rw [mem_set_of_eq, mem_set_of_eq, ne.def, ne.def, zpow_neg, inv_eq_one], },
  rw [mul_support, h],
  exact finite_support R K x,
end

/-- The map from `finite_idele_group' R K` to the fractional_ideals of `R` sending a finite idèle 
`x` to the product `∏_v v^(val_v(x_v))`, where `val_v` denotes the additive `v`-adic valuation. -/
def map_to_fractional_ideals.val :
  (finite_idele_group' R K) → (fractional_ideal (non_zero_divisors R) K) := λ x,
∏ᶠ (v : height_one_spectrum R), (v.as_ideal : fractional_ideal (non_zero_divisors R) K)^
  (finite_idele.to_add_valuations R K x v)

def map_to_fractional_ideals.group_hom : monoid_hom
  (finite_idele_group' R K)  (fractional_ideal (non_zero_divisors R) K) := 
{ to_fun := map_to_fractional_ideals.val R K,
  map_one' := by { simp_rw [map_to_fractional_ideals.val, finite_idele.to_add_valuations.map_one,
    zpow_zero, finprod_one],},
  map_mul' := λ x y,
  begin
    rw [map_to_fractional_ideals.val], 
    dsimp only,
    rw finite_idele.to_add_valuations.map_mul,
    simp_rw pi.add_apply,
    rw ← finprod_mul_distrib (finite_support R K x) (finite_support R K y),
    apply finprod_congr,
    intro v,
    rw zpow_add₀,
    { rw [ne.def, fractional_ideal.coe_ideal_eq_zero],
      exact v.ne_bot},
  end }

/-- The map from `finite_idele_group' R K` to the fractional_ideals of `R` sending a finite idèle 
`x` to the product `∏_v v^-(val_v(x_v))`, where `val_v` denotes the additive `v`-adic valuation. -/
def map_to_fractional_ideals.inv :
  (finite_idele_group' R K) → (fractional_ideal (non_zero_divisors R) K) := λ x,
∏ᶠ (v : height_one_spectrum R), (v.as_ideal : fractional_ideal (non_zero_divisors R) K)^
  (-finite_idele.to_add_valuations R K x v)

lemma finite_idele.to_add_valuations.mul_inv (x : finite_idele_group' R K): 
  map_to_fractional_ideals.val R K x * map_to_fractional_ideals.inv R K x = 1 := 
begin
  rw [map_to_fractional_ideals.val, map_to_fractional_ideals.inv],
  dsimp only,
  rw [← finprod_mul_distrib (finite_support R K x) (finite_support' R K x), ← finprod_one],
  apply finprod_congr ,
  intro v,
  rw [← zpow_add₀, add_right_neg, zpow_zero],
  { rw [ne.def, fractional_ideal.coe_ideal_eq_zero],
      exact v.ne_bot },
end

lemma finite_idele.to_add_valuations.inv_mul (x : finite_idele_group' R K): 
  map_to_fractional_ideals.inv R K x * map_to_fractional_ideals.val R K x = 1 := 
by simpa [mul_comm] using (finite_idele.to_add_valuations.mul_inv R K x)


/-- The map from `finite_idele_group' R K` to the units of the fractional_ideals of `R` sending a 
finite idèle `x` to the product `∏_v v^(val_v(x_v))`, where `val_v` denotes the additive `v`-adic
valuation. -/
def map_to_fractional_ideals.def :
  (finite_idele_group' R K) → (units (fractional_ideal (non_zero_divisors R) K)) := 
force_noncomputable $ λ x, ⟨map_to_fractional_ideals.val R K x, map_to_fractional_ideals.inv R K x, 
  finite_idele.to_add_valuations.mul_inv R K x, finite_idele.to_add_valuations.inv_mul R K x⟩

/-- `map_to_fractional_ideals.def` is a group homomorphism. -/
def map_to_fractional_ideals : monoid_hom
  (finite_idele_group' R K)  (units (fractional_ideal (non_zero_divisors R) K)) := 
{ to_fun := map_to_fractional_ideals.def R K,
  map_one' := by {
    rw [map_to_fractional_ideals.def, force_noncomputable_def, ← units.eq_iff, units.coe_mk,
      units.coe_one],
    exact (map_to_fractional_ideals.group_hom R K).map_one', },
  map_mul' := λ x y,
  begin
    rw [map_to_fractional_ideals.def,force_noncomputable_def, ← units.eq_iff, units.coe_mul,
      units.coe_mk, units.coe_mk, units.coe_mk], 
    exact (map_to_fractional_ideals.group_hom R K).map_mul' x y,
  end }

variables {R K}
lemma val_property {a : Π v : height_one_spectrum R, v.adic_completion K}
  (ha : ∀ᶠ v : height_one_spectrum R in filter.cofinite,
    (valued.v (a v) : with_zero (multiplicative ℤ)) = 1)
  (h_ne_zero : ∀ v : height_one_spectrum R, a v ≠ 0) :
  ∀ᶠ v : height_one_spectrum R in filter.cofinite, a v ∈ v.adic_completion_integers K :=
begin
  rw filter.eventually_cofinite at ha ⊢,
  simp_rw adic_completion.is_integer,
  have h_subset :
    {x : height_one_spectrum R | ¬(valued.v (a x) : with_zero (multiplicative ℤ)) ≤ 1} ⊆ 
    {x : height_one_spectrum R | ¬(valued.v (a x) : with_zero (multiplicative ℤ)) = 1},
  { intros v hv,
    exact ne_of_gt (not_le.mp hv), },
  exact finite.subset ha h_subset,
end

lemma inv_property {a : Π v : height_one_spectrum R, v.adic_completion K}
  (ha : ∀ᶠ v : height_one_spectrum R in filter.cofinite, 
    (valued.v (a v) : with_zero (multiplicative ℤ)) = 1)
  (h_ne_zero : ∀ v : height_one_spectrum R, a v ≠ 0) :
  ∀ᶠ v : height_one_spectrum R in filter.cofinite, (a v)⁻¹ ∈ v.adic_completion_integers K :=
begin
  rw filter.eventually_cofinite at ha ⊢,
  simp_rw [adic_completion.is_integer, not_le],
  have h_subset : {x : height_one_spectrum R |
    1 < (valued.v (a x)⁻¹ : with_zero (multiplicative ℤ)) } ⊆ 
    {x : height_one_spectrum R | ¬(valued.v (a x) : with_zero (multiplicative ℤ)) = 1},
  { intros v hv,
    rw [mem_set_of_eq, map_inv₀] at hv,
    rw [mem_set_of_eq, ←inv_inj, inv_one],
    exact ne_of_gt hv, },
  exact finite.subset ha h_subset,
end

lemma right_inv' {a : Π v : height_one_spectrum R, v.adic_completion K}
  (ha : ∀ᶠ v : height_one_spectrum R in filter.cofinite,
    (valued.v (a v) : with_zero (multiplicative ℤ)) = 1)
  (h_ne_zero : ∀ v : height_one_spectrum R, a v ≠ 0)  :
  (⟨a, val_property ha h_ne_zero⟩ : finite_adele_ring' R K) *
  ⟨(λ v : height_one_spectrum R, (a v)⁻¹), inv_property ha h_ne_zero⟩ = 1 := 
begin
  ext v,
  unfold_projs,
  simp only [mul'],
  rw [subtype.coe_mk, subtype.coe_mk, pi.mul_apply, if_neg (h_ne_zero v)],
  apply uniform_space.completion.mul_hat_inv_cancel,
  exact h_ne_zero v,
end

lemma left_inv' {a : Π v : height_one_spectrum R, v.adic_completion K}
  (ha : ∀ᶠ v : height_one_spectrum R in filter.cofinite,
    (valued.v (a v) : with_zero (multiplicative ℤ)) = 1)
  (h_ne_zero : ∀ v : height_one_spectrum R, a v ≠ 0) :
  (⟨(λ v : height_one_spectrum R, (a v)⁻¹), inv_property ha h_ne_zero⟩ : finite_adele_ring' R K) *
  ⟨a, val_property ha h_ne_zero⟩ = 1 := 
by { rw mul_comm, exact right_inv' ha h_ne_zero}

/-- If `a = (a_v)_v ∈ ∏_v K_v` is such that `|a_v|_v ≠ 1` for all but finitely many `v` and
`a_v ≠ 0` for all `v`, then `a` is a finite idèle  of `R`. -/
def idele.mk (a : Π v : height_one_spectrum R, v.adic_completion K)
  (ha : ∀ᶠ v : height_one_spectrum R in filter.cofinite,
    (valued.v (a v) : with_zero (multiplicative ℤ)) = 1)
  (h_ne_zero : ∀ v : height_one_spectrum R, a v ≠ 0) :
  finite_idele_group' R K :=
⟨⟨a, val_property ha h_ne_zero⟩,
  ⟨(λ v : height_one_spectrum R, (a v)⁻¹), inv_property ha h_ne_zero⟩, right_inv' ha h_ne_zero,
  left_inv' ha h_ne_zero⟩

lemma map_to_fractional_ideals.inv_eq_inv (x : finite_idele_group' R K)
  (I : units (fractional_ideal (non_zero_divisors R) K))
  (hxI : map_to_fractional_ideals.val R K (x) = I.val) : 
  map_to_fractional_ideals.inv R K (x) = I.inv := 
begin
  have h_inv : I.val * (map_to_fractional_ideals.inv R K (x)) = 1,
  { rw ← hxI, exact finite_idele.to_add_valuations.mul_inv R K _ },
  exact eq_comm.mp (units.inv_eq_of_mul_eq_one_right h_inv),
end

variables (R K)
/-- A finite idèle `(pi_v)_v`, where each `pi_v` is a uniformizer for the `v`-adic valuation. -/
def pi.unif : Π v : height_one_spectrum R, v.adic_completion K :=
λ v : height_one_spectrum R, (coe : K → (v.adic_completion K)) 
  (classical.some (v.valuation_exists_uniformizer K))

lemma pi.unif.ne_zero : ∀ v : height_one_spectrum R, pi.unif R K v ≠ 0 :=
begin
  intro v,
  rw [pi.unif, ← uniform_space.completion.coe_zero,
    injective.ne_iff (@uniform_space.completion.coe_inj K v.adic_valued.to_uniform_space _)],
  exact v.valuation_uniformizer_ne_zero K,
end

variables {R K}
lemma idele.mk'.val {exps : Π v : height_one_spectrum R, ℤ}
  (h_exps : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, exps v = 0) :
  ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
    pi.unif R K v ^ exps v ∈ v.adic_completion_integers K :=
begin
  rw filter.eventually_cofinite at h_exps ⊢,
  simp_rw adic_completion.is_integer,
  have h_subset : {x : height_one_spectrum R |
    ¬ (valued.v (pi.unif R K x ^ exps x) : with_zero (multiplicative ℤ)) ≤ 1} ⊆ 
    {x : height_one_spectrum R | ¬exps x = 0},
  { intros v hv,
    rw mem_set_of_eq at hv ⊢,
    intro h_zero,
    rw [h_zero, zpow_zero, valuation.map_one, not_le, lt_self_iff_false] at hv,
    exact hv, },
    exact finite.subset h_exps h_subset,
end

lemma idele.mk'.inv {exps : Π v : height_one_spectrum R, ℤ}
  (h_exps : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, exps v = 0) :
  ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
    pi.unif R K v ^-exps v ∈ v.adic_completion_integers K :=
begin
  rw filter.eventually_cofinite at h_exps ⊢,
  simp_rw adic_completion.is_integer,
  have h_subset : {x : height_one_spectrum R |
    ¬ (valued.v (pi.unif R K x ^ -exps x) : with_zero (multiplicative ℤ))  ≤ 1} ⊆ 
    {x : height_one_spectrum R | ¬exps x = 0},
  { intros v hv,
    rw mem_set_of_eq at hv ⊢,
    intro h_zero,
    rw [h_zero, neg_zero, zpow_zero, valuation.map_one, not_le, lt_self_iff_false] at hv,
    exact hv, },
    exact finite.subset h_exps h_subset,
end

lemma idele.mk'.mul_inv {exps : Π v : height_one_spectrum R, ℤ}
  (h_exps : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, exps v = 0) :
  (⟨λ (v : height_one_spectrum R), pi.unif R K v ^ exps v, 
    idele.mk'.val h_exps⟩ : finite_adele_ring' R K) *
    ⟨λ (v : height_one_spectrum R), pi.unif R K v ^ -exps v, idele.mk'.inv h_exps⟩ = 1 :=
begin
  ext v,
  unfold_projs,
  simp only [mul'],
  rw [subtype.coe_mk, subtype.coe_mk, pi.mul_apply, zpow_eq_pow, zpow_eq_pow,
    ← zpow_add₀ (pi.unif.ne_zero R K v)],
  have : (exps v).neg = - exps v := rfl,
  rw [this, add_right_neg, zpow_zero],
  refl,
end

lemma idele.mk'.inv_mul {exps : Π v : height_one_spectrum R, ℤ}
  (h_exps : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, exps v = 0) :
  (⟨λ (v : height_one_spectrum R), pi.unif R K v ^-exps v, 
    idele.mk'.inv h_exps⟩ : finite_adele_ring' R K) *
    ⟨λ (v : height_one_spectrum R), pi.unif R K v ^ exps v, idele.mk'.val h_exps⟩ = 1 :=
begin
  rw mul_comm, exact idele.mk'.mul_inv h_exps,
end

variables (R K)
/-- Given a collection `exps` of integers indexed by the maximal ideals `v` of `R`, of which only
finitely many are allowed to be nonzero, `(pi_v^(exps v))_v` is a finite idèle of `R`. -/
def idele.mk' {exps : Π v : height_one_spectrum R, ℤ} (h_exps : ∀ᶠ (v : height_one_spectrum R) in
  filter.cofinite, exps v = 0) : finite_idele_group' R K :=
⟨⟨λ v : height_one_spectrum R, (pi.unif R K v)^exps v, idele.mk'.val h_exps⟩,
  ⟨λ v : height_one_spectrum R, (pi.unif R K v)^-exps v, idele.mk'.inv h_exps⟩,
  idele.mk'.mul_inv h_exps, idele.mk'.inv_mul h_exps⟩

variables {R K}
lemma idele.mk'.valuation_ne_zero {exps : Π v : height_one_spectrum R, ℤ}
  (h_exps : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, exps v = 0) :
  (valued.v ((idele.mk' R K h_exps).val.val v) : with_zero (multiplicative ℤ)) ≠ 0 :=
begin
  rw [ne.def, valuation.zero_iff],
  simp only [idele.mk'],
  intro h,
  exact pi.unif.ne_zero R K v (zpow_eq_zero h),
end

variables (R K)
/-- `map_to_fractional_ideals` is surjective. -/
lemma map_to_fractional_ideals.surjective : surjective (map_to_fractional_ideals R K) :=
begin
  rintro ⟨I, I_inv, hval_inv, hinv_val⟩,
  obtain ⟨a, J, ha, haJ⟩ := fractional_ideal.exists_eq_span_singleton_mul I,
  have hI_ne_zero : I ≠ 0 := left_ne_zero_of_mul_eq_one hval_inv,
  have hI := fractional_ideal.factorization I hI_ne_zero haJ,
  have h_exps : ∀ᶠ v : height_one_spectrum R in filter.cofinite,
  ((associates.mk v.as_ideal).count (associates.mk J).factors : ℤ) - 
    ((associates.mk v.as_ideal).count (associates.mk (ideal.span {a})).factors) = 0 :=
   fractional_ideal.finite_factors hI_ne_zero haJ,
  use idele.mk' R K h_exps,
  rw map_to_fractional_ideals,
  simp only [map_to_fractional_ideals.def, force_noncomputable_def, monoid_hom.coe_mk],
  have H : map_to_fractional_ideals.val R K (idele.mk' R K h_exps) = I,
  { simp only [map_to_fractional_ideals.val, finite_idele.to_add_valuations, ← hI],
    apply finprod_congr,
    intro v,
    apply congr_arg,
    have hv : (valued.v ((idele.mk' R K h_exps).val.val v) : with_zero (multiplicative ℤ)) ≠ 0 := 
    idele.mk'.valuation_ne_zero v h_exps,
    rw with_zero.to_integer,
    set x := classical.some (with_zero.to_integer._proof_1 hv) with hx_def,
    have hx := classical.some_spec (with_zero.to_integer._proof_1 hv),
    rw ← hx_def at hx ⊢,
    simp only [idele.mk', pi.unif] at hx,
    rw [map_zpow₀, height_one_spectrum.valued_adic_completion_def,
      valued.extension_extends, v.adic_valued_apply, classical.some_spec
      (v.valuation_exists_uniformizer K), ← with_zero.coe_zpow, with_zero.coe_inj] at hx,
    rw [hx, ← of_add_zsmul, to_add_of_add, algebra.id.smul_eq_mul, mul_neg,
          mul_one, neg_neg] },
  exact ⟨H, map_to_fractional_ideals.inv_eq_inv _ ⟨I, I_inv, hval_inv, hinv_val⟩ H⟩,
end

variables {R K}
/-- A finite idèle `x` is in the kernel of `map_to_fractional_ideals` if and only if `|x_v|_v = 1` 
for all `v`. -/ 
lemma map_to_fractional_ideals.mem_kernel_iff (x : finite_idele_group' R K) : 
  map_to_fractional_ideals R K x = 1 ↔ 
  ∀ v : height_one_spectrum R, finite_idele.to_add_valuations R K x v = 0 :=
begin
  rw [map_to_fractional_ideals, monoid_hom.coe_mk, map_to_fractional_ideals.def,
    force_noncomputable_def],
  simp_rw map_to_fractional_ideals.val,
  rw [units.ext_iff, units.coe_mk, units.coe_one],
  refine ⟨λ h_ker, _, λ h_val, _⟩,
  { intro v,
    rw [← fractional_ideal.count_finprod K v (finite_idele.to_add_valuations R K x),
      ← fractional_ideal.count_one K v, h_ker],
    exact finite_add_support R K x, },
  { rw ← @finprod_one _ (height_one_spectrum R) _,
    apply finprod_congr,
    intro v,
    rw [h_val v, zpow_zero _] }
end

variables (R K)
/-- The additive `v`-adic valuation of `x_v` equals 0 if and only if `|x_v|_v = 1`-/
lemma finite_idele.to_add_valuations.comp_eq_zero_iff (x : finite_idele_group' R K) : 
  finite_idele.to_add_valuations R K x v = 0 ↔ 
  (valued.v (x.val.val v) : with_zero (multiplicative ℤ)) = 1 :=
begin
  set y := classical.some (with_zero.to_integer._proof_1 
    (finite_idele.to_add_valuations._proof_1 R K x v)) with hy,
  have hy_spec := classical.some_spec (with_zero.to_integer._proof_1 
    (finite_idele.to_add_valuations._proof_1 R K x v)),
  rw ← hy at hy_spec,
  rw [finite_idele.to_add_valuations, neg_eq_zero ,with_zero.to_integer, ← to_add_one, ← hy,
    ← hy_spec, ← with_zero.coe_one, with_zero.coe_inj],
  refine ⟨λ h_eq, by rw [← of_add_to_add y, ← of_add_to_add 1, h_eq], λ h_eq, by rw h_eq⟩,
end

/-- `|x_v|_v = 1` if and only if both `x_v` and `x⁻¹_v` are in `R_v`. -/
lemma finite_idele.valuation_eq_one_iff (x : finite_idele_group' R K) : 
  (valued.v (x.val.val v) : with_zero (multiplicative ℤ)) = 1 ↔ 
  x.val.val v ∈ v.adic_completion_integers K ∧ x⁻¹.val.val v ∈ v.adic_completion_integers K :=
begin
  rw [adic_completion.is_integer, adic_completion.is_integer],
  refine ⟨λ h_one, _, λ h_int, _⟩,
  { have h_mul := valuation_val_inv R K v x,
    rw [h_one, one_mul] at h_mul,
    exact ⟨ le_of_eq h_one, le_of_eq h_mul ⟩ , },
  { have : x.inv = x⁻¹.val := rfl,
    rw [← this, valuation_inv, ← inv_one, inv_le_inv₀, inv_one] at h_int,
    rw [eq_iff_le_not_lt, not_lt],
    exact h_int,
    { exact (valuation.ne_zero_iff _).mpr (v_comp.ne_zero R K v x)},
    { exact one_ne_zero }}
end

/-- `map_to_fractional_ideals` is continuous, where the codomain is given the discrete topology. -/
lemma map_to_fractional_ideals.continuous : continuous (map_to_fractional_ideals R K) := 
begin
  apply uniform_continuous.continuous,
  rw uniform_group.uniform_continuous_iff_open_ker,  
  have h_ker : ((map_to_fractional_ideals R K).ker : set (finite_idele_group' R K)) = 
    { x : units(finite_adele_ring' R K) |
       ∀ v : height_one_spectrum R, finite_idele.to_add_valuations R K x v = 0 },
  { ext x,
    exact map_to_fractional_ideals.mem_kernel_iff x, },
  change is_open ↑((map_to_fractional_ideals R K).ker),
  rw h_ker,
  use {p : (finite_adele_ring' R K × (finite_adele_ring' R K)ᵐᵒᵖ) | 
    ∀ v : height_one_spectrum R, (p.1.val v) ∈ v.adic_completion_integers K ∧ 
    ((mul_opposite.unop p.2).val v) ∈ v.adic_completion_integers K},
  split,
  { rw [is_open_prod_iff],
    intros x y hxy,
    rw mem_set_of_eq at hxy,
    use {x : finite_adele_ring' R K | ∀ (v : height_one_spectrum R),
      x.val v ∈ v.adic_completion_integers K},
    use {x : (finite_adele_ring' R K )ᵐᵒᵖ | ∀ (v : height_one_spectrum R), 
      (mul_opposite.unop x).val v ∈ v.adic_completion_integers K},
    refine ⟨finite_adele_ring'.is_open_integer_subring R K, 
      finite_adele_ring'.is_open_integer_subring_opp R K, λ v, (hxy v).1, λ v, (hxy v).2, _⟩,
    { intros p hp v,
      exact ⟨ hp.1 v, hp.2 v⟩, }},
  { rw preimage_set_of_eq,
    ext x,
    rw [mem_set_of_eq, units.embed_product, monoid_hom.coe_mk, mul_opposite.unop_op],
    simp_rw [finite_idele.to_add_valuations.comp_eq_zero_iff, finite_idele.valuation_eq_one_iff],
    refl, },
end