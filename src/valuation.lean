import algebraic_geometry.prime_spectrum.basic
import ring_theory.dedekind_domain
import topology.algebra.valued_field

noncomputable theory
open_locale classical

section valuation
variables {S : Type*} [ring S] {Γ₀ : Type*} [linear_ordered_comm_monoid_with_zero Γ₀]
  (v : valuation S Γ₀) {x y z : S}

lemma valuation.def : v x = v.to_fun x := rfl

end valuation

variables (R : Type) {K : Type} [comm_ring R] [is_domain R] [is_dedekind_domain R] [field K]
  [algebra R K] [is_fraction_ring R K] 

-- Note : not the maximal spectrum if R is a field
def maximal_spectrum := {v : prime_spectrum R // v.val ≠ 0 }
variable (v : maximal_spectrum R)

variable {R}
--Maximal spectrum lemmas
lemma associates.irreducible_of_maximal (v : maximal_spectrum R) :
  irreducible (associates.mk v.val.val) := 
begin
  rw [associates.irreducible_mk _, unique_factorization_monoid.irreducible_iff_prime],
  apply ideal.prime_of_is_prime v.property v.val.property,
end

lemma ideal.irreducible_of_maximal (v : maximal_spectrum R) :
  irreducible v.val.val := 
begin
  rw [unique_factorization_monoid.irreducible_iff_prime],
  apply ideal.prime_of_is_prime v.property v.val.property,
end

lemma ideal.prime_of_maximal (v : maximal_spectrum R) :
  prime v.val.val := 
begin
  apply ideal.prime_of_is_prime v.property v.val.property,
end

-- of_add lemmas
lemma of_add_le (α : Type*) [has_add α] [partial_order α] (x y : α) :
  multiplicative.of_add x ≤ multiplicative.of_add y ↔ x ≤ y := by refl

lemma of_add_lt (α : Type*) [has_add α] [partial_order α] (x y : α) :
  multiplicative.of_add x < multiplicative.of_add y ↔ x < y := by refl

lemma of_add_inj (α : Type*) [has_add α] (x y : α) 
  (hxy : multiplicative.of_add x = multiplicative.of_add y) : x = y := 
by rw [← to_add_of_add x, ← to_add_of_add y, hxy]

-- is_localization lemmas
lemma is_localization.mk'_eq_zero_of_num_zero {R : Type*} [comm_ring R] {M : submonoid R}
  {S : Type*} [comm_ring S] [algebra R S] [is_localization M S] {z : S}  {x : R} {y : M}
  (hxyz : z = is_localization.mk' S x y) (hx : x = 0) : z = 0 := 
by rw [hxyz, hx, eq_comm, is_localization.eq_mk'_iff_mul_eq, zero_mul, ring_hom.map_zero]

lemma is_localization.mk'_num_ne_zero_of_ne_zero {R : Type*} [comm_ring R] {M : submonoid R}
  {S : Type*} [comm_ring S] [algebra R S] [is_localization M S] {z : S}  {x : R} {y : M}
  (hxyz : z = is_localization.mk' S x y) (hz : z ≠ 0) : x ≠ 0 := 
λ hx, hz (is_localization.eq_zero_of_fst_eq_zero (is_localization.eq_mk'_iff_mul_eq.mp hxyz) hx)

variables {A : Type*} [comm_ring A] [is_domain A] {S : Type*} [field S] [algebra A S]
  [is_fraction_ring A S]

lemma is_localization.mk'_eq_zero {r : A} {s : non_zero_divisors A}
  (h : is_localization.mk' S r s = 0) : r = 0 := 
begin
  rw [is_fraction_ring.mk'_eq_div, div_eq_zero_iff] at h,
  apply is_fraction_ring.injective A S,
  rw (algebra_map A S).map_zero,
  exact or.resolve_right h (is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors s.property),
end

variable (S)
lemma is_localization.mk'_eq_one {r : A} {s : non_zero_divisors A}
  (h : is_localization.mk' S r s = 1) : r = s :=
begin
  rw [is_fraction_ring.mk'_eq_div, div_eq_one_iff_eq] at h,
  exact is_fraction_ring.injective A S h,
  exact is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors s.property,
end 

-- Ideal associates lemmas
@[simp] lemma associates.mk_ne_zero' {x : R} : 
  (associates.mk (ideal.span{x} : ideal R)) ≠ 0 ↔ (x ≠ 0):=
begin
  rw associates.mk_ne_zero,
  rw [ideal.zero_eq_bot, ne.def, ideal.span_singleton_eq_bot],
end

lemma associates.le_singleton_iff (x : R) (n : ℕ) (I : ideal R) :
  associates.mk I^n ≤ associates.mk (ideal.span {x}) ↔ x ∈ I^n :=
begin
  rw [← associates.dvd_eq_le, ← associates.mk_pow, associates.mk_dvd_mk, ideal.dvd_span_singleton],
end

-- Ideal lemmas
lemma ideal.mem_pow_count {x : R} (hx : x ≠ 0) {I : ideal R} (hI : irreducible I) :
  x ∈ I^((associates.mk I).count (associates.mk (ideal.span {x})).factors) :=
begin
  have hx' := associates.mk_ne_zero'.mpr hx,
  rw [← associates.le_singleton_iff, 
    associates.prime_pow_dvd_iff_le hx' ((associates.irreducible_mk I).mpr hI)],
end   

lemma ideal.mem_le_pow {x : R}  (hx : x ≠ 0) {I : ideal R} (hI : irreducible I)
  {n : ℕ} (hxI : x ∈ I^n) : ∀ m : ℕ, m ≤ n → x ∈ I^m :=
begin
  have hx' := associates.mk_ne_zero'.mpr hx,
  intros m hm,
  rw [← associates.le_singleton_iff x _ I, 
    associates.prime_pow_dvd_iff_le hx' ((associates.irreducible_mk I).mpr hI)] at hxI ⊢,
  exact le_trans hm hxI,
end 

/-! Adic valuation on the Dedekind domain R -/

def ring.adic_valuation.def (r : R) : with_zero (multiplicative ℤ) :=
dite (r = 0) (λ (h : r = 0), 0) (λ h : ¬ r = 0, (multiplicative.of_add
  (-(associates.mk v.val.val).count (associates.mk (ideal.span{r} : ideal R)).factors : ℤ)))

lemma ring.adic_valuation.def.dif_pos {r : R} (hr : r = 0) :
  ring.adic_valuation.def v r = 0 :=
by rw [ring.adic_valuation.def, dif_pos hr]

lemma ring.adic_valuation.def.dif_neg {r : R} (hr : r ≠ 0) :
  ring.adic_valuation.def v r = (multiplicative.of_add
  (-(associates.mk v.val.val).count (associates.mk (ideal.span{r} : ideal R)).factors : ℤ)) :=
by rw [ring.adic_valuation.def, dif_neg hr]

lemma ring.adic_valuation.map_zero' : ring.adic_valuation.def v 0 = 0 := 
by { rw [ring.adic_valuation.def, dif_pos], refl, }

lemma ring.adic_valuation.map_one' : ring.adic_valuation.def v 1 = 1 := 
begin
  rw [ring.adic_valuation.def, dif_neg (ne.symm zero_ne_one)],
  { rw [← with_zero.coe_one, with_zero.coe_inj, ← of_add_zero],
    apply congr_arg,
    rw [neg_eq_zero, int.coe_nat_eq_zero, ideal.span_singleton_one, ← ideal.one_eq_top,
      associates.mk_one, associates.factors_one,
      associates.count_zero _],
    apply associates.irreducible_of_maximal v },
  { by apply_instance }
end

lemma ring.adic_valuation.map_mul' (x y : R) :
  ring.adic_valuation.def v (x * y) = ring.adic_valuation.def v x * ring.adic_valuation.def v y :=
begin
  rw [ring.adic_valuation.def, ring.adic_valuation.def, ring.adic_valuation.def],
  by_cases hx : x = 0,
  { rw [hx, zero_mul, dif_pos (eq.refl _), zero_mul] },
  { by_cases hy : y = 0,
    { rw [hy, mul_zero, dif_pos (eq.refl _), mul_zero] },
    { rw [dif_neg hx, dif_neg hy, dif_neg (mul_ne_zero hx hy), ← with_zero.coe_mul,
        with_zero.coe_inj, ← of_add_add],
      have hx' : associates.mk (ideal.span{x} : ideal R) ≠ 0 := associates.mk_ne_zero'.mpr hx,
      have hy' : associates.mk (ideal.span{y} : ideal R) ≠ 0 := associates.mk_ne_zero'.mpr hy,
      rw [← ideal.span_singleton_mul_span_singleton, ← associates.mk_mul_mk, ← neg_add,
        associates.count_mul hx' hy' _],
      { refl },
      { apply (associates.irreducible_of_maximal v), }}}
end

lemma ring.adic_valuation.map_add' (x y : R) : ring.adic_valuation.def v (x + y) ≤
  max (ring.adic_valuation.def v x) (ring.adic_valuation.def v y) := 
begin
  by_cases hx : x = 0,
  { rw [hx, zero_add],
    conv_rhs {rw [ring.adic_valuation.def, dif_pos (eq.refl _)]},
    rw max_eq_right (with_zero.zero_le (ring.adic_valuation.def v y)),
    exact le_refl _, },
  { by_cases hy : y = 0,
    { rw [hy, add_zero],
      conv_rhs {rw [max_comm, ring.adic_valuation.def, dif_pos (eq.refl _)]},
        rw max_eq_right (with_zero.zero_le (ring.adic_valuation.def v x)), 
        exact le_refl _ },
    { by_cases hxy : x + y = 0,
      { rw [ring.adic_valuation.def, dif_pos hxy], exact zero_le',},
      { rw [ring.adic_valuation.def, ring.adic_valuation.def, ring.adic_valuation.def,
          dif_neg hxy, dif_neg hx, dif_neg hy],
      rw [le_max_iff, with_zero.coe_le_coe, of_add_le, with_zero.coe_le_coe, of_add_le,
        neg_le_neg_iff, neg_le_neg_iff, int.coe_nat_le, int.coe_nat_le, ← min_le_iff],
      set nmin := min 
        ((associates.mk v.val.val).count (associates.mk (ideal.span {x})).factors)
        ((associates.mk v.val.val).count (associates.mk (ideal.span {y})).factors),
      have hx' : (associates.mk (ideal.span {x} : ideal R)) ≠ 0 := associates.mk_ne_zero'.mpr hx,
      have hy' : (associates.mk (ideal.span {y} : ideal R)) ≠ 0 := associates.mk_ne_zero'.mpr hy,
      have hxy' : (associates.mk (ideal.span {x + y} : ideal R)) ≠ 0 := 
      associates.mk_ne_zero'.mpr hxy,
      have h_dvd_x : x ∈ v.val.val ^ (nmin),
      { rw [← associates.le_singleton_iff x nmin _],
       rw [associates.prime_pow_dvd_iff_le hx' _],
       exact min_le_left _ _,
        apply associates.irreducible_of_maximal v,
      },
      have h_dvd_y : y ∈ v.val.val ^ nmin,
      { rw [← associates.le_singleton_iff y nmin _, associates.prime_pow_dvd_iff_le hy' _],
        exact min_le_right _ _,
        apply associates.irreducible_of_maximal v,
      },
      have h_dvd_xy : associates.mk v.val.val^nmin ≤ associates.mk (ideal.span {x + y}),
      { rw associates.le_singleton_iff,
        exact ideal.add_mem (v.val.val^nmin) h_dvd_x h_dvd_y, },
      rw (associates.prime_pow_dvd_iff_le hxy' _) at h_dvd_xy,
      exact h_dvd_xy,
      apply associates.irreducible_of_maximal v, }}}
end

/-! Adic valuation on the ring of fractions -/

def ring.adic_valuation (v : maximal_spectrum R) : valuation R (with_zero (multiplicative ℤ)) :=
{ to_fun    := ring.adic_valuation.def v, 
  map_zero' := ring.adic_valuation.map_zero' v,
  map_one'  := ring.adic_valuation.map_one' v,
  map_mul'  := ring.adic_valuation.map_mul' v,
  map_add'  := ring.adic_valuation.map_add' v }

lemma ring.adic_valuation.ne_zero (v : maximal_spectrum R) (x : non_zero_divisors R) :
  ring.adic_valuation.def v x ≠ 0 :=
begin
  rw [ring.adic_valuation.def, dif_neg (non_zero_divisors.coe_ne_zero x)],
  exact with_zero.coe_ne_zero,
end

lemma ring.adic_valuation.ne_zero' (v : maximal_spectrum R) (x : R) (hx : x ≠ 0) :
  ring.adic_valuation.def v x ≠ 0 :=
begin
  rw [ring.adic_valuation.def, dif_neg hx],
  exact with_zero.coe_ne_zero,
end

lemma ring.adic_valuation.zero_le (v : maximal_spectrum R)
(x : non_zero_divisors R) : 0 < ring.adic_valuation.def v x :=
begin
  rw [ring.adic_valuation.def, dif_neg (non_zero_divisors.coe_ne_zero x)],
  exact with_zero.zero_lt_coe _,
end

lemma ring.adic_valuation.le_one (x : R) : ring.adic_valuation.def v x ≤ 1 :=
begin
  rw ring.adic_valuation.def,
  by_cases hx : x = 0,
  { rw dif_pos hx, exact with_zero.zero_le 1,},
  { rw [dif_neg hx, ← with_zero.coe_one, ← of_add_zero, with_zero.coe_le_coe, of_add_le,
      right.neg_nonpos_iff],
    exact int.coe_nat_nonneg _, }
end

lemma ring.adic_valuation.lt_one_iff_dvd (r : R) : 
  ring.adic_valuation.def v r < 1 ↔ v.val.val ∣ ideal.span {r} :=
begin
  rw ring.adic_valuation.def,
  split_ifs with hr,
  { rw [hr, ideal.dvd_span_singleton], 
    simp only [submodule.zero_mem],
    rw [iff_true, ← with_zero.coe_one],
     exact with_zero.zero_lt_coe 1, },
  { rw [← with_zero.coe_one, ← of_add_zero, with_zero.coe_lt_coe, of_add_lt, neg_lt_zero,
      ← int.coe_nat_zero, int.coe_nat_lt, zero_lt_iff],
    apply associates.count_ne_zero_iff_dvd,
    { rw [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot], exact hr },
    { apply ideal.irreducible_of_maximal v }}
end

lemma ideal.is_nonunit_iff {I : ideal R} : ¬ is_unit I ↔ I ≠ ⊤ := by rw ideal.is_unit_iff

lemma ring.adic_valuation.exists_uniformizer : 
  ∃ (π : R), ring.adic_valuation.def v π = multiplicative.of_add (-1 : ℤ) := 
begin
  have hv : irreducible (associates.mk v.val.val) := associates.irreducible_of_maximal v,
  have hlt : v.val.val^2 < v.val.val,
  { rw ← ideal.dvd_not_unit_iff_lt,
    exact ⟨v.property, v.val.val,
     ideal.is_nonunit_iff.mpr (ideal.is_prime.ne_top v.val.property), sq v.val.val⟩ } ,
  obtain ⟨π, mem, nmem⟩ := set_like.exists_of_lt hlt,
  have hπ : associates.mk (ideal.span {π}) ≠ 0,
  { rw associates.mk_ne_zero',
    intro h,
    rw h at nmem,
    exact nmem (submodule.zero_mem (v.val.val^2)), },
  use π,
  rw [ring.adic_valuation.def, dif_neg (associates.mk_ne_zero'.mp hπ), with_zero.coe_inj],
  apply congr_arg, 
  rw [neg_inj, ← int.coe_nat_one, int.coe_nat_inj'],
  rw [← ideal.dvd_span_singleton, ← associates.mk_le_mk_iff_dvd_iff] at mem nmem,
  rw [← pow_one ( associates.mk v.val.val), 
    associates.prime_pow_dvd_iff_le hπ hv]  at mem,
  rw [associates.mk_pow, associates.prime_pow_dvd_iff_le hπ hv, not_le] at nmem,
  exact nat.eq_of_le_of_lt_succ mem nmem,
end

def adic_valuation.def (v : maximal_spectrum R) (x : K) : (with_zero (multiplicative ℤ)) :=
let s := classical.some (classical.some_spec (is_localization.mk'_surjective
  (non_zero_divisors R) x)) in (ring.adic_valuation.def v (classical.some
    (is_localization.mk'_surjective (non_zero_divisors R) x)))/(ring.adic_valuation.def v s)

variable (K)
lemma adic_valuation.well_defined (v : maximal_spectrum R) {r r' : R} {s s' : non_zero_divisors R} 
  (h_mk : is_localization.mk' K r s = is_localization.mk' K r' s') :
  (ring.adic_valuation.def v r)/(ring.adic_valuation.def v s) =
  (ring.adic_valuation.def v r')/(ring.adic_valuation.def v s') := 
begin
  rw [div_eq_div_iff (ring.adic_valuation.ne_zero v s) (ring.adic_valuation.ne_zero v s'),
  ← ring.adic_valuation.map_mul' v, ← ring.adic_valuation.map_mul' v,
  is_fraction_ring.injective R K (is_localization.mk'_eq_iff_eq.mp h_mk)],
end

lemma adic_valuation.of_mk' {r : R} {s : non_zero_divisors R} :
  adic_valuation.def v (is_localization.mk' K r s) =
   (ring.adic_valuation.def v r)/(ring.adic_valuation.def v s) :=
begin
  rw adic_valuation.def,
  exact adic_valuation.well_defined K v
   (classical.some_spec (adic_valuation.def._proof_2 (is_localization.mk' K r s))),
end

variable {K}
lemma adic_valuation.of_algebra_map {r : R} :
  adic_valuation.def v (algebra_map R K r) = ring.adic_valuation.def v r :=
begin
  rw [← is_localization.mk'_one K r, adic_valuation.of_mk', submonoid.coe_one, 
    ring.adic_valuation.map_one' v, div_one _],
end

lemma adic_valuation.le_one (r : R) : adic_valuation.def v (algebra_map R K r) ≤ 1 :=
begin
  rw adic_valuation.of_algebra_map v,
  exact ring.adic_valuation.le_one v r,
end

lemma adic_valuation.lt_one_iff_dvd (r : R) : 
  adic_valuation.def v (algebra_map R K r) < 1 ↔ v.val.val ∣ ideal.span {r} :=
begin
  rw adic_valuation.of_algebra_map v,
  exact ring.adic_valuation.lt_one_iff_dvd v r,
end

variable {K}

lemma adic_valuation.map_zero' (v : maximal_spectrum R) :
adic_valuation.def v (0 : K) = 0 := 
begin
  rw [← (algebra_map R K).map_zero, adic_valuation.of_algebra_map v],
  exact ring.adic_valuation.map_zero' v,
end

lemma adic_valuation.map_one' (v : maximal_spectrum R) :
adic_valuation.def v (1 : K) = 1 := 
begin
  rw [← (algebra_map R K).map_one, adic_valuation.of_algebra_map v],
  exact ring.adic_valuation.map_one' v,
end

lemma adic_valuation.map_mul' (v : maximal_spectrum R)
(x y : K) : adic_valuation.def v (x * y) = adic_valuation.def v x * adic_valuation.def v y :=
begin
  rw [adic_valuation.def, adic_valuation.def, adic_valuation.def, div_mul_div _ _ _ _,
    ← ring.adic_valuation.map_mul', ← ring.adic_valuation.map_mul', ← submonoid.coe_mul],
  apply adic_valuation.well_defined K v,
  rw [(classical.some_spec (adic_valuation.def._proof_2 (x * y))), is_fraction_ring.mk'_eq_div,
    (algebra_map R K).map_mul, submonoid.coe_mul, (algebra_map R K).map_mul, ← div_mul_div,
    ← is_fraction_ring.mk'_eq_div, ← is_fraction_ring.mk'_eq_div,
    (classical.some_spec (adic_valuation.def._proof_2 x)),
    (classical.some_spec (adic_valuation.def._proof_2 y))],
end

lemma adic_valuation.map_add' (v : maximal_spectrum R) (x y : K) :
  adic_valuation.def v (x + y) ≤ max (adic_valuation.def v x)  (adic_valuation.def v y) := 
begin
  rw [adic_valuation.def, adic_valuation.def, adic_valuation.def, le_max_iff],
  dsimp only,
  let rxy : R := (classical.some (adic_valuation.def._proof_1 (x + y))),
  let sxy : non_zero_divisors R := (classical.some (adic_valuation.def._proof_2 (x + y))),
  let rx : R := (classical.some (adic_valuation.def._proof_1 x)),
  let sx : non_zero_divisors R := (classical.some (adic_valuation.def._proof_2 x)),
  let ry : R := (classical.some (adic_valuation.def._proof_1 y)),
  let sy : non_zero_divisors R := (classical.some (adic_valuation.def._proof_2 y)),
  have h_frac_xy : is_localization.mk' K rxy sxy = 
    is_localization.mk' K (rx*(sy : R) + ry*(sx : R)) (sx*sy),
  { rw [is_localization.mk'_add, classical.some_spec (adic_valuation.def._proof_2 (x + y)),
    classical.some_spec (adic_valuation.def._proof_2 x),
    classical.some_spec (adic_valuation.def._proof_2 y)] },
  have h_frac_x : is_localization.mk' K rx sx = is_localization.mk' K (rx*(sy : R)) (sx*sy),
  { rw [is_localization.mk'_eq_iff_eq, submonoid.coe_mul, mul_assoc, mul_comm (sy : R) _], },
  have h_frac_y : is_localization.mk' K ry sy = is_localization.mk' K (ry*(sx : R)) (sx*sy),
  { rw [is_localization.mk'_eq_iff_eq, submonoid.coe_mul, mul_assoc], },
  have h_denom : 0 < ring.adic_valuation.def v ↑(sx * sy),
  { rw [ring.adic_valuation.def, dif_neg _], 
    exact with_zero.zero_lt_coe _,
    exact non_zero_divisors.ne_zero
      (submonoid.mul_mem (non_zero_divisors R) sx.property sy.property), },

  rw [adic_valuation.well_defined K v h_frac_x, adic_valuation.well_defined K v h_frac_y,
    adic_valuation.well_defined K v h_frac_xy, div_le_div_right₀ (ne_of_gt h_denom), 
    div_le_div_right₀ (ne_of_gt h_denom), ← le_max_iff],
  exact ring.adic_valuation.map_add' v _ _,
end

def adic_valuation (v : maximal_spectrum R) : valuation K (with_zero (multiplicative ℤ)) := { 
  to_fun    := adic_valuation.def v, 
  map_zero' := adic_valuation.map_zero' v,
  map_one'  := adic_valuation.map_one' v, 
  map_mul'  := adic_valuation.map_mul' v, 
  map_add'  := adic_valuation.map_add' v }

variable (K)
lemma adic_valuation.exists_uniformizer : 
  ∃ (π : K), adic_valuation.def v π = multiplicative.of_add (-1 : ℤ) := 
begin
  obtain ⟨r, hr⟩ := ring.adic_valuation.exists_uniformizer v,
  use algebra_map R K r,
  rw adic_valuation.of_algebra_map v,
  exact hr,
end

lemma adic_valuation.uniformizer_ne_zero :
  (classical.some (adic_valuation.exists_uniformizer K v)) ≠ 0 :=
begin
  have hu := (classical.some_spec (adic_valuation.exists_uniformizer K v)),
  have h : adic_valuation.def v (classical.some _) = adic_valuation v (classical.some _) := rfl,
  rw h at hu,
  exact (valuation.ne_zero_iff _).mp (ne_of_eq_of_ne hu with_zero.coe_ne_zero),
end

