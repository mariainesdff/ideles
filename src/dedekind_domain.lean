import algebra.field_power
import algebraic_geometry.prime_spectrum
import ring_theory.dedekind_domain
import topology.algebra.valued_field

noncomputable theory
open_locale classical

variables (R K : Type) [integral_domain R] [is_dedekind_domain R] [field K] [algebra R K]
  [is_fraction_ring R K] [decidable_eq K]

def le (x y : with_zero (multiplicative ℤ)) : Prop := 
dite (x = 0) (λ (h : x = 0), true) (λ (hx : ¬ x = 0), dite (y = 0) (λ (h : y = 0), false) (λ (hy : ¬ y = 0), classical.some (or.resolve_left (group_with_zero.eq_zero_or_unit x) hx) ≤  classical.some (or.resolve_left (group_with_zero.eq_zero_or_unit y) hy)))

lemma le_def (x y : with_zero (multiplicative ℤ)) : le x y ↔
dite (x = 0) (λ (h : x = 0), true) (λ (hx : ¬ x = 0), dite (y = 0) (λ (h : y = 0), false) (λ (hy : ¬ y = 0), classical.some (or.resolve_left (group_with_zero.eq_zero_or_unit x) hx) ≤  classical.some (or.resolve_left (group_with_zero.eq_zero_or_unit y) hy))) := 
by { rw le }

lemma zero_of_le_zero (x : with_zero (multiplicative ℤ)) (hx : le x 0) : x = 0 := 
begin
  by_cases h_zero : x = 0,
  { exact h_zero },
  { rw [le, dif_neg h_zero, dif_pos (eq.refl _)] at hx,
    exfalso, exact hx }
end

instance bar : comm_group_with_zero (with_zero (multiplicative ℤ)) := infer_instance
instance foo : linear_ordered_comm_group_with_zero (with_zero (multiplicative ℤ)) := 
{ le := le,
  le_refl := λ x,
  begin
    simp only [le, dite_eq_ite,le_refl,  if_false_left_eq_and, and_true, if_true_left_eq_or],
    tauto,
  end,
  le_trans := λ x y z hxy hyz,
  begin
    by_cases hx : x = 0,
    { rw hx, simp only [le, dif_pos]},
    { by_cases hy : y = 0,
      { rw hy at hxy,
        exact absurd (zero_of_le_zero x hxy) hx,},
      { have hz : z ≠ 0,
        { by_contradiction h,
          rw not_not.mp h at hyz,
          exact hy (zero_of_le_zero y hyz)},
        simp only [le] at hxy hyz ⊢,
        rw dif_neg hx at hxy ⊢,
        rw dif_neg hy at hxy hyz,
        rw dif_neg hz at hyz ⊢,
        exact le_trans hxy hyz,
        }}
  end,
  le_antisymm := λ x y hxy hyx,
  begin
    by_cases hx : x = 0,
    { rw hx at hyx ⊢,
      rw (zero_of_le_zero y hyx) },
    { by_cases hy : y = 0,
      { rw hy at hxy, exact absurd (zero_of_le_zero x hxy) hx},
      { simp only [has_le.le, le] at hxy hyx,
        rw [dif_neg hy, dif_neg hx] at hyx,
        rw [dif_neg hx, dif_neg hy] at hxy,
        rw [classical.some_spec (or.resolve_left (group_with_zero.eq_zero_or_unit x) hx),
          classical.some_spec (or.resolve_left (group_with_zero.eq_zero_or_unit y) hy)],
        exact le_antisymm hxy hyx,
        }}
  end,
  le_total := λ x y,
  begin
     by_cases hx : x = 0,
    { sorry },
    { by_cases hy : y = 0,
      { sorry },
      { simp only [has_le.le, preorder.le],
        sorry,
        /- simp only [dif_neg hx, dif_neg hy],
        let ux := classical.some (or.resolve_left (group_with_zero.eq_zero_or_unit x) hx),
        let uy := classical.some (or.resolve_left (group_with_zero.eq_zero_or_unit y) hy),
        cases h_tot : le_total ux uy,
        { left, intros a ha,
          sorry} -/
        }}
  end,
  decidable_le := classical.dec_rel _,
  mul_le_mul_left := sorry,
  zero_le_one := begin
    change le 0 1,
    rw [le, dif_pos (eq.refl _)], tauto,
  end,
  ..bar }



def pow_n (e : ℚ) := λ (n : ℤ), e^n
def Γ₀ {e : ℚ} (he : 1 < e) := (pow_n e) '' (set.univ) ∪ {0}

instance locmwz {e : ℚ} (he : 1 < e) : linear_ordered_comm_monoid_with_zero (Γ₀ he) := {
  le               := λ x y, x.val ≤ y.val,
  lt               := λ x y, x.val < y.val,
  le_refl          := le_refl,
  le_trans         := λ x y z, le_trans,
  lt_iff_le_not_le := λ x y, lt_iff_le_not_le,
  le_antisymm      := λ x y hxy hyx, le_antisymm hxy hyx,
  le_total         := λ x y, rat.le_total x y,
  decidable_le     := λ x y, rat.decidable_le x y,
  mul              := λ ⟨x, hx⟩ ⟨y, hy⟩, ⟨ x*y,
    begin
      cases hx,
      { cases hy,
        { left,
        obtain ⟨nx, -, hnx⟩ := hx,
        obtain ⟨ny, -, hny⟩ := hy,
        use [nx + ny, set.mem_univ _],
        rw [← hnx, ← hny, pow_n],
        apply fpow_add,
        exact ne_of_gt (lt_trans zero_lt_one he),},
        { right, rw [set.mem_singleton_iff.mp hy, mul_zero], exact set.mem_singleton 0}},
      { right, rw [set.mem_singleton_iff.mp hx, zero_mul], exact set.mem_singleton 0 }
    end⟩,          
  mul_assoc        := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩, by {ext, exact mul_assoc _ _ _,},
  one              := ⟨1, set.mem_union_left _ ⟨ 0, set.mem_univ 0, pow_zero e⟩⟩,
  one_mul          := λ ⟨x, hx⟩, by { ext, exact one_mul x },
  mul_one          := λ ⟨x, hx⟩, by { ext, exact mul_one x },
  mul_comm         := λ ⟨x, hx⟩ ⟨y, hy⟩, by {ext, exact mul_comm _ _ },
  mul_le_mul_left  := λ ⟨x, hx⟩ ⟨y, hy⟩ hxy ⟨c, hc⟩, by 
  { change c*x ≤ c*y, 
    cases hc,
    { obtain ⟨n, -, hnc⟩ := hc,
      rw pow_n at hnc, dsimp only at hnc,
      have hc_pos : 0 < c,
      { rw ← hnc,
        exact fpow_pos_of_pos (lt_trans (zero_lt_one) he) n, },
      exact (mul_le_mul_left hc_pos).mpr hxy, },
    { rw [set.mem_singleton_iff.mp hc, zero_mul, zero_mul], }   },
  zero             := ⟨ 0, set.mem_union_right _ (set.mem_singleton 0)⟩,
  zero_mul         := λ ⟨x, hx⟩, by { ext, exact zero_mul x, },
  mul_zero         := λ ⟨x, hx⟩, by { ext, exact mul_zero x, },
  zero_le_one      := by { change (0 : ℚ) ≤ 1, exact zero_le_one, }}

instance locgwz {e : ℚ} (he : 1 < e) : linear_ordered_comm_group_with_zero (Γ₀ he) := { 
  inv := λ ⟨x, hx⟩, if x = 0 then 0 else ⟨x⁻¹, by {sorry}⟩,
  exists_pair_ne := begin
    use ⟨0, by {right, exact set.mem_singleton 0}⟩,
    use ⟨1, set.mem_union_left _ ⟨ 0, set.mem_univ 0, pow_zero e⟩⟩,
    rw ne.def,
    simp_rw subtype.mk_eq_mk,
    exact zero_ne_one,
  end,
  inv_zero := rfl,
  mul_inv_cancel := λ ⟨x, hx⟩ hx_ne_zero, by { ext, sorry },
  ..locmwz he }

  -- Note : not the maximal spectrum if R is a field
def maximal_spectrum := {v : prime_spectrum R // v.as_ideal ≠ 0 }

def adic_valuation.def (v : maximal_spectrum R) {e : ℚ} (he : 1 < e) (x : K) (hx : x ≠ 0) : Γ₀ he :=
let s := classical.some (classical.some_spec (is_localization.mk'_surjective (non_zero_divisors R) x)) in 
  let val := (multiset.count v.val.as_ideal (unique_factorization_monoid.factors (ideal.span{classical.some (is_localization.mk'_surjective (non_zero_divisors R) x)} : ideal R)) : ℤ) - (multiset.count v.val.as_ideal (unique_factorization_monoid.factors (ideal.span{s} : ideal R)) : ℤ) in ⟨ e^val, set.mem_union_left _ ⟨val, set.mem_univ val, rfl⟩⟩ 

def ring.adic_valuation.def (v : maximal_spectrum R) {e : ℚ} (he : 1 < e) (r : R) (hx : r ≠ 0) : Γ₀ he :=
let val := (multiset.count v.val.as_ideal (unique_factorization_monoid.normalized_factors (ideal.span{r} : ideal R)) : ℤ)  in ⟨ e^val, set.mem_union_left _ ⟨val, set.mem_univ val, rfl⟩⟩ 


-- TODO: show well-defined

--#print adic_valuation.def

def R.adic_valuation (v : maximal_spectrum R) {e : ℚ} (he : 1 < e) : valuation R (Γ₀ he) := { 
  to_fun    := λ x, dite  (x = 0) (λ (h : x = 0), 0) (λ (h : ¬x = 0), ring.adic_valuation.def R v he x h), --TODO : valuation v
  map_zero' := by { rw dif_pos, refl, },
  map_one'  := by { rw dif_neg, rw ring.adic_valuation.def,
  { ext, simp only [subtype.coe_mk],
    suffices h : multiset.count v.val.as_ideal (unique_factorization_monoid.normalized_factors (ideal.span {1})) = 0,
    { rw h, refl },
    rw [multiset.count_eq_zero, ideal.span_singleton_one, ← ideal.one_eq_top,
    unique_factorization_monoid.normalized_factors_one],
    exact multiset.not_mem_zero _ },
  { exact one_ne_zero},},
  map_mul'  := λ x y, begin
    by_cases hx : x = 0,
    { rw [dif_pos hx, dif_pos, zero_mul],
      { rw [hx, zero_mul] }},
    { by_cases hy : y = 0,
      { rw [dif_pos hy, dif_pos, mul_zero],
      { rw [hy, mul_zero] }},
      { rw dif_neg hx, rw dif_neg hy, rw dif_neg (mul_ne_zero hx hy),
        rw [ring.adic_valuation.def, ring.adic_valuation.def, ring.adic_valuation.def],
        simp only [subtype.val_eq_coe, gpow_coe_nat],
        ext,
        simp only [subtype.coe_mk],
        have he' : e ≠ 0 := sorry,
        

       sorry } }
  end,
  map_add'  := sorry }

def adic_valuation (v : maximal_spectrum R) {e : ℚ} (he : 1 < e) : valuation K (Γ₀ he) := { 
  to_fun    := λ x, dite  (x = 0) (λ (h : x = 0), 0) ((λ (h : ¬x = 0), adic_valuation.def R K v he x h)), --TODO : valuation v
  map_zero' := by { rw dif_pos, refl, },
  map_one'  := by { rw dif_neg, rw adic_valuation.def,
  { simp only [is_fraction_ring.mk'_eq_div, subtype.val_eq_coe],
  ext, simp only [subtype.coe_mk],
  sorry },
  { exact one_ne_zero},},
  map_mul'  := λ x y, begin
    sorry,
  end,
  map_add'  := sorry }

variables (v : maximal_spectrum R) (e : ℚ) (he : 1 < e)


instance adic_valued : valued K := 
{ Γ₀ := (Γ₀ he),
  grp := locgwz he,
  v := sorry}



