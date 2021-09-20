import adeles_K

noncomputable theory

--set_option profiler true

open nat 
/-! Finite ideles of ℚ -/
def I_Q_f := units A_Q_f

instance : topological_space I_Q_f := units.topological_space
instance : group I_Q_f := units.group
instance : topological_group I_Q_f := units.topological_group

private def map_id: units ℚ → A_Q_f := λ r, localization.mk (λ p, (r.val.num : ℤ_[p])) 
⟨ inj_pnat r.val.denom, by use [r.val.denom, 
  set.mem_compl_singleton_iff.mpr (int.coe_nat_ne_zero.mpr r.val.denom_ne_zero)]⟩

private def map_inv : units ℚ → A_Q_f := λ r, localization.mk (λ p, (r.inv.num : ℤ_[p]))
⟨ inj_pnat r.inv.denom, by use [r.inv.denom, 
  set.mem_compl_singleton_iff.mpr (int.coe_nat_ne_zero.mpr r.inv.denom_ne_zero)]⟩

private lemma hnum (r : units ℚ) (h : 0 < (r : ℚ).num) : 
(λ (p : primes), (((r : ℚ).num : ℤ_[p]) * (((r : ℚ))⁻¹.num))) = 
  (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) :=
begin
  ext p,
  rw [rat.inv_def', padic_int.coe_mul, padic_int.coe_mul, mul_eq_mul_left_iff, padic_int.coe_coe, 
    padic_int.coe_coe_int],
  left,
  repeat {rw ← int.cast_coe_nat (r : ℚ).denom},
  rw int.cast_inj,
  apply rat.num_div_eq_of_coprime,
  { exact h },
  rw coprime_comm,
  exact rat.cop ↑r,
end

private lemma hnum' (r : units ℚ) (h : (r : ℚ).num < 0 ) : 
(λ (p : primes), (((r : ℚ).num : ℤ_[p]) * (((r : ℚ))⁻¹.num))) =
  (λ (p : primes), -(((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) :=
begin
  ext p,
  apply eq.symm,
  rw [rat.inv_def', ← int.cast_mul, padic_int.cast_inj, ← int.cast_coe_nat _, ← int.cast_mul,
    ← int.cast_neg, padic_int.coe_int_eq _ _, int.neg_mul_eq_mul_neg (r : ℚ).num ((r : ℚ).denom)],
  suffices h1: -↑((r : ℚ).denom) = ((((r : ℚ).denom) / (r : ℚ).num) : ℚ).num ,
  { rw h1 },
  rw [← int.cast_coe_nat _, neg_eq_iff_neg_eq, ← rat.num_neg_eq_neg_num _, ← rat.mk_eq_div _ _,
    rat.neg_def, rat.mk_eq_div _ _, int.cast_neg, neg_div, ← div_neg_eq_neg_div, ← int.cast_neg],
  apply rat.num_div_eq_of_coprime,
  { rw neg_pos, exact h },
  rw [coprime_comm, (r : ℚ).num.nat_abs_neg],
  exact rat.cop ↑r,
end

--set_option profiler true
private lemma hdenom (r : units ℚ) (h : 0 < (r : ℚ).num) : 
(λ (p : primes), (((r : ℚ).denom : ℤ_[p]) * (((r : ℚ))⁻¹.denom))) =
  (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom)))  :=
begin
  ext p,
  rw [rat.inv_def', mul_comm, padic_int.coe_mul, padic_int.coe_mul, mul_eq_mul_right_iff,
    padic_int.coe_coe, padic_int.coe_coe_int],
  left,
  rw [← int.cast_coe_nat (((r : ℚ).denom) / ((r : ℚ).num) : ℚ).denom, int.cast_inj,
    ← int.cast_coe_nat (r : ℚ).denom],
  apply rat.denom_div_eq_of_coprime,
  { exact h },
  rw coprime_comm,
  exact rat.cop ↑r,
end

private lemma hdenom' (r : units ℚ) (h : (r : ℚ).num < 0 ) :
(λ (p : primes), (((r : ℚ).denom : ℤ_[p]) * (((r : ℚ))⁻¹.denom))) =
  (λ (p : primes), -(((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) :=
begin
  ext p,
  apply eq.symm,
  rw [rat.inv_def', mul_comm, ← int.cast_coe_nat _, ← int.cast_mul, padic_int.cast_inj,
    ← int.cast_coe_nat _, ← int.cast_mul, ← int.cast_neg, int.cast_inj,
    int.neg_mul_eq_neg_mul ((r : ℚ).denom) (r : ℚ).num, int.neg_mul_comm],
  suffices h1 : -(r : ℚ).num = ((((r : ℚ).denom) / (r : ℚ).num) : ℚ).denom,
  { rw h1 },
  rw [← int.cast_coe_nat, ← rat.mk_eq_div _ _, ← rat.denom_neg_eq_denom, rat.neg_def,
    rat.mk_eq_div _ _, int.cast_neg, neg_div, ← div_neg_eq_neg_div, ← int.cast_neg],
  apply eq.symm,
  apply rat.denom_div_eq_of_coprime,
  { rw neg_pos, exact h },
  rw [coprime_comm, (r : ℚ).num.nat_abs_neg],
  exact rat.cop ↑r,
end

--set_option profiler true
private lemma right_inv (r : units ℚ) : (map_id r) * (map_inv r) = 1 := 
begin
  rw [map_id, map_inv],
  unfold inj_pnat,
  dsimp only,
  rw [localization.mk_eq_mk', ← is_localization.mk'_mul (localization M) _ _ _ _, pi.mul_def,
    ← @is_localization.mk'_self' R _ M (localization M) _ _ _ 1],
  apply is_localization.mk'_eq_iff_eq.mpr,
  rw [submonoid.coe_one, mul_one, one_mul, submonoid.coe_mul,set_like.coe_mk, set_like.coe_mk,
    units.val_eq_coe, units.inv_eq_coe_inv, units.coe_inv', pi.mul_def],
  simp only [int.cast_coe_nat],
  by_cases h_sgn : 0 < (r : ℚ).num, 
  { have hnum : (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * (((r : ℚ))⁻¹.num))) =
      (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) := hnum r h_sgn,
    have hdenom : (λ (p : primes), (((r : ℚ).denom : ℤ_[p]) * (((r : ℚ))⁻¹.denom))) =
      (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) := hdenom r h_sgn,
    rw [hnum, hdenom]
    },
    rw [not_lt, le_iff_eq_or_lt] at h_sgn,
    cases h_sgn,
    { have hzero : (r : ℚ) = 0 := rat.zero_of_num_zero h_sgn,
      have hne_zero : (r : ℚ) ≠ 0 := by { apply units.ne_zero,
      },
      exfalso,
      exact hne_zero hzero},
    { have hnum : (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * (((r : ℚ))⁻¹.num))) =
        (λ (p : primes), -(((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) := hnum' r h_sgn,
      have hdenom : (λ (p : primes), (((r : ℚ).denom : ℤ_[p]) * (((r : ℚ))⁻¹.denom))) = 
        (λ (p : primes), -(((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) := hdenom' r h_sgn,
      rw [hnum, hdenom]}
end

private lemma left_inv (r : units ℚ) : (map_inv r) * (map_id r) = 1 := 
by {rw mul_comm, exact right_inv r}

def map_units_Q_I_Q_f : units ℚ → I_Q_f := λ r, ⟨map_id r, map_inv r, right_inv r, left_inv r⟩

lemma map_id_mul : ∀ r s : units ℚ, map_id (r * s) = map_id r * map_id s := begin
  intros r s,
  rw map_id,
  unfold inj_pnat,
  rw [localization.mk_eq_mk', ← is_localization.mk'_mul (localization M) _ _ _ _],
  apply is_localization.mk'_eq_iff_eq.mpr,
  rw algebra_map,
  repeat {rw pi.mul_def},
  apply congr_arg,
  ext p,
  rw submonoid.coe_mul,
  repeat {rw [set_like.coe_mk]},
  repeat {rw units.val_eq_coe _},
  rw pi.mul_apply,
  dsimp only,
  repeat {rw int.cast_coe_nat},
  repeat {rw padic_int.coe_mul},
  repeat {rw [padic_int.coe_coe_int, padic_int.coe_coe]},
  --rw padic_int.cast_inj,
  exact map_mul r s p,
end

lemma map_units_Q_I_Q_f_mul (r s : units ℚ) :  
  map_units_Q_I_Q_f (r * s) = map_units_Q_I_Q_f r * map_units_Q_I_Q_f s := 
begin
  rw [map_units_Q_I_Q_f, ← units.eq_iff, units.coe_mul],
  repeat {rw units.coe_mk},
  exact map_id_mul r s,
end

def hom_units_Q_I_Q_f : monoid_hom (units ℚ) I_Q_f := 
monoid_hom.mk' map_units_Q_I_Q_f map_units_Q_I_Q_f_mul

variables (K : Type*) [field K] [char_zero K] [finite_dimensional ℚ K]

/-! Ideles of ℚ -/
def I_Q := units A_Q

instance : group I_Q := units.group
instance : topological_space I_Q := units.topological_space
instance : topological_group I_Q := units.topological_group

private def map_id': units ℚ → A_Q := λ r, (map_id r, r.val)

private def map_inv' : units ℚ → A_Q := λ r, (map_inv r, r.inv)

private lemma right_inv' (r : units ℚ) : (map_id' r) * (map_inv' r) = 1 := 
begin
  rw [map_id', map_inv', prod.mk_mul_mk, prod.eq_iff_fst_eq_snd_eq],
  dsimp only,
  split,
  { exact right_inv r},
  rw [units.val_eq_coe, units.inv_eq_coe_inv, units.coe_inv', @rat.cast_inv ℝ _ _ (r : ℚ)],
  exact mul_inv_cancel ((@rat.cast_ne_zero ℝ _ _ ↑r).mpr (units.ne_zero r)),
end

private lemma left_inv' (r : units ℚ) : (map_inv' r) * (map_id' r) = 1 := 
by {rw mul_comm, exact right_inv' r}

def map_units_Q_I_Q : units ℚ → I_Q := λ r, ⟨map_id' r, map_inv' r, right_inv' r, left_inv' r⟩

lemma map_units_Q_I_Q_mul (r s : units ℚ) : 
  map_units_Q_I_Q (r * s) = map_units_Q_I_Q r * map_units_Q_I_Q s := 
begin
  rw [map_units_Q_I_Q, ← units.eq_iff, units.coe_mul, units.coe_mk, units.coe_mk, units.coe_mk,
    map_id', prod.eq_iff_fst_eq_snd_eq],
  split,
  { rw prod.mk_mul_mk, exact map_id_mul r s},
  dsimp only,
  rw [prod.mk_mul_mk, units.val_eq_coe r, units.val_eq_coe s,units.val_eq_coe (r*s),units.coe_mul,
    rat.cast_mul],
end

def hom_units_Q_I_Q : monoid_hom (units ℚ) I_Q := 
monoid_hom.mk' map_units_Q_I_Q  map_units_Q_I_Q_mul

--set_option profiler true
lemma inj_hom_units_Q_I_Q : function.injective hom_units_Q_I_Q := 
begin
  rw monoid_hom.injective_iff,
  intros r hr,
  have hf : hom_units_Q_I_Q r = map_units_Q_I_Q r := rfl,
  rw [hf, map_units_Q_I_Q, ← units.eq_iff, units.coe_mk, units.coe_one, map_id',
    prod.eq_iff_fst_eq_snd_eq] at hr,
  rcases hr with ⟨ -, hr⟩,
  dsimp only at hr,
  rw [units.val_eq_coe, prod.snd_one, ← rat.cast_one, rat.cast_inj] at hr,
  rwa ← units.coe_eq_one,
end

/-! Finite ideles of K -/
def finite_ideles_map : Type* := units (finite_adeles_map K)

instance : group (finite_ideles_map K) := units.group

/-! Ideles of K -/
def ideles_map : Type* := units (adeles_map K)

instance : group (ideles_map K) := units.group