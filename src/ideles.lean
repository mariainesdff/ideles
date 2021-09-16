import adeles_K

noncomputable theory

open nat 
/-! Finite ideles of ℚ -/
def I_Q_f := units A_Q_f

instance : topological_space I_Q_f := units.topological_space
instance : group I_Q_f := units.group
instance : topological_group I_Q_f := units.topological_group

/-! Ideles of ℚ -/
def I_Q := units A_Q

private def map_id: units ℚ → A_Q_f := λ r, localization.mk (λ p, (r.val.num : ℤ_[p])) ⟨ inj_pnat r.val.denom, by 
    use [r.val.denom, set.mem_compl_singleton_iff.mpr (int.coe_nat_ne_zero.mpr r.val.denom_ne_zero)]⟩

private def map_inv : units ℚ → A_Q_f := λ r, localization.mk (λ p, (r.inv.num : ℤ_[p])) ⟨ inj_pnat r.inv.denom, by 
    use [r.inv.denom, set.mem_compl_singleton_iff.mpr (int.coe_nat_ne_zero.mpr r.inv.denom_ne_zero)]⟩

private lemma hnum (r : units ℚ) (h : 0 < (r : ℚ).num) : (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * (((r : ℚ))⁻¹.num))) =  (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) :=
begin
  ext p,
  rw rat.inv_def',
  simp,
  left,
  norm_cast,
  rw rat.mk_eq_div _ _,
  apply rat.num_div_eq_of_coprime,
  { exact h },
  rw coprime_comm,
  exact rat.cop ↑r,
end

private lemma hnum' (r : units ℚ) (h : (r : ℚ).num < 0 ) : (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * (((r : ℚ))⁻¹.num))) =  (λ (p : primes), -(((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) :=
begin
  ext p,
  rw rat.inv_def',
  simp,
  norm_cast,
  rw int.neg_mul_eq_mul_neg (r : ℚ).num ((r : ℚ).denom),
  suffices h1: (rat.mk ↑((r : ℚ).denom) (r : ℚ).num).num = -↑((r : ℚ).denom),
  { rw h1 },
  rw [eq_neg_iff_eq_neg,
  ← rat.num_neg_eq_neg_num _, rat.neg_def, rat.mk_eq_div _ _],
  apply eq.symm,
  rw [int.cast_neg, neg_div, ← div_neg_eq_neg_div, ← int.cast_neg],
  apply rat.num_div_eq_of_coprime,
  { rw neg_pos, exact h },
  rw [coprime_comm, (r : ℚ).num.nat_abs_neg],
  exact rat.cop ↑r,
end

private lemma hdenom (r : units ℚ) (h : 0 < (r : ℚ).num) : (λ (p : primes), (((r : ℚ).denom : ℤ_[p]) * (((r : ℚ))⁻¹.denom))) = (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom)))  :=
begin
  ext p,
  rw [rat.inv_def', mul_comm],
  simp,
  left,
  norm_cast,
  rw rat.mk_eq_div _ _,
  apply rat.denom_div_eq_of_coprime,
  { exact h },
  rw coprime_comm,
  exact rat.cop ↑r,
end

private lemma hdenom' (r : units ℚ) (h : (r : ℚ).num < 0 ) : (λ (p : primes), (((r : ℚ).denom : ℤ_[p]) * (((r : ℚ))⁻¹.denom))) =  (λ (p : primes), -(((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) :=
begin
  ext p,
  rw [rat.inv_def', mul_comm],
  simp,
  norm_cast,
  rw int.neg_mul_eq_neg_mul (r : ℚ).num ((r : ℚ).denom),
  rw int.coe_nat_mul (rat.mk ↑((r : ℚ).denom) (r : ℚ).num).denom (r : ℚ).denom,
  suffices h1: ((rat.mk ↑((r : ℚ).denom) (r : ℚ).num).denom : ℤ) = -((r : ℚ).num : ℤ),
  { rw h1 },
  rw [← rat.denom_neg_eq_denom, rat.neg_def, rat.mk_eq_div _ _],
  rw [int.cast_neg, neg_div, ← div_neg_eq_neg_div, ← int.cast_neg],
  apply rat.denom_div_eq_of_coprime,
  { rw neg_pos, exact h },
  rw [coprime_comm, (r : ℚ).num.nat_abs_neg],
  exact rat.cop ↑r,
end

private lemma right_inv (r : units ℚ) : (map_id r) * (map_inv r) = 1 := 
begin
  rw [map_id, map_inv],
  unfold inj_pnat,
  dsimp only,
  rw [localization.mk_eq_mk', ← is_localization.mk'_mul (localization M) _ _ _ _],
  rw [pi.mul_def, ← @is_localization.mk'_self' R _ M (localization M) _ _ _ 1],
  apply is_localization.mk'_eq_iff_eq.mpr,
  simp,
  rw [algebra_map, ← ring_hom.map_mul, pi.mul_def],

  by_cases h_sgn : 0 < (r : ℚ).num, 
  { have hnum : (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * (((r : ℚ))⁻¹.num))) = (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) := hnum r h_sgn,
    have hdenom : (λ (p : primes), (((r : ℚ).denom : ℤ_[p]) * (((r : ℚ))⁻¹.denom))) = (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) := hdenom r h_sgn,
    rw [hnum, hdenom]},

    rw [not_lt, le_iff_eq_or_lt] at h_sgn,
    cases h_sgn,
    { have hzero : (r : ℚ) = 0 := rat.zero_of_num_zero h_sgn,
      have hne_zero : (r : ℚ) ≠ 0 := by { apply units.ne_zero,
      },
      exfalso,
      exact hne_zero hzero,
    },
    { have hnum : (λ (p : primes), (((r : ℚ).num : ℤ_[p]) * (((r : ℚ))⁻¹.num))) = (λ (p : primes), -(((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) := hnum' r h_sgn,
      have hdenom : (λ (p : primes), (((r : ℚ).denom : ℤ_[p]) * (((r : ℚ))⁻¹.denom))) = (λ (p : primes), -(((r : ℚ).num : ℤ_[p]) * ((r : ℚ).denom))) := hdenom' r h_sgn,
      rw [hnum, hdenom]}
end

private lemma left_inv (r : units ℚ) : (map_inv r) * (map_id r) = 1 := by {rw mul_comm, exact right_inv r}

def map_units_Q_I_Q : units ℚ → I_Q_f := λ r, ⟨map_id r, map_inv r, right_inv r, left_inv r⟩

instance : topological_space I_Q := units.topological_space
instance : group I_Q := units.group
instance : topological_group I_Q := units.topological_group

variables (K : Type*) [field K] [char_zero K] [finite_dimensional ℚ K]

/-! Finite ideles of K -/
def finite_ideles_map : Type* := units (finite_adeles_map K)

instance : group (finite_ideles_map K) := units.group

/-! Ideles of K -/
def ideles_map : Type* := units (adeles_map K)

instance : group (ideles_map K) := units.group