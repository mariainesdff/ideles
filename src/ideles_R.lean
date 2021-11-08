import adeles_R

noncomputable theory

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
