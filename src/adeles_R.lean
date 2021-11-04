import valuation
import ring_theory.valuation.integers

noncomputable theory
--open_locale classical
open function set

variables {R : Type} {K : Type} [integral_domain R] [is_dedekind_domain R] [field K] [algebra R K]
  [is_fraction_ring R K] (v : maximal_spectrum R)

instance v_valued_K (v : maximal_spectrum R) : valued K := 
{ Γ₀  := with_zero (multiplicative ℤ),
  grp := infer_instance,
  v   := adic_valuation v }

instance ts' : topological_space K := @valued.topological_space K _ (v_valued_K v)
instance tdr' : @topological_division_ring K _ (ts' v) := 
@valued.topological_division_ring K _ (v_valued_K v)
instance tr' : @topological_ring K  (ts' v) _ := infer_instance
instance tg' : @topological_add_group K (ts' v) _ := infer_instance
instance us' : uniform_space K := @topological_add_group.to_uniform_space K _ (ts' v) (tg' v)
instance ug' : @uniform_add_group K (us' v) _ := 
@topological_add_group_is_uniform K _ (ts' v) (tg' v)
instance cf' : @completable_top_field K _ (us' v) := @valued.completable K _ (v_valued_K v)

instance ss : @separated_space K (us' v) := @valued_ring.separated K _ (v_valued_K v)

variables (K)
def K_v := @uniform_space.completion K (us' v)
instance : field (K_v K v) := @field_completion K _ (us' v) (tdr' v) _ (ug' v) (tr' v)
instance : division_ring (K_v K v) := infer_instance
instance : comm_ring (K_v K v) := infer_instance

variables {K}
instance valued_K_v : valued (K_v K v) := 
{ Γ₀  := with_zero (multiplicative ℤ),
  grp := infer_instance,
  v   := @valued.extension_valuation K _ (v_valued_K v) }

instance ts : topological_space (K_v K v) := @valued.topological_space (K_v K v) _ (valued_K_v v)
instance tdr : @topological_division_ring (K_v K v) _ (ts v) := 
@valued.topological_division_ring (K_v K v) _ (valued_K_v v)
instance tr : @topological_ring (K_v K v) (ts v) _ := (tdr v).to_topological_ring
instance tg : @topological_add_group (K_v K v) (ts v) _ := 
@topological_ring.to_topological_add_group (K_v K v) _ (ts v) (tr v)
instance us : uniform_space (K_v K v) := 
@topological_add_group.to_uniform_space (K_v K v) _ (ts v) (tg v)
instance ug : @uniform_add_group (K_v K v) (us v) _ := 
@topological_add_group_is_uniform (K_v K v) _ (ts v) (tg v)

instance : has_lift_t K (@uniform_space.completion K (us' v)) := infer_instance
instance R_v.has_lift_t : has_lift_t K (K_v K v) := uniform_space.completion.has_lift_t v

variables (K)
def R_v : subring (K_v K v) := 
@valuation.integer (K_v K v) (with_zero (multiplicative ℤ)) _ _ (valued_K_v v).v 

-- Finite adele ring of R
variables (R)
def R_hat := (Π (v : maximal_spectrum R), (R_v K v))
instance : comm_ring (R_hat R K) := pi.comm_ring

lemma valuation.is_integer {R : Type*} {Γ₀ : Type*} [ring R]
  [linear_ordered_comm_group_with_zero Γ₀] (v : valuation R Γ₀) (x : R):
x ∈ valuation.integer v ↔ v(x) ≤ 1 := 
begin
   rw ← subring.mem_carrier,
   refl,
end

lemma K_v.is_integer (x : K_v K v) : x ∈ R_v K v ↔ valued.v x ≤ 1 := 
by { rw R_v, exact valuation.is_integer _ _,}

def inj_R_v' : R → (K_v K v) := λ r, (coe : K → (K_v K v)) (algebra_map R K r)
def inj_R_v : R → (R_v K v) := λ r, ⟨(coe : K → (K_v K v)) (algebra_map R K r), begin 
  --rw [R_v, valuation.is_integer],
  --simp only [valued.v, valued.extension_valuation],
  change @valued.extension K _ (v_valued_K v) (algebra_map R K r) ≤ 1, --need a coe_to_fun?
  rw @valued.extension_extends K _ (v_valued_K v) (algebra_map R K r),
  exact adic_valuation.le_one v _,
end⟩
def inj_R : R → (R_hat R K) := λ r v, inj_R_v R K v r

lemma inj_R_v.injective : function.injective (inj_R_v R K v) :=
begin
  intros x y hxy,
  have h_inj : function.injective (coe : K → (K_v K v)) :=
    @uniform_embedding.inj K _ (us' v) _ coe 
      (@uniform_space.completion.uniform_embedding_coe K (us' v) (ss v)),
  rw [inj_R_v, subtype.mk_eq_mk] at hxy,
  exact (is_fraction_ring.injective R K) ((h_inj) hxy),
end

lemma inj_R_v.map_one : inj_R_v R K v 1 = 1 :=  by { rw inj_R_v, simp_rw ring_hom.map_one, refl, }
lemma inj_R.map_one : inj_R R K 1 = 1 := 
by { rw inj_R, ext v, simp_rw inj_R_v.map_one R K v, refl, }

lemma inj_R_v.map_mul (x y : R): inj_R_v R K v (x*y) = (inj_R_v R K v x) * (inj_R_v R K v y) :=
begin
  rw inj_R_v,
  simp_rw ring_hom.map_mul,
  ext,
  rw [subtype.coe_mk, subring.coe_mul, subtype.coe_mk, subtype.coe_mk,
    uniform_space.completion.coe_mul],
end

lemma inj_R.map_mul (x y : R): inj_R R K (x*y) = (inj_R R K x) * (inj_R R K y) :=
by { rw inj_R, ext v, apply congr_arg _ (inj_R_v.map_mul R K v x y), }

def diag_R : submonoid (R_hat R K) := 
{ carrier  := (inj_R R K) '' set.compl {0},
  one_mem' :=  ⟨1, set.mem_compl_singleton_iff.mpr one_ne_zero, inj_R.map_one R K⟩,
  mul_mem' := 
  begin
    rintros a b ⟨za, hza, rfl⟩ ⟨zb, hzb, rfl⟩,
    exact ⟨za*zb, mul_ne_zero hza hzb, inj_R.map_mul R K za zb⟩,
  end }

def finite_adele_ring := localization (diag_R R K)
instance : comm_ring (finite_adele_ring R K) := localization.comm_ring
instance : algebra (R_hat R K) (finite_adele_ring R K) := localization.algebra
instance : is_localization (diag_R R K) (finite_adele_ring R K):= localization.is_localization

lemma preimage_diag_R (x : diag_R R K) : ∃ r : R, r ≠ 0 ∧ inj_R R K r = (x : R_hat R K) := 
x.property

def finite_adele_ring' :=
{ x : (Π v : (maximal_spectrum R), K_v K v) //
  ∀ᶠ (v : maximal_spectrum R) in filter.cofinite, (x v ∈ R_v K v) }

lemma restr_add (x y : finite_adele_ring' R K) : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  ((x.val + y.val) v ∈ R_v K v) := 
begin
  cases x with x hx,
  cases y with y hy,
  rw filter.eventually_cofinite at hx hy ⊢,
  have h_subset : {v : maximal_spectrum R | ¬ (x + y) v ∈  (R_v K v)} ⊆
    {v : maximal_spectrum R | ¬ x v ∈ (R_v K v)} ∪ {v : maximal_spectrum R | ¬ y v ∈ (R_v K v)},
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq],
    rw mem_set_of_eq at hv,
    by_contradiction h,
    push_neg at h,
    apply hv,
    rw [K_v.is_integer, K_v.is_integer, ← max_le_iff] at h,
    rw [K_v.is_integer, pi.add_apply],
    exact le_trans (valued.v.map_add' (x v) (y v)) h },
  exact finite.subset (finite.union hx hy) h_subset,
end

def add' (x y : finite_adele_ring' R K) : finite_adele_ring' R K := 
⟨x.val + y.val, restr_add R K x y⟩

lemma restr_zero : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  ((0 : K_v K v) ∈ R_v K v) := 
begin
  rw filter.eventually_cofinite,
  have h_empty : {v : maximal_spectrum R | ¬ ((0 : K_v K v) ∈ R_v K v)} = ∅,
  { ext v, rw mem_empty_eq, split; intro hv,
    { rw mem_set_of_eq at hv, apply hv, rw K_v.is_integer, 
      have h_zero : valued.v (0 : K_v K v) = 0 := valued.v.map_zero',
      rw h_zero, exact zero_le_one' },
    { exfalso, exact hv }},
  rw h_empty,
  exact finite_empty,
end

lemma restr_neg (x : finite_adele_ring' R K)  : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  (-x.val v ∈ R_v K v) := 
begin
  cases x with x hx,
  have h : ∀ (v : maximal_spectrum R), (-x v ∈ R_v K v) ↔ (x v ∈ R_v K v),
  { intro v,
    rw [K_v.is_integer, K_v.is_integer, valuation.map_neg], },
  simp_rw h,
  exact hx,
end

def neg' (x : finite_adele_ring' R K) : finite_adele_ring' R K := ⟨-x.val, restr_neg R K x⟩

lemma restr_mul (x y : finite_adele_ring' R K) : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  ((x.val * y.val) v ∈ R_v K v) := 
begin
  cases x with x hx,
  cases y with y hy,
  rw filter.eventually_cofinite at hx hy ⊢,
  have h_subset : {v : maximal_spectrum R | ¬ (x * y) v ∈  (R_v K v)} ⊆
    {v : maximal_spectrum R | ¬ x v ∈ (R_v K v)} ∪ {v : maximal_spectrum R | ¬ y v ∈ (R_v K v)},
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq],
    rw mem_set_of_eq at hv,
    by_contradiction h,
    push_neg at h,
    apply hv,
    rw [K_v.is_integer, K_v.is_integer] at h,
    have h_mul : valued.v (x v * y v) = (valued.v (x v)) * (valued.v (y v)) 
    := (valued.v).map_mul' (x v) (y v),
    rw [K_v.is_integer, pi.mul_apply, h_mul, ← mul_one (1 : with_zero (multiplicative ℤ ))],
    exact with_zero.mul_le_one h.left  h.right, },
  exact finite.subset (finite.union hx hy) h_subset,
end

def mul' (x y : finite_adele_ring' R K) : finite_adele_ring' R K := 
⟨x.val * y.val, restr_mul R K x y⟩

lemma restr_one : ∀ᶠ (v : maximal_spectrum R) in filter.cofinite,
  ((1 : K_v K v) ∈ R_v K v) := 
begin
  rw filter.eventually_cofinite,
  have h_empty : {v : maximal_spectrum R | ¬ ((1 : K_v K v) ∈ R_v K v)} = ∅,
  { ext v, rw mem_empty_eq, split; intro hv,
    { rw mem_set_of_eq at hv, apply hv, rw K_v.is_integer, 
      exact le_of_eq valued.v.map_one' },
    { exfalso, exact hv }},
  rw h_empty,
  exact finite_empty,
end

instance : add_comm_group (finite_adele_ring' R K) := 
{ add          := add' R K,
  add_assoc    := λ ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩,
  by { dsimp only [add'], rw [subtype.mk_eq_mk], exact add_assoc _ _ _, },
  zero         := ⟨0, restr_zero R K⟩,
  zero_add     := λ x, by { simp_rw [add', zero_add, subtype.val_eq_coe, subtype.coe_eta] },
  add_zero     := λ x, by { simp_rw [add', add_zero, subtype.val_eq_coe, subtype.coe_eta] },
  neg          := λ x, ⟨-x.val, restr_neg R K x⟩,
  add_left_neg := λ x, by { unfold_projs,  dsimp only [add'], ext, 
    rw [subtype.coe_mk, subtype.coe_mk, pi.add_apply, add_left_neg], refl, },
  add_comm     := λ x y, by { unfold_projs,  dsimp only [add'], ext, 
    rw [subtype.coe_mk, subtype.coe_mk, pi.add_apply, pi.add_apply, add_comm], }}

instance : comm_ring (finite_adele_ring' R K) := 
{ mul           := mul' R K,
  mul_assoc     := λ x y z,
  by { sorry },
  one           := ⟨1, restr_one R K⟩,
  one_mul       := λ x, by { simp_rw [mul', one_mul, subtype.val_eq_coe, subtype.coe_eta] },
  mul_one       := λ x, by { simp_rw [mul', mul_one, subtype.val_eq_coe, subtype.coe_eta] },
  left_distrib  := λ x y z, by { unfold_projs, sorry },
  right_distrib := λ x y z, by { unfold_projs, sorry },
  mul_comm      := λ x y, by { sorry },
  ..(finite_adele_ring'.add_comm_group R K)}

def finite_adele.hom : (finite_adele_ring R K) →+* (finite_adele_ring' R K) := 
{ to_fun := sorry,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }
  
def finite_adele.inv : (finite_adele_ring' R K) →+* (finite_adele_ring R K) := 
{ to_fun := sorry,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

lemma finite_adele.hom_inv_id : 
  (finite_adele.inv R K).comp (finite_adele.hom R K) = ring_hom.id (finite_adele_ring R K) := sorry

lemma finite_adele.inv_hom_id :
  (finite_adele.hom R K).comp (finite_adele.inv R K) = ring_hom.id (finite_adele_ring' R K) := sorry

def finite_adele.eq_defs : ring_equiv (finite_adele_ring R K) (finite_adele_ring' R K) :=
  ring_equiv.of_hom_inv (finite_adele.hom R K) (finite_adele.inv R K)
    (finite_adele.hom_inv_id R K) (finite_adele.inv_hom_id R K)
