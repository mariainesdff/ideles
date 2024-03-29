/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import fractional_ideal
import ring_theory.valuation.integers
import topology.algebra.localization
import topology.algebra.valued_field
import ring_theory.dedekind_domain.adic_valuation

/-!
# The finite adèle ring of a Dedekind domain
Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`,
we define the completion of `K` with respect to its `v`-adic valuation, denoted `adic_completion`,and its ring
of integers, denoted `adic_completion_integers`. 

We define the ring of finite adèles of a Dedekind domain. We provide two equivalent definitions of
this ring (TODO: show that they are equivalent).

We show that there is an injective ring homomorphism from the field of fractions of a Dedekind
domain of Krull dimension 1 to its finite adèle ring.

## Main definitions
- `adic_completion`   : the completion of `K` with respect to its `v`-adic valuation.
- `adic_completion_integers`   : the ring of integers of `adic_completion`. 
- `R_hat` : product of `adic_completion_integers`, where `v` runs over all maximal ideals of `R`. 
- `K_hat` : the product of `adic_completion`, where `v` runs over all maximal ideals of `R`. 
- `finite_adele_ring'` : The finite adèle ring of `R`, defined as the restricted product `Π'_v adic_completion`.
- `inj_K` : The diagonal inclusion of `K` in `finite_adele_ring' R K`.
- `finite_adele_ring` : The finite adèle ring of `R`, defined as the localization of `R_hat` at the
  submonoid `R∖{0}`.
- `finite_adele.hom` : A ring homomorphism from `finite_adele_ring R K` to `finite_adele_ring' R K`.

## Main results
- `inj_K.ring_hom` : `inj_K` is a ring homomorphism.
- `inj_K.injective` : `inj_K` is injective for every Dedekind domain of Krull dimension 1.

## Implementation notes
We are only interested on Dedekind domains of Krull dimension 1 (i.e., not fields). If `R` is a 
field, its finite adèle ring is just defined to be empty.

## References
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite adèle ring, dedekind domain, completions
-/

noncomputable theory
open_locale classical
open function set is_dedekind_domain
/- Auxiliary lemmas. -/
private lemma subset.three_union {α : Type*} (f g h : α → Prop):
  {a : α| ¬ (f a ∧ g a ∧ h a)} ⊆ {a : α| ¬ f a} ∪ {a : α| ¬ g a} ∪ {a : α| ¬ h a} := 
begin
  intros a ha,
  rw mem_set_of_eq at ha,
  push_neg at ha,
  by_cases hf : f a,
  { by_cases hg : g a,
    { exact mem_union_right _ (ha hf hg)},
    { exact mem_union_left _ (mem_union_right _ hg), }},
  { exact mem_union_left _ (mem_union_left _ hf),},
end

/-- Auxiliary definition to force a definition to be noncomputable. This is used to avoid timeouts
or memory errors when Lean cannot decide whether a certain definition is computable.
Author: Gabriel Ebner. -/
noncomputable def force_noncomputable {α : Sort*} (a : α) : α :=
  function.const _ a (classical.choice ⟨a⟩)

@[simp]
lemma force_noncomputable_def {α} (a : α) : force_noncomputable a = a := rfl

/-! ### Completions with respect to adic valuations
Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`, we define
the completion of `K` with respect to its `v`-adic valuation, denoted `adic_completion`,and its ring
of integers, denoted `adic_completion_integers`. 

We define `R_hat` (resp. `K_hat`) to be the product of `adic_completion_integers` (resp.
`adic_completion`), where `v` runs over all maximal ideals of `R`. -/

variables {R : Type} {K : Type} [comm_ring R] [is_domain R] [is_dedekind_domain R] [field K]
  [algebra R K] [is_fraction_ring R K] (v : height_one_spectrum R)

variables (R K)

/-- The product of all `adic_completion_integers`, where `v` runs over the maximal ideals of `R`. -/
def R_hat := (Π (v : height_one_spectrum R), v.adic_completion_integers K)
instance : comm_ring (R_hat R K) := pi.comm_ring
instance : topological_space (R_hat R K) := Pi.topological_space

/-- The product of all `adic_completion`, where `v` runs over the maximal ideals of `R`. -/
def K_hat := (Π (v : height_one_spectrum R), v.adic_completion K )

instance : comm_ring (K_hat R K) := pi.comm_ring
instance : ring (K_hat R K) := infer_instance
instance : topological_space (K_hat R K) := Pi.topological_space
instance : topological_ring (K_hat R K) := 
(infer_instance : topological_ring (Π (v : height_one_spectrum R), v.adic_completion K))

lemma adic_completion.is_integer (x : v.adic_completion K) :
  x ∈ v.adic_completion_integers K ↔ (valued.v x : with_zero (multiplicative ℤ)) ≤ 1 := by refl

/-- The natural inclusion of `R` in `adic_completion`. -/
def inj_adic_completion_integers' : R → (v.adic_completion K) :=
λ r, (coe : K → (v.adic_completion K)) (algebra_map R K r)

/-- The natural inclusion of `R` in `adic_completion_integers`. -/
def inj_adic_completion_integers : R → (v.adic_completion_integers K) :=
λ r, ⟨(coe : K → (v.adic_completion K)) (algebra_map R K r), begin 
  change @valued.extension K _ _ _ v.adic_valued (algebra_map R K r) ≤ 1,
  rw @valued.extension_extends K _ _ _ v.adic_valued (algebra_map R K r),
  exact v.valuation_le_one _,
end⟩

/-- The diagonal inclusion `r ↦ (r)_v` of `R` in `R_hat`. -/
def inj_R : R → (R_hat R K) := λ r v, inj_adic_completion_integers R K v r
lemma uniform_space.completion.coe_inj {α : Type*} [uniform_space α] [separated_space α] :
  injective  (coe : α → uniform_space.completion α) := 
uniform_embedding.inj (uniform_space.completion.uniform_embedding_coe _)

lemma inj_adic_completion_integers.injective :
  function.injective (inj_adic_completion_integers R K v) :=
begin
  intros x y hxy,
  have h_inj : function.injective (coe : K → v.adic_completion K) :=
    @uniform_space.completion.coe_inj K v.adic_valued.to_uniform_space _,
  rw [inj_adic_completion_integers, subtype.mk_eq_mk] at hxy,
  exact (is_fraction_ring.injective R K) ((h_inj) hxy),
end

lemma inj_adic_completion_integers.map_one : inj_adic_completion_integers R K v 1 = 1 :=
by { rw inj_adic_completion_integers, simp_rw ring_hom.map_one, refl, }

lemma inj_R.map_one : inj_R R K 1 = 1 := 
by { rw inj_R, ext v, simp_rw inj_adic_completion_integers.map_one R K v, refl, }

lemma inj_adic_completion_integers.map_mul (x y : R) : inj_adic_completion_integers R K v (x*y) =
  (inj_adic_completion_integers R K v x) * (inj_adic_completion_integers R K v y) :=
begin
  rw inj_adic_completion_integers,
  simp_rw ring_hom.map_mul,
  ext,
  rw [subtype.coe_mk, subring.coe_mul, subtype.coe_mk, subtype.coe_mk,
    uniform_space.completion.coe_mul],
end

lemma inj_R.map_mul (x y : R): inj_R R K (x*y) = (inj_R R K x) * (inj_R R K y) :=
by { rw inj_R, ext v, apply congr_arg _ (inj_adic_completion_integers.map_mul R K v x y), }

/-- The inclusion of `R_hat` in `K_hat` is a homomorphism of additive monoids. -/
def group_hom_prod : add_monoid_hom (R_hat R K) (K_hat R K) := force_noncomputable
{ to_fun    := λ x v, x v,
  map_zero' := rfl,
  map_add'  := λ x y, by { ext v, rw [pi.add_apply, pi.add_apply, subring.coe_add], }}

/-- The inclusion of `R_hat` in `K_hat` is a ring homomorphism. -/
def hom_prod : ring_hom (R_hat R K) (K_hat R K)  := force_noncomputable --TODO: ask
{ to_fun   := λ x v, x v,
  map_one' := rfl,
  map_mul' := λ x y, by {ext p, rw [pi.mul_apply, pi.mul_apply, subring.coe_mul], },
  ..group_hom_prod R K, }

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adic_completion` with respect to `adic_completion_integers`. We prove that it is a commutative
ring and give it a topology that makes it into a topological ring. -/

/-- A tuple `(x_v)_v` is in the restricted product of the `adic_completion` with respect to
`adic_completion_integers` if for all but finitely many `v`, `x_v ∈ adic_completion_integers`. -/
def restricted : K_hat R K → Prop := λ x, 
 ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, (x v ∈ v.adic_completion_integers K)

/-- The finite adèle ring of `R` is the restricted product over all maximal ideals `v` of `R`
of `adic_completion` with respect to `adic_completion_integers`.-/
def finite_adele_ring' := { x : (K_hat R K) // 
  ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, (x v ∈ v.adic_completion_integers K) }

/-- The coercion map from `finite_adele_ring' R K` to `K_hat R K`. -/
def coe' : (finite_adele_ring' R K) → K_hat R K := force_noncomputable $ λ x, x.val
instance has_coe' : has_coe (finite_adele_ring' R K) (K_hat R K) := {coe := coe' R K } 
instance has_lift_t' : has_lift_t (finite_adele_ring' R K) (K_hat R K) := {lift := coe' R K } 

/-- The sum of two finite adèles is a finite adèle. -/
lemma restr_add (x y : finite_adele_ring' R K) : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  ((x.val + y.val) v ∈ v.adic_completion_integers K) := 
begin
  cases x with x hx,
  cases y with y hy,
  simp only [restricted] at hx hy ⊢,
  rw filter.eventually_cofinite at hx hy ⊢,
  have h_subset : {v : height_one_spectrum R | ¬ (x + y) v ∈  (v.adic_completion_integers K)} ⊆
    {v : height_one_spectrum R | ¬ x v ∈ (v.adic_completion_integers K)} ∪
    {v : height_one_spectrum R | ¬ y v ∈ (v.adic_completion_integers K)},
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq],
    rw mem_set_of_eq at hv,
    by_contradiction h,
    push_neg at h,
    apply hv,
    rw [adic_completion.is_integer, adic_completion.is_integer, ← max_le_iff] at h,
    rw [adic_completion.is_integer, pi.add_apply],
    exact le_trans (valued.v.map_add_le_max' (x v) (y v)) h },
  exact finite.subset (finite.union hx hy) h_subset,
end

/-- Addition on the finite adèle. ring. -/
def add' (x y : finite_adele_ring' R K) : finite_adele_ring' R K := 
⟨x.val + y.val, restr_add R K x y⟩

/-- The tuple `(0)_v` is a finite adèle. -/
lemma restr_zero : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  ((0 : v.adic_completion K) ∈ v.adic_completion_integers K) := 
begin
  rw filter.eventually_cofinite,
  have h_empty : {v : height_one_spectrum R | 
    ¬ ((0 : v.adic_completion K) ∈ v.adic_completion_integers K)} = ∅,
  { ext v, rw [mem_empty_iff_false, iff_false],
    intro hv,
    rw mem_set_of_eq at hv, apply hv, rw adic_completion.is_integer, 
    have h_zero : (valued.v (0 : v.adic_completion K) : (with_zero(multiplicative ℤ))) = 0 :=
    valued.v.map_zero',
    rw h_zero, exact zero_le_one' _ },
  rw h_empty,
  exact finite_empty,
end

/-- The negative of a finite adèle is a finite adèle. -/
lemma restr_neg (x : finite_adele_ring' R K)  : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  (-x.val v ∈ v.adic_completion_integers K) := 
begin
  cases x with x hx,
  have h : ∀ (v : height_one_spectrum R), (-x v ∈ v.adic_completion_integers K) ↔
    (x v ∈ v.adic_completion_integers K),
  { intro v,
    rw [adic_completion.is_integer, adic_completion.is_integer, valuation.map_neg], },
  simpa only [h] using hx,
end

/-- Negation on the finite adèle ring. -/
def neg' (x : finite_adele_ring' R K) : finite_adele_ring' R K := ⟨-x.val, restr_neg R K x⟩

/-- The product of two finite adèles is a finite adèle. -/
lemma restr_mul (x y : finite_adele_ring' R K) : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  ((x.val * y.val) v ∈ v.adic_completion_integers K) := 
begin
  cases x with x hx,
  cases y with y hy,
  simp only [restricted] at hx hy ⊢,
  rw filter.eventually_cofinite at hx hy ⊢,
  have h_subset : {v : height_one_spectrum R | ¬ (x * y) v ∈  (v.adic_completion_integers K)} ⊆
    {v : height_one_spectrum R | ¬ x v ∈ (v.adic_completion_integers K)} ∪
    {v : height_one_spectrum R | ¬ y v ∈ (v.adic_completion_integers K)},
  { intros v hv,
    rw [mem_union, mem_set_of_eq, mem_set_of_eq],
    rw mem_set_of_eq at hv,
    by_contradiction h,
    push_neg at h,
    apply hv,
    rw [adic_completion.is_integer, adic_completion.is_integer] at h,
    have h_mul : valued.v (x v * y v) = (valued.v (x v)) * (valued.v (y v)) 
    := (valued.v).map_mul' (x v) (y v),
    rw [adic_completion.is_integer, pi.mul_apply, h_mul,
      ← mul_one (1 : with_zero (multiplicative ℤ ))],
    exact @mul_le_one' (with_zero (multiplicative ℤ)) _ _ 
      (ordered_comm_monoid.to_covariant_class_left _) _ _ h.left h.right,  },
  exact finite.subset (finite.union hx hy) h_subset,
end

/-- Multiplication on the finite adèle ring. -/
def mul' (x y : finite_adele_ring' R K) : finite_adele_ring' R K := 
⟨x.val * y.val, restr_mul R K x y⟩

/-- The tuple `(1)_v` is a finite adèle. -/
lemma restr_one : ∀ᶠ (v : height_one_spectrum R) in filter.cofinite,
  ((1 : v.adic_completion K) ∈ v.adic_completion_integers K) := 
begin
  rw filter.eventually_cofinite,
  have h_empty : {v : height_one_spectrum R |
    ¬ ((1 : v.adic_completion K) ∈ v.adic_completion_integers K)} = ∅,
  { ext v, rw [mem_empty_iff_false, iff_false],intro hv,
    rw mem_set_of_eq at hv, apply hv, rw adic_completion.is_integer, 
    exact le_of_eq valued.v.map_one' },
  rw h_empty,
  exact finite_empty,
end

/-- `finite_adele_ring' R K` is a commutative additive group. -/
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

/-- `finite_adele_ring' R K` is a commutative ring. -/
instance : comm_ring (finite_adele_ring' R K) := 
{ mul           := mul' R K,
  mul_assoc     := λ x y z, by { unfold_projs, simp_rw [mul'], 
    rw [subtype.mk_eq_mk, mul_assoc]},
  one           := ⟨1, restr_one R K⟩,
  one_mul       := λ x, by { simp_rw [mul', one_mul, subtype.val_eq_coe, subtype.coe_eta] },
  mul_one       := λ x, by { simp_rw [mul', mul_one, subtype.val_eq_coe, subtype.coe_eta] },
  left_distrib  := λ x y z, by { unfold_projs, simp_rw [mul', add', left_distrib], },
  right_distrib := λ x y z, by { unfold_projs, simp_rw [mul', add', right_distrib], },
  mul_comm      := λ x y, by { unfold_projs, rw [mul', mul', subtype.mk_eq_mk, mul_comm], },
  ..(finite_adele_ring'.add_comm_group R K)}

@[norm_cast] lemma finite_adele_ring'.coe_add (x y : finite_adele_ring' R K) :
  (↑(x + y) : K_hat R K) = ↑x + ↑y := rfl

@[norm_cast] lemma finite_adele_ring'.coe_zero : (↑(0 : finite_adele_ring' R K) : K_hat R K) = 0 :=
rfl

@[norm_cast] lemma finite_adele_ring'.coe_neg (x : finite_adele_ring' R K) :
  (↑(-x) : K_hat R K) = -↑x  := rfl

@[norm_cast] lemma finite_adele_ring'.coe_mul (x y : finite_adele_ring' R K) : 
  (↑(x * y) : K_hat R K) = ↑x * ↑y := rfl

@[norm_cast] lemma finite_adele_ring'.coe_one : (↑(1 : finite_adele_ring' R K) : K_hat R K) = 1 :=
rfl

instance finite_adele_ring'.inhabited : inhabited (finite_adele_ring' R K) := 
{ default := ⟨0, restr_zero R K⟩ }

/-- The ring of integers `adic_completion_integers` is an open subset of `adic_completion`. -/
lemma adic_completion.is_open_adic_completion_integers :
  is_open ((v.adic_completion_integers K) : set (v.adic_completion K)) := 
begin
  rw is_open_iff_mem_nhds,
  intros x hx,
  rw [set_like.mem_coe, adic_completion.is_integer] at hx,
  rw valued.mem_nhds,
  use (1 : units (with_zero (multiplicative ℤ))),
  { intros y hy,
    rw [units.coe_one, mem_set_of_eq] at hy,
    rw [set_like.mem_coe, adic_completion.is_integer, ← sub_add_cancel y x],
    refine le_trans _ (max_le (le_of_lt hy) hx),
    exact valuation.map_add _ _ _ }
end

/-- A generating set for the topology on the finite adèle ring of `R` consists on products `∏_v U_v`
of open sets such that `U_v = adic_completion_integers` for all but finitely many maximal ideals
`v`. -/
def finite_adele_ring'.generating_set : set (set (finite_adele_ring' R K)) :=
{ U : set (finite_adele_ring' R K) |
  ∃ (V : Π (v : height_one_spectrum R), set (v.adic_completion K)),
  (∀ x : finite_adele_ring' R K, x ∈ U ↔ ∀ v, x.val v ∈ V v) ∧ 
  (∀ v, is_open (V v)) ∧ ∀ᶠ v in filter.cofinite, V v = v.adic_completion_integers K } 

/-- The topology on the finite adèle ring of `R`. -/
instance : topological_space (finite_adele_ring' R K) := topological_space.generate_from
  (finite_adele_ring'.generating_set R K)

private lemma set_cond_finite {x y: finite_adele_ring' R K} 
  {V : Π (v : height_one_spectrum R), set (v.adic_completion K)} 
  (hV_int: ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, V v =
    ↑(v.adic_completion_integers K)) :
  {v : height_one_spectrum R | ¬ (x.val v ∈ v.adic_completion_integers K ∧
    y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K)}.finite := 
begin
  have h_subset := subset.three_union (λ v, x.val v ∈ v.adic_completion_integers K)
    (λ v, y.val v ∈ v.adic_completion_integers K)
    (λ v, V v = v.adic_completion_integers K),
  exact finite.subset (finite.union (finite.union x.property y.property) hV_int) h_subset,
end

private lemma is_open_Vx  {x y: finite_adele_ring' R K}
  {V : Π (v : height_one_spectrum R), set (v.adic_completion K)}
  (hV : ∀ v : height_one_spectrum R, is_open 
    ((λ p : ( v.adic_completion K × v.adic_completion K), p.fst + p.snd) ⁻¹' V v))
  (hV_int: ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, V v = ↑(v.adic_completion_integers K))
  (hxy : ∀ (v : height_one_spectrum R), (x.val v, y.val v) ∈
    (λ p : (v.adic_completion K) × (v.adic_completion K), p.fst + p.snd) ⁻¹' V v ) 
  {Vx : Π (v : height_one_spectrum R), set (v.adic_completion K)}
  (hVx : Vx = λ v, ite ( x.val v ∈ v.adic_completion_integers K ∧
    y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K )
    (v.adic_completion_integers K) 
    (classical.some (is_open_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))) :
  is_open {z : finite_adele_ring' R K | ∀ (v : height_one_spectrum R), z.val v ∈ Vx v} :=
begin
  use Vx,
  refine ⟨λ x, by refl,_,_⟩,
  { intro v, simp only [hVx], split_ifs,
    { exact adic_completion.is_open_adic_completion_integers R K v },
    { exact (classical.some_spec (classical.some_spec (is_open_prod_iff.mp (hV v) 
        (x.val v) (y.val v) (hxy v)))).1 },},
    { have h_subset : {v : height_one_spectrum R | ¬ Vx v = v.adic_completion_integers K} ⊆
        {v : height_one_spectrum R | ¬ (x.val v ∈ v.adic_completion_integers K ∧
          y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K)},
    { intros v hv h_cond_v,
      simp only [mem_set_of_eq, hVx, if_pos h_cond_v] at hv,
      exact hv (eq.refl _), }, 
    apply finite.subset _ h_subset,
    apply set_cond_finite R K hV_int },
end

private lemma is_open_Vy {x y : finite_adele_ring' R K}
  {V : Π (v : height_one_spectrum R), set (v.adic_completion K)}
  (hV : ∀ v : height_one_spectrum R, is_open 
    ((λ p : ( v.adic_completion K × v.adic_completion K), p.fst + p.snd) ⁻¹' V v))
  (hV_int: ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, V v = ↑(v.adic_completion_integers K))
  (hxy : ∀ (v : height_one_spectrum R), (x.val v, y.val v) ∈
    (λ p : (v.adic_completion K) × (v.adic_completion K), p.fst + p.snd) ⁻¹' V v ) 
  {Vy : Π (v : height_one_spectrum R), set (v.adic_completion K)}
  (hVx : Vy = λ v, ite ( x.val v ∈ v.adic_completion_integers K ∧
    y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K )
    (v.adic_completion_integers K) (classical.some (classical.some_spec 
      (is_open_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v))))) :
  is_open {z : finite_adele_ring' R K | ∀ (v : height_one_spectrum R), z.val v ∈ Vy v} :=
begin
  use Vy,
  refine ⟨λ x, by refl,_,_⟩,
  { intro v, simp only [hVx], split_ifs,
    { exact adic_completion.is_open_adic_completion_integers R K v },
    { exact (classical.some_spec (classical.some_spec (is_open_prod_iff.mp (hV v) 
        (x.val v) (y.val v) (hxy v)))).2.1 },},
    { have h_subset : {v : height_one_spectrum R | ¬ Vy v = v.adic_completion_integers K} ⊆
        {v : height_one_spectrum R | ¬ (x.val v ∈ v.adic_completion_integers K ∧
          y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K)},
    { intros v hv h_cond_v,
      rw mem_set_of_eq at hv,
      simp only [hVx] at hv,
      rw if_pos h_cond_v at hv,
      exact hv (eq.refl _), }, 
    apply finite.subset _ h_subset,
    exact set_cond_finite R K hV_int },
end

/-- Addition on the finite adèle ring of `R` is continuous. -/
lemma finite_adele_ring'.continuous_add : 
  continuous (λ (p : finite_adele_ring' R K × finite_adele_ring' R K), p.fst + p.snd) :=
begin
  apply continuous_generated_from,
  rintros U ⟨V, hUV, hV_open, hV_int⟩,
  have hV : ∀ v : height_one_spectrum R, is_open 
    ((λ p : ( v.adic_completion K × v.adic_completion K), p.fst + p.snd) ⁻¹' V v) := 
  λ v, continuous.is_open_preimage continuous_add (V v) (hV_open v),
  rw is_open_prod_iff,
  intros x y hxy,
  have hxy' : ∀ (v : height_one_spectrum R), (x.val v, y.val v) ∈
    (λ p : (v.adic_completion K) × (v.adic_completion K), p.fst + p.snd) ⁻¹' V v :=
  λ v, (hUV _).mp hxy v,
  set cond := λ v : height_one_spectrum R, x.val v ∈ v.adic_completion_integers K ∧
    y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K with h_cond,
  have hS_fin : {v : height_one_spectrum R | ¬ (cond v)}.finite := set_cond_finite R K  hV_int,
  set Vx : Π (v : height_one_spectrum R), set (v.adic_completion K) := λ v, ite (cond v)
    (v.adic_completion_integers K)
    (classical.some (is_open_prod_iff.mp (hV v) _ _ (hxy' v))) with hVx,
  set Vy : Π (v : height_one_spectrum R), set (v.adic_completion K) := λ v, ite (cond v) 
    (v.adic_completion_integers K) (classical.some (classical.some_spec
      (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))) 
    with hVy,
  use [{z : finite_adele_ring' R K | ∀ v : height_one_spectrum R, z.val v ∈ Vx v },
    {z : finite_adele_ring' R K | ∀ v : height_one_spectrum R, z.val v ∈ Vy v }],
  refine ⟨is_open_Vx R K hV hV_int hxy' hVx, is_open_Vy R K hV hV_int hxy' hVy, _, _,_⟩,
  { rw [mem_set_of_eq],
    intro v,
    simp only [hVx],
    split_ifs,
    { exact h.1,},
    { exact (classical.some_spec (classical.some_spec 
        (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.1 },},
  { rw [mem_set_of_eq],
    intro v,
    simp only [hVy],
    split_ifs,
    { exact h.2.1 },
    { exact (classical.some_spec (classical.some_spec 
        (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.1 }},
  { intros p hp,
    rw [mem_prod, mem_set_of_eq, mem_set_of_eq] at hp,
    rw [mem_preimage, hUV],
    intro v,
    have hp' : prod.mk (p.fst.val v) (p.snd.val v) ∈ (Vx v) ×ˢ (Vy v) := 
    mem_prod.mpr ⟨hp.1 v, hp.2 v⟩,
    by_cases h_univ : V v = univ,
    { rw h_univ, exact mem_univ _},
    { simp only [hVx, hVy, if_neg h_univ] at hp',
      by_cases hv : cond v,
      { rw [if_pos hv, if_pos hv, mem_prod, set_like.mem_coe, adic_completion.is_integer,
          set_like.mem_coe, adic_completion.is_integer] at hp',
        rw [hv.2.2, set_like.mem_coe, adic_completion.is_integer],
        have h_max : valued.v ((p.fst + p.snd).val v) ≤ max (valued.v ((p.fst).val v))
          (valued.v ((p.snd).val v)) := valuation.map_add _ _ _,
        exact le_trans h_max (max_le hp'.1 hp'.2), },
      { rw [if_neg hv, if_neg hv] at hp',
        { exact (classical.some_spec (classical.some_spec
         (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.2 hp'}, }}}
end

private lemma is_open_Vx_mul  {x y: finite_adele_ring' R K}
  {V : Π (v : height_one_spectrum R), set (v.adic_completion K)}
  (hV : ∀ v : height_one_spectrum R, is_open 
    ((λ p : ( v.adic_completion K × v.adic_completion K), p.fst * p.snd) ⁻¹' V v))
  (hV_int: ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, V v = ↑(v.adic_completion_integers K))
  (hxy : ∀ (v : height_one_spectrum R), (x.val v, y.val v) ∈
    (λ p : (v.adic_completion K) × (v.adic_completion K), p.fst * p.snd) ⁻¹' V v ) 
  {Vx : Π (v : height_one_spectrum R), set (v.adic_completion K)}
  (hVx : Vx = λ v, ite ( x.val v ∈ v.adic_completion_integers K ∧
    y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K )
    (v.adic_completion_integers K) 
    (classical.some (is_open_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v)))) :
  is_open {z : finite_adele_ring' R K | ∀ (v : height_one_spectrum R), z.val v ∈ Vx v} :=
begin
  use Vx,
  refine ⟨λ x, by refl,_,_⟩,
  { intro v, simp only [hVx], split_ifs,
    { exact adic_completion.is_open_adic_completion_integers R K v },
    { exact (classical.some_spec (classical.some_spec (is_open_prod_iff.mp (hV v) 
        (x.val v) (y.val v) (hxy v)))).1 },},
    { have h_subset : {v : height_one_spectrum R | ¬ Vx v = v.adic_completion_integers K} ⊆
        {v : height_one_spectrum R | ¬ (x.val v ∈ v.adic_completion_integers K ∧
          y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K)},
    { intros v hv h_cond_v,
      simp only [mem_set_of_eq, hVx, if_pos h_cond_v] at hv,
      exact hv (eq.refl _), }, 
    apply finite.subset _ h_subset,
    apply set_cond_finite R K hV_int },
end

private lemma is_open_Vy_mul {x y : finite_adele_ring' R K}
  {V : Π (v : height_one_spectrum R), set (v.adic_completion K)}
  (hV : ∀ v : height_one_spectrum R, is_open 
    ((λ p : ( v.adic_completion K × v.adic_completion K), p.fst * p.snd) ⁻¹' V v))
  (hV_int: ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, V v = ↑(v.adic_completion_integers K))
  (hxy : ∀ (v : height_one_spectrum R), (x.val v, y.val v) ∈
    (λ p : (v.adic_completion K) × (v.adic_completion K), p.fst * p.snd) ⁻¹' V v ) 
  {Vy : Π (v : height_one_spectrum R), set (v.adic_completion K)}
  (hVx : Vy = λ v, ite ( x.val v ∈ v.adic_completion_integers K ∧
    y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K )
    (v.adic_completion_integers K) (classical.some (classical.some_spec 
      (is_open_prod_iff.mp (hV v) (x.val v) (y.val v) (hxy v))))) :
  is_open {z : finite_adele_ring' R K | ∀ (v : height_one_spectrum R), z.val v ∈ Vy v} :=
begin
  use Vy,
  refine ⟨λ x, by refl,_,_⟩,
  { intro v, simp only [hVx], split_ifs,
    { exact adic_completion.is_open_adic_completion_integers R K v },
    { exact (classical.some_spec (classical.some_spec (is_open_prod_iff.mp (hV v) 
        (x.val v) (y.val v) (hxy v)))).2.1 },},
    { have h_subset : {v : height_one_spectrum R | ¬ Vy v = v.adic_completion_integers K} ⊆
        {v : height_one_spectrum R | ¬ (x.val v ∈ v.adic_completion_integers K ∧
          y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K)},
    { intros v hv h_cond_v,
      rw mem_set_of_eq at hv,
      simp only [hVx] at hv,
      rw if_pos h_cond_v at hv,
      exact hv (eq.refl _), }, 
    apply finite.subset _ h_subset,
    exact set_cond_finite R K hV_int },
end

/-- Multiplication on the finite adèle ring of `R` is continuous. -/
lemma finite_adele_ring'.continuous_mul : 
  continuous (λ (p : finite_adele_ring' R K × finite_adele_ring' R K), p.fst * p.snd) :=
begin
 apply continuous_generated_from,
  rintros U ⟨V, hUV, hV_open, hV_int⟩,
  have hV : ∀ v : height_one_spectrum R, is_open 
    ((λ p : ( v.adic_completion K × v.adic_completion K), p.fst * p.snd) ⁻¹' V v) := 
  λ v, continuous.is_open_preimage continuous_mul (V v) (hV_open v),
  rw is_open_prod_iff,
  intros x y hxy,
  have hxy' : ∀ (v : height_one_spectrum R), (x.val v, y.val v) ∈
    (λ p : (v.adic_completion K) × (v.adic_completion K), p.fst * p.snd) ⁻¹' V v :=
  λ v, (hUV _).mp hxy v,
  set cond := λ v : height_one_spectrum R, x.val v ∈ v.adic_completion_integers K ∧
    y.val v ∈ v.adic_completion_integers K ∧ V v = v.adic_completion_integers K with h_cond,
  have hS_fin : {v : height_one_spectrum R | ¬ (cond v)}.finite := set_cond_finite R K hV_int,
  set Vx : Π (v : height_one_spectrum R), set (v.adic_completion K) := λ v, 
  ite (cond v) (v.adic_completion_integers K)
    (classical.some (is_open_prod_iff.mp (hV v) _ _ (hxy' v))) with hVx,
  set Vy : Π (v : height_one_spectrum R), set (v.adic_completion K) := λ v, ite (cond v) 
    (v.adic_completion_integers K)
    (classical.some (classical.some_spec (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))) with hVy,
  use [{z : finite_adele_ring' R K | ∀ v : height_one_spectrum R, z.val v ∈ Vx v },
    {z : finite_adele_ring' R K | ∀ v : height_one_spectrum R, z.val v ∈ Vy v }],
  refine ⟨is_open_Vx_mul R K hV hV_int hxy' hVx, is_open_Vy_mul R K hV hV_int hxy' hVy, _, _,_⟩,
  { rw [mem_set_of_eq],
    intro v,
    simp only [hVx],
    split_ifs,
    { exact h.1,},
    { exact (classical.some_spec (classical.some_spec 
        (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.1 },},
  { rw [mem_set_of_eq],
    intro v,
    simp only [hVy],
    split_ifs,
    { exact h.2.1 },
    { exact (classical.some_spec (classical.some_spec 
        (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.1 }},
  { intros p hp,
    rw [mem_prod, mem_set_of_eq, mem_set_of_eq] at hp,
    rw [mem_preimage, hUV],
    intro v,
    have hp' : prod.mk (p.fst.val v) (p.snd.val v) ∈ (Vx v) ×ˢ (Vy v) := 
    mem_prod.mpr ⟨hp.1 v, hp.2 v⟩,
    by_cases h_univ : V v = univ,
    { rw h_univ, exact mem_univ _},
    { simp only [hVx, hVy, if_neg h_univ] at hp',
      by_cases hv : cond v,
      { rw [if_pos hv, if_pos hv, mem_prod, set_like.mem_coe, adic_completion.is_integer,
          set_like.mem_coe, adic_completion.is_integer] at hp',
        rw [hv.2.2, set_like.mem_coe, adic_completion.is_integer],
        have h_mul : valued.v ((p.fst * p.snd).val v) = (valued.v ((p.fst).val v)) * 
          (valued.v ((p.snd).val v)) := valuation.map_mul _ _ _,
        rw h_mul,
        apply mul_le_one₀ hp'.1 hp'.2, },
      { rw [if_neg hv, if_neg hv] at hp',
        { exact (classical.some_spec (classical.some_spec
         (is_open_prod_iff.mp (hV v) _ _ (hxy' v)))).2.2.2.2 hp'}, }}}
end

instance : has_continuous_mul (finite_adele_ring' R K) := ⟨finite_adele_ring'.continuous_mul R K⟩

/-- The finite adèle ring of `R` is a topological ring. -/
instance : topological_ring (finite_adele_ring' R K) := 
{ continuous_add := finite_adele_ring'.continuous_add R K,
  continuous_neg := topological_semiring.has_continuous_neg_of_mul.continuous_neg,
  ..finite_adele_ring'.has_continuous_mul R K }

/-- The product `∏_v adic_completion_integers` is an open subset of the finite adèle ring of `R`. -/
lemma finite_adele_ring'.is_open_integer_subring :
  is_open {x : finite_adele_ring' R K |
    ∀ (v : height_one_spectrum R), x.val v ∈ v.adic_completion_integers K} :=
begin  
  apply topological_space.generate_open.basic,
  rw finite_adele_ring'.generating_set,
  use λ v, v.adic_completion_integers K,
  refine ⟨_, _,_⟩,
  { intro v, refl, },
  { intro v, exact adic_completion.is_open_adic_completion_integers R K v },
  { rw filter.eventually_cofinite,
    simp_rw [eq_self_iff_true, not_true, set_of_false, finite_empty] },
end

lemma finite_adele_ring'.is_open_integer_subring_opp : is_open
  {x : (finite_adele_ring' R K)ᵐᵒᵖ | 
    ∀ (v : height_one_spectrum R),(mul_opposite.unop x).val v ∈ v.adic_completion_integers K} :=
begin
  use {x : finite_adele_ring' R K | ∀ (v : height_one_spectrum R),
    x.val v ∈ v.adic_completion_integers K},
  use finite_adele_ring'.is_open_integer_subring R K,
  refl,
end

instance : comm_ring { x : (K_hat R K) // 
  ∀ᶠ (v : height_one_spectrum R) in filter.cofinite, (x v ∈ v.adic_completion_integers K)  } := 
finite_adele_ring'.comm_ring R K

lemma mul_apply (x y : finite_adele_ring' R K) :  
(⟨x.val * y.val, restr_mul R K x y⟩ : finite_adele_ring' R K) = x * y := rfl

lemma mul_apply_val (x y : finite_adele_ring' R K) :  
x.val * y.val = (x * y).val := rfl

@[simp] lemma one_def : (⟨1, restr_one R K⟩ : finite_adele_ring' R K) = 1 := rfl

@[simp] lemma zero_def : (⟨0, restr_zero R K⟩ : finite_adele_ring' R K) = 0 := rfl

/-- For any `x ∈ K`, the tuple `(x)_v` is a finite adèle. -/
lemma inj_K_image (x : K) : set.finite { v : height_one_spectrum R |
  ¬ (coe : K → (v.adic_completion K)) x ∈ (v.adic_completion_integers K)} := 
begin
  set supp := { v : height_one_spectrum R |
    ¬ (coe : K → (v.adic_completion K)) x ∈ (v.adic_completion_integers K)} with h_supp,
  obtain ⟨r, ⟨d, hd⟩, hx⟩ := is_localization.mk'_surjective (non_zero_divisors R) x,
  have hd_ne_zero : ideal.span{d} ≠ (0 : ideal R),
  { rw [ideal.zero_eq_bot, ne.def, ideal.span_singleton_eq_bot],
    apply non_zero_divisors.ne_zero hd, },
  obtain ⟨f, h_irred, h_assoc⟩:= wf_dvd_monoid.exists_factors (ideal.span{d}) hd_ne_zero,
  have hsubset : supp ⊆ { v : height_one_spectrum R | v.as_ideal ∣ ideal.span({d})},
  { rw h_supp,
    intros v hv,
    rw mem_set_of_eq at hv ⊢,
    have h_val : valued.v ((coe : K → (v.adic_completion K)) x) =
      @valued.extension K _ _ _ v.adic_valued x := rfl,
    rw [← @height_one_spectrum.valuation_lt_one_iff_dvd R _ _ _ K, v.valuation_of_algebra_map],
    by_contradiction h_one_le,
    have hdeq : v.int_valuation_def d = v.int_valuation d := rfl,
    rw [adic_completion.is_integer, h_val, valued.extension_extends _, v.adic_valued_apply, ← hx,
      v.valuation_of_mk', subtype.coe_mk, ← hdeq,
        (le_antisymm (v.int_valuation_le_one d) (not_lt.mp h_one_le)), div_one] at hv,
    exact hv (v.int_valuation_le_one r) },
  exact finite.subset (finite_factors d hd_ne_zero) hsubset,
end

/-- The diagonal inclusion `k ↦ (k)_v` of `K` into the finite adèle ring of `R`. -/
@[simps coe] def inj_K : K → finite_adele_ring' R K := 
λ x, ⟨(λ v : height_one_spectrum R, (coe : K → (v.adic_completion K)) x), inj_K_image R K x⟩

lemma inj_K_apply (k : K) : inj_K R K  k =
  ⟨(λ v : height_one_spectrum R, (coe : K → (v.adic_completion K)) k), inj_K_image R K k⟩ := rfl

@[simp] lemma inj_K.map_zero : inj_K R K 0 = 0 := by { rw inj_K, ext v, rw [subtype.coe_mk], refl }

@[simp] lemma inj_K.map_add (x y : K) : inj_K R K (x + y) = (inj_K R K x) + (inj_K R K y) := 
begin
  rw inj_K, ext v, unfold_projs, simp only [add'],
  rw [subtype.coe_mk, subtype.coe_mk, pi.add_apply], 
  norm_cast,
end

@[simp] lemma inj_K.map_one : inj_K R K 1 = 1 := by { rw inj_K, ext v, rw [subtype.coe_mk], refl }

@[simp] lemma inj_K.map_mul (x y : K) : inj_K R K (x*y) = (inj_K R K x) * (inj_K R K y) := 
begin
  rw inj_K, ext v, unfold_projs, simp only [mul'],
  rw [subtype.coe_mk, subtype.coe_mk, pi.mul_apply], 
  norm_cast,
end

/-- The map `inj_K` is an additive group homomorphism. -/
def inj_K.add_group_hom : add_monoid_hom K (finite_adele_ring' R K) := 
{ to_fun    := inj_K R K,
  map_zero' := inj_K.map_zero R K,
  map_add'  := inj_K.map_add R K, }

/-- The map `inj_K` is a ring homomorphism. -/
def inj_K.ring_hom : ring_hom K (finite_adele_ring' R K)  := 
{ to_fun   := inj_K R K,
  map_one' := inj_K.map_one R K,
  map_mul' := inj_K.map_mul R K,
  ..inj_K.add_group_hom R K }

lemma inj_K.ring_hom_apply {k : K} : inj_K.ring_hom R K k = inj_K R K k := rfl

/-- If `height_one_spectrum R` is nonempty, then `inj_K` is injective. Note that the nonemptiness
hypothesis is satisfied for every Dedekind domain that is not a field. -/
lemma inj_K.injective [inh : nonempty (height_one_spectrum R)] : injective (inj_K.ring_hom R K) :=
begin
  rw [ring_hom.injective_iff_ker_eq_bot, ring_hom.ker_eq_bot_iff_eq_zero],
  intros x hx,
  rw [inj_K.ring_hom, ring_hom.coe_mk, inj_K] at hx,
  dsimp only at hx,
  unfold_projs at hx,
  rw [subtype.mk_eq_mk] at hx,
  let v : height_one_spectrum R := (classical.inhabited_of_nonempty inh).default,
  have hv := congr_fun hx v,
  dsimp only at hv,
  have h_inj : function.injective (coe : K → (v.adic_completion K)) :=
    @uniform_space.completion.coe_inj K v.adic_valued.to_uniform_space _,
  apply h_inj hv,
end

/-! ### Alternative definition of the finite adèle ring
We can also define the finite adèle ring of `R` as the localization of `R_hat` at `R∖{0}`. We denote
this definition by `finite_adele_ring` and construct a ring homomorphism from `finite_adele_ring R`
to `finite_adele_ring' R`. 
TODO: show that this homomorphism is in fact an isomorphism of topological rings. -/

/-- `R∖{0}` is a submonoid of `R_hat R K`, via the inclusion `r ↦ (r)_v`. -/
def diag_R : submonoid (R_hat R K) := force_noncomputable
{ carrier  := (inj_R R K) '' {0}ᶜ,
  one_mem' :=  ⟨1, set.mem_compl_singleton_iff.mpr one_ne_zero, inj_R.map_one R K⟩,
  mul_mem' := 
  begin
    rintros a b ⟨za, hza, rfl⟩ ⟨zb, hzb, rfl⟩,
    exact ⟨za*zb, mul_ne_zero hza hzb, inj_R.map_mul R K za zb⟩,
  end }

/-- The finite adèle ring of `R` as the localization of `R_hat` at `R∖{0}`. -/
def finite_adele_ring := localization (diag_R R K)
instance : comm_ring (finite_adele_ring R K) := localization.comm_ring
instance : algebra (R_hat R K) (finite_adele_ring R K) := localization.algebra
instance : is_localization (diag_R R K) (finite_adele_ring R K):= localization.is_localization
instance : topological_space (finite_adele_ring R K) := localization.topological_space
instance : topological_ring (finite_adele_ring R K) := localization.topological_ring

lemma preimage_diag_R (x : diag_R R K) : ∃ r : R, r ≠ 0 ∧ inj_R R K r = (x : R_hat R K) := 
x.property

/-- For every `r ∈ R`, `(r)_v` is a unit of `K_hat R K`. -/
lemma hom_prod_diag_unit : ∀ x : (diag_R R K), is_unit (hom_prod R K x) :=
begin
  rintro ⟨x, r, hr, hrx⟩,
  rw [is_unit_iff_exists_inv, subtype.coe_mk],
  use (λ v : height_one_spectrum R, 1/(x v : v.adic_completion K)),
  ext v,
  rw [hom_prod, force_noncomputable_def, ring_hom.coe_mk, pi.mul_apply, pi.one_apply, 
  ← mul_div_assoc, mul_one, div_self],
  rw  [ne.def, subring.coe_eq_zero_iff, ← hrx, inj_R],
  simp only [inj_adic_completion_integers], 
  have h : (0 : v.adic_completion K) ∈ v.adic_completion_integers K,
  { rw [adic_completion.is_integer R K, valuation.map_zero], exact zero_le_one' _ },
  have h_zero : (0 : v.adic_completion_integers K) = ⟨(0 : v.adic_completion K), h⟩ := rfl,
  have h_inj : function.injective (coe : K → (v.adic_completion K)) :=
    @uniform_space.completion.coe_inj K v.adic_valued.to_uniform_space _,
  rw [h_zero, subtype.mk_eq_mk, ← uniform_space.completion.coe_zero, 
    ← (algebra_map R K).map_zero, ← ne.def, 
    injective.ne_iff (injective.comp h_inj (is_fraction_ring.injective R K))],
  rw [mem_compl_iff, mem_singleton_iff] at hr,
  exact hr,
end

/-- The map from `finite_adele_ring R K` to `K_hat R K` induced by `hom_prod`. -/
def map_to_K_hat (x : finite_adele_ring R K) : K_hat R K := 
is_localization.lift (hom_prod_diag_unit R K) x

/-- The image of `map_to_K_hat R K` is contained in `finite_adele_ring' R K`. -/
lemma restricted_image (x : finite_adele_ring R K) : set.finite 
  { v : height_one_spectrum R | ¬ (map_to_K_hat R K x v) ∈ (v.adic_completion_integers K)} :=
begin
  obtain ⟨r, d', hx⟩ := is_localization.mk'_surjective (diag_R R K) x,
  obtain ⟨d, hd_ne_zero, hd_inj⟩ := d'.property,
  have hd : ideal.span{d} ≠ (0 : ideal R),
  { rw [ideal.zero_eq_bot, ne.def, ideal.span_singleton_eq_bot],
    exact hd_ne_zero, },
  obtain ⟨f, h_irred, h_assoc⟩:= wf_dvd_monoid.exists_factors (ideal.span{d}) hd,
  have hsubset : { v : height_one_spectrum R |
    ¬ (map_to_K_hat R K x v) ∈ (v.adic_completion_integers K)} ⊆ 
    { v : height_one_spectrum R | v.as_ideal ∣ ideal.span({d})},
  { intros v hv,
    rw mem_set_of_eq at hv ⊢,
    rw [map_to_K_hat, ← hx, is_localization.lift_mk', pi.mul_apply] at hv,
    by_cases hr : hom_prod R K r v = 0,
    { rw [hr, zero_mul, adic_completion.is_integer, valuation.map_zero] at hv,
      exact absurd (with_zero.zero_le 1) hv, },
    { have h_inv : (((is_unit.lift_right ((hom_prod R K).to_monoid_hom.restrict (diag_R R K)) 
        (hom_prod_diag_unit R K)) d').inv v) *
        (((hom_prod R K).to_monoid_hom.restrict (diag_R R K)) d' v) = 1,
      { rw [units.inv_eq_coe_inv, ← pi.mul_apply, is_unit.lift_right_inv_mul 
          ((hom_prod R K).to_monoid_hom.restrict (diag_R R K)) (hom_prod_diag_unit R K) d',
          pi.one_apply]},
      have h_val : (valued.v (((is_unit.lift_right ((hom_prod R K).to_monoid_hom.restrict 
        (diag_R R K)) (hom_prod_diag_unit R K)) d').inv v))*
        ((valued.v (((hom_prod R K).to_monoid_hom.restrict (diag_R R K)) d' v)) :
          with_zero(multiplicative ℤ)) = 1,
      { rw [← valuation.map_mul, h_inv, valuation.map_one], },
      have h_coe : (((hom_prod R K).to_monoid_hom.restrict (diag_R R K)) d') v =
        ((d' : R_hat R K) v) := rfl,
      have hd' : ((d'.val) v).val = (coe : K → v.adic_completion K) (algebra_map R K d),
      { rw ← hd_inj, dsimp only [inj_R], rw inj_adic_completion_integers, },
      rw [adic_completion.is_integer, valuation.map_mul, ← units.inv_eq_coe_inv,
        eq_one_div_of_mul_eq_one_left h_val, ← mul_div_assoc, mul_one, 
        div_le_iff₀ (right_ne_zero_of_mul_eq_one h_val), one_mul, not_le, h_coe,
        ← subtype.val_eq_coe, ← subtype.val_eq_coe, hd',
        height_one_spectrum.valued_adic_completion_def, valued.extension_extends,
        v.adic_valued_apply] at hv,
      have h_val_r : (valued.v ((hom_prod R K) r v) : with_zero (multiplicative ℤ)) ≤ 1,
      { rw [hom_prod, force_noncomputable_def, ring_hom.coe_mk, ← subtype.val_eq_coe,
          ← adic_completion.is_integer],
        exact (r v).property, },
      exact (v.valuation_lt_one_iff_dvd d).mp (lt_of_lt_of_le hv h_val_r), }},
    exact finite.subset (finite_factors d hd) hsubset
end 

lemma map_to_K_hat.map_one : map_to_K_hat R K 1 = 1 := 
by { rw [map_to_K_hat, ring_hom.map_one] }

lemma map_to_K_hat.map_mul (x y : finite_adele_ring R K) : 
  map_to_K_hat R K (x*y) = map_to_K_hat R K x * map_to_K_hat R K y := 
by { rw [map_to_K_hat, map_to_K_hat, map_to_K_hat, ring_hom.map_mul], }

lemma map_to_K_hat.map_add (x y : finite_adele_ring R K) : map_to_K_hat R K (x + y) = 
  map_to_K_hat R K x + map_to_K_hat R K y := 
by { rw [map_to_K_hat, map_to_K_hat, map_to_K_hat, ring_hom.map_add], }

lemma map_to_K_hat.map_zero : map_to_K_hat R K 0 = 0 := 
by { rw [map_to_K_hat, ring_hom.map_zero] }

/-- `map_to_K_hat` is a ring homomorphism between our two definitions of finite adèle ring.  -/
def finite_adele.hom : (finite_adele_ring R K) →+* (finite_adele_ring' R K) := 
{ to_fun    := λ x, ⟨(map_to_K_hat R K x), restricted_image R K x⟩,
  map_one'  := begin
    have h_one : (1 : finite_adele_ring' R K) = ⟨1, restr_one R K⟩ := rfl,
    rw [h_one, subtype.mk_eq_mk],
    exact map_to_K_hat.map_one R K,
  end,
  map_mul'  := λ x y,
  by { unfold_projs, simp only [mul'], exact subtype.mk_eq_mk.mpr (map_to_K_hat.map_mul R K x y) },
  map_zero' := begin
    have h_zero : (0 : finite_adele_ring' R K) = ⟨0, restr_zero R K⟩ := rfl,
    rw [h_zero, subtype.mk_eq_mk],
    exact map_to_K_hat.map_zero R K,
  end,
  map_add'  := λ x y,
  by { unfold_projs, simp only [add'], exact subtype.mk_eq_mk.mpr (map_to_K_hat.map_add R K x y) }}