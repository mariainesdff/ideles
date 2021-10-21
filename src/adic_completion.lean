import ring_theory.ideal.operations
import topology.algebra.nonarchimedean.adic_topology

variables {R : Type*} [comm_ring R] (I : ideal R)

/-- The completion of a ring with respect to an ideal. -/
def ring.adic_completion : 
subring (Π n : ℕ, (I ^ n • ⊤ : ideal R).quotient) := 
{ carrier  := { f | ∀ {m n} (h : m ≤ n), ideal.quotient.lift ( I ^ n • ⊤ : ideal R) 
    (ideal.quotient.mk _)
    (by { intros a ha,
          rw [← ring_hom.mem_ker, ideal.mk_ker], 
          rw [algebra.id.smul_eq_mul, ideal.mul_top]at ha ⊢,
          apply ideal.pow_le_pow h,
          exact ha }) (f n) = f m },
  one_mem'  := λ m n hmn, by { rw [pi.one_apply, pi.one_apply, ring_hom.map_one] },
  mul_mem'  := λ f g hf hg m n hmn, by rw [pi.mul_apply, pi.mul_apply, ring_hom.map_mul, 
    hf hmn, hg hmn],
  zero_mem' := λ m n hmn, by rw [pi.zero_apply, pi.zero_apply, ring_hom.map_zero],
  add_mem'  := λ f g hf hg m n hmn, by rw [pi.add_apply, pi.add_apply,
    ring_hom.map_add, hf hmn, hg hmn],
  neg_mem'  := λ f hf m n hmn, by {rw [pi.neg_apply, pi.neg_apply, ring_hom.map_neg, hf hmn] }}

instance : comm_ring (ring.adic_completion I) := infer_instance

/-- The canonical ring map to the completion. -/
def ring.adic_completion.of : R →+* (ring.adic_completion I) := 
{ to_fun := λ x, ⟨λ (n : ℕ), (ideal.quotient.mk (I ^ n • ⊤ : ideal R) x), λ m n hmn, rfl⟩,
  map_one' := rfl,
  map_mul' := λ x y, rfl,
  map_zero' := rfl,
  map_add' := λ x y, rfl, }

@[simp] lemma ring.adic_completion.of_apply (x : R) (n : ℕ) :
  (ring.adic_completion.of I x).1 n = ideal.quotient.mk _ x := rfl

set_option profiler true
-- deterministic timeout
instance : algebra R (ring.adic_completion I) := 
ring_hom.to_algebra (ring.adic_completion.of I)

instance : algebra R (ring.adic_completion I):= 
{ smul := λ r x, (ring.adic_completion.of I r) * x,
  commutes' := λ r x, by {rw mul_comm},
  smul_def' := λ r x, rfl,
  ..(ring.adic_completion.of I) }

def I_hat : ideal (ring.adic_completion I) := 
{ carrier := ideal.span ((ring.adic_completion.of I) '' I),
  zero_mem' := by { simp_rw [set_like.mem_coe, ideal.zero_mem] },
  add_mem' := λ a b, by 
  { simp_rw [set_like.mem_coe],
    exact ideal.add_mem _, },
  smul_mem' := λ x a, by { simp_rw [set_like.mem_coe],
  exact ideal.mul_mem_left _ x, }}

-- deterministic timeout
--instance : ring_filter_basis (ring.adic_completion I) := ideal.ring_filter_basis (I_hat I)

/- instance : topological_space (ring.adic_completion I) := ideal.adic_topology (I_hat I) -/