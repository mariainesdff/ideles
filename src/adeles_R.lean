import adic_completion
import algebraic_geometry.prime_spectrum
import data.int.basic
import data.nat.prime
import data.pnat.basic
import data.real.basic
import ring_theory.dedekind_domain
import topology.algebra.localization

variables (R K : Type*) [integral_domain R] [is_dedekind_domain R] [field K] [algebra R K] 
[is_fraction_ring R K] 

-- For a Dedekind domain, the maximal ideals are the nonzero prime ideals
def maximal_spectrum := {v : prime_spectrum R // v.as_ideal ≠ ⊥}

def R_hat := (Π (v : maximal_spectrum R), ring.adic_completion v.val.as_ideal)

instance : ring (R_hat R) := pi.ring

/- example (v : prime_spectrum R) : false :=
begin
  let : comm_ring (ring.adic_completion v.as_ideal) := by apply_instance,
  sorry,
end -/

def inj_R : R → (R_hat R) := 
λ (r: R), (λ (v : maximal_spectrum R), ring.adic_completion.of v.val.as_ideal r)

def diag_R : submonoid (R_hat R) := 
{ carrier  := (inj_R  R) '' set.compl {0},
  one_mem' := 
  begin
    use [1, set.mem_compl_singleton_iff.mpr one_ne_zero],
    rw inj_R, dsimp only, ext v, rw [pi.one_apply, ring_hom.map_one],
  end,
  mul_mem' := 
  begin
    rintros a b ⟨za, hza, rfl⟩ ⟨zb, hzb, rfl⟩,
    use [za*zb, mul_ne_zero hza hzb],
    rw inj_R, ext, dsimp only,
    rw [pi.mul_apply, ring_hom.map_mul],
  end }

