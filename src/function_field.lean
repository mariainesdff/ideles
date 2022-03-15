/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import adeles_R
import number_theory.function_field

/-!
# The valuation at infinity on k(t)
For a field `k`, the valuation at infinity on the function field `k(t)` is the nonarchimedean
valuation on `k(t)` with uniformizer `1/t`. Explicitly, if `f/g ∈ k(t)` is a nonzero quotient of
polynomials, its valuation at infinity is `multiplicative.of_add(degree(f) - degree(g))`.

## Main definitions
- `kt_infty` : The completion `k((t⁻¹))` of `k(t)` with respect to `infty_valuation`.

## Tags
function field, valuation
-/

noncomputable theory

open_locale classical
open multiplicative function_field

variables (k : Type) [field k]

/-- The valued field `k(t)` with the valuation at infinity. -/
def infty_valued_kt : valued (ratfunc k) (with_zero (multiplicative ℤ)) := 
⟨infty_valuation k⟩

lemma infty_valued_kt.def {x : ratfunc k} :
  @valued.v (ratfunc k) _ _ _ (infty_valued_kt k) (x) = infty_valuation_def k x := rfl

/-- The topology structure on `k(t)` induced by the valuation at infinity. -/
def tsq' : topological_space (ratfunc k) :=
@valued.topological_space (ratfunc k) _ _ _ (infty_valued_kt k)

lemma tdrq' : @topological_division_ring (ratfunc k) _ (tsq' k) := 
@valued.topological_division_ring (ratfunc k) _ _ _ (infty_valued_kt k)

/-- The uniform structure on `k(t)` induced by the valuation at infinity. -/
def usq' : uniform_space (ratfunc k) := 
@topological_add_group.to_uniform_space (ratfunc k) _ (tsq' k) _

lemma ugq' : @uniform_add_group (ratfunc k) (usq' k) _ := 
@topological_add_group_is_uniform (ratfunc k) _ (tsq' k) _

lemma cfq' : @completable_top_field (ratfunc k) _ (usq' k) :=
@valued.completable (ratfunc k) _ _ _ (infty_valued_kt k)

lemma ssq' : @separated_space (ratfunc k) (usq' k) :=
@valued_ring.separated (ratfunc k) _ _ _ (infty_valued_kt k)

/-- The completion `k((t⁻¹))`  of `k(t)` with respect to the valuation at infinity. -/
def kt_infty := @uniform_space.completion (ratfunc k) (usq' k)

instance : field (kt_infty k) :=
@field_completion (ratfunc k) _ (usq' k) (tdrq' k) _ (ugq' k)

/-- The valuation at infinity on `k(t)` extends to a valuation on `kt_infty`. -/
instance valued_kt_infty : valued (kt_infty k) (with_zero (multiplicative ℤ)):= 
⟨@valued.extension_valuation (ratfunc k) _ _ _ (infty_valued_kt k)⟩

lemma valued_kt_infty.def {x : kt_infty k} :
  valued.v (x) = @valued.extension (ratfunc k) _ _ _ (infty_valued_kt k) x := rfl

instance tsq : topological_space (kt_infty k) :=
@valued.topological_space (kt_infty k) _ _ _ (valued_kt_infty k)

instance tdrq : @topological_division_ring (kt_infty k) _ (tsq k) := 
@valued.topological_division_ring (kt_infty k) _ _ _(valued_kt_infty k)

instance trq : @topological_ring (kt_infty k) (tsq k) _ := (tdrq k).to_topological_ring

instance tgq : @topological_add_group (kt_infty k) (tsq k) _ := 
@topological_ring.to_topological_add_group (kt_infty k) _ (tsq k) (trq k)

instance usq : uniform_space (kt_infty k) := 
@topological_add_group.to_uniform_space (kt_infty k) _ (tsq k) (tgq k)

instance ugq : @uniform_add_group (kt_infty k) (usq k) _ := 
@topological_add_group_is_uniform (kt_infty k) _ (tsq k) (tgq k)

instance : inhabited (kt_infty k) := ⟨(0 : kt_infty k)⟩