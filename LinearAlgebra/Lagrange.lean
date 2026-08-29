/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Wrenna Robson
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Lagrange interpolation

## Main definitions
* In everything that follows, `s : Finset ι` is a finite set of indices, with `v : ι → F` an
  indexing of the field over some type. We call the image of `v` on `s` the interpolation nodes,
  though strictly unique nodes are only defined when `v` is injective on `s`.
* `Lagrange.basisDivisor x y`, with `x y : F`. These are the normalised irreducible factors of
  the Lagrange basis polynomials. They evaluate to `1` at `x` and `0` at `y` when `x` and `y`
  are distinct.
* `Lagrange.basis v i` with `i : ι`: the Lagrange basis polynomial that evaluates to `1` at `v i`
  and `0` at `v j` for `i ≠ j`.
* `Lagrange.interpolate v r` where `r : ι → F` is a function from the fintype to the field: the
  Lagrange interpolant that evaluates to `r i` at `x i` for all `i : ι`. The `r i` are the _values_
  associated with the _nodes_ `x i`.
-/

@[expose] public section


open Polynomial

section PolynomialDetermination

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]}

section Finset

open Function Fintype
open scoped Finset

variable (s : Finset R)

/--
theorem `eq_zero_of_degree_lt_of_eval_finset_eq_zero` / 定理 `eq_zero_of_degree_lt_of_eval_finset_eq_zero`

English:
theorem eq_zero_of_degree_lt_of_eval_finset_eq_zero
  statement: (degree_f_lt : f.degree < #s)
  proof: by
  rw [← mem_degreeLT] at degree_f_lt
  simp_rw [eval_eq_sum_degreeLTEquiv degree_f_lt] at eval_f
  rw [← degreeLTEquiv_eq_zero_iff_eq_zero degree_f_lt]
  exact
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (Injective.comp (Embedding.subtype _).inj' (equivFinOfCardEq (card_coe _)).symm.injective)
      fun _ => eval_f _ (Finset.coe_mem _)

中文:
定理 eq_zero_of_degree_lt_of_eval_finset_eq_zero
  结论: (degree_f_lt : f.degree < #s)
  证明: by
  rw [← mem_degreeLT] at degree_f_lt
  simp_rw [eval_eq_sum_degreeLTEquiv degree_f_lt] at eval_f
  rw [← degreeLTEquiv_eq_zero_iff_eq_zero degree_f_lt]
  exact
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (Injective.comp (Embedding.subtype _).inj' (equivFinOfCardEq (card_coe _)).symm.injective)
      fun _ => eval_f _ (Finset.coe_mem _)

Depends on / 依赖: Embedding, Embedding.subtype, Finset, Finset.coe_mem, Injective, Injective.comp, Matrix, Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero, card_coe, coe_mem, degreeLTEquiv_eq_zero_iff_eq_zero, degree_f_lt, eq_zero_of_forall_index_sum_mul_pow_eq_zero, equivFinOfCardEq, eval_eq_sum_degreeLTEquiv, eval_f, injective, mem_degreeLT, simp_rw, subtype
-/
theorem eq_zero_of_degree_lt_of_eval_finset_eq_zero (degree_f_lt : f.degree < #s)
    (eval_f : forall x in s, f.eval x = 0) : f = 0 := by
  rw [← mem_degreeLT] at degree_f_lt
  simp_rw [eval_eq_sum_degreeLTEquiv degree_f_lt] at eval_f
  rw [← degreeLTEquiv_eq_zero_iff_eq_zero degree_f_lt]
  exact
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (Injective.comp (Embedding.subtype _).inj' (equivFinOfCardEq (card_coe _)).symm.injective)
      fun _ => eval_f _ (Finset.coe_mem _)

/--
theorem `eq_of_degree_sub_lt_of_eval_finset_eq` / 定理 `eq_of_degree_sub_lt_of_eval_finset_eq`

English:
theorem eq_of_degree_sub_lt_of_eval_finset_eq
  statement: (degree_fg_lt : (f - g).degree < #s)
  proof: by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

中文:
定理 eq_of_degree_sub_lt_of_eval_finset_eq
  结论: (degree_fg_lt : (f - g).degree < #s)
  证明: by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

Depends on / 依赖: degree_fg_lt, eq_zero_of_degree_lt_of_eval_finset_eq_zero, eval_fg, eval_sub, simp_rw, sub_eq_zero
-/
theorem eq_of_degree_sub_lt_of_eval_finset_eq (degree_fg_lt : (f - g).degree < #s)
    (eval_fg : forall x in s, f.eval x = g.eval x) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

/--
theorem `eq_of_degrees_lt_of_eval_finset_eq` / 定理 `eq_of_degrees_lt_of_eval_finset_eq`

English:
theorem eq_of_degrees_lt_of_eval_finset_eq
  statement: (degree_f_lt : f.degree < #s)
  proof: by
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ ?_ eval_fg
  rw [← mem_degreeLT]; exact Submodule.sub_mem _ degree_f_lt degree_g_lt

中文:
定理 eq_of_degrees_lt_of_eval_finset_eq
  结论: (degree_f_lt : f.degree < #s)
  证明: by
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ ?_ eval_fg
  rw [← mem_degreeLT]; exact Submodule.sub_mem _ degree_f_lt degree_g_lt

Depends on / 依赖: Submodule, Submodule.sub_mem, degree_f_lt, degree_g_lt, eq_of_degree_sub_lt_of_eval_finset_eq, eval_fg, mem_degreeLT, sub_mem
-/
theorem eq_of_degrees_lt_of_eval_finset_eq (degree_f_lt : f.degree < #s)
    (degree_g_lt : g.degree < #s) (eval_fg : forall x in s, f.eval x = g.eval x) : f = g := by
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ ?_ eval_fg
  rw [← mem_degreeLT]; exact Submodule.sub_mem _ degree_f_lt degree_g_lt

/--
theorem `eq_of_degree_le_of_eval_finset_eq` / 定理 `eq_of_degree_le_of_eval_finset_eq`

English:
theorem eq_of_degree_le_of_eval_finset_eq
  proof: by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_finset_eq s
      (lt_of_lt_of_le (degree_sub_lt_left h_deg_eq hf hlc) h_deg_le) h_eval

中文:
定理 eq_of_degree_le_of_eval_finset_eq
  证明: by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_finset_eq s
      (lt_of_lt_of_le (degree_sub_lt_left h_deg_eq hf hlc) h_deg_le) h_eval

Depends on / 依赖: degree_eq_bot, degree_sub_lt_left, degree_zero, eq_comm, eq_of_degree_sub_lt_of_eval_finset_eq, eq_or_ne, h_deg_eq, h_deg_le, h_eval, lt_of_lt_of_le
-/
theorem eq_of_degree_le_of_eval_finset_eq
    (h_deg_le : f.degree <= #s)
    (h_deg_eq : f.degree = g.degree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (h_eval : forall x in s, f.eval x = g.eval x) :
    f = g := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_finset_eq s
      (lt_of_lt_of_le (degree_sub_lt_left h_deg_eq hf hlc) h_deg_le) h_eval

end Finset

section Indexed

open Finset

variable {ι : Type*} {v : ι -> R} (s : Finset ι)

/--
theorem `eq_zero_of_degree_lt_of_eval_index_eq_zero` / 定理 `eq_zero_of_degree_lt_of_eval_index_eq_zero`

English:
theorem eq_zero_of_degree_lt_of_eval_index_eq_zero
  statement: (hvs : Set.InjOn v s)
  proof: by
  classical
    rw [← card_image_of_injOn hvs] at degree_f_lt
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_f_lt ?_
    intro x hx
    rcases mem_image.mp hx with ⟨_, hj, rfl⟩
    exact eval_f _ hj

中文:
定理 eq_zero_of_degree_lt_of_eval_index_eq_zero
  结论: (hvs : 集合.单射限制 v s)
  证明: by
  classical
    rw [← card_image_of_injOn hvs] at degree_f_lt
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_f_lt ?_
    intro x hx
    rcases mem_image.mp hx with ⟨_, hj, rfl⟩
    exact eval_f _ hj

Depends on / 依赖: card_image_of_injOn, classical, degree_f_lt, eq_zero_of_degree_lt_of_eval_finset_eq_zero, eval_f, mem_image, mem_image.mp
-/
theorem eq_zero_of_degree_lt_of_eval_index_eq_zero (hvs : Set.InjOn v s)
    (degree_f_lt : f.degree < #s) (eval_f : forall i in s, f.eval (v i) = 0) : f = 0 := by
  classical
    rw [← card_image_of_injOn hvs] at degree_f_lt
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_f_lt ?_
    intro x hx
    rcases mem_image.mp hx with ⟨_, hj, rfl⟩
    exact eval_f _ hj

/--
theorem `eq_of_degree_sub_lt_of_eval_index_eq` / 定理 `eq_of_degree_sub_lt_of_eval_index_eq`

English:
theorem eq_of_degree_sub_lt_of_eval_index_eq
  statement: (hvs : Set.InjOn v s)
  proof: by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero _ hvs degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

中文:
定理 eq_of_degree_sub_lt_of_eval_index_eq
  结论: (hvs : 集合.单射限制 v s)
  证明: by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero _ hvs degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

Depends on / 依赖: degree_fg_lt, eq_zero_of_degree_lt_of_eval_index_eq_zero, eval_fg, eval_sub, simp_rw, sub_eq_zero
-/
theorem eq_of_degree_sub_lt_of_eval_index_eq (hvs : Set.InjOn v s)
    (degree_fg_lt : (f - g).degree < #s) (eval_fg : forall i in s, f.eval (v i) = g.eval (v i)) :
    f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero _ hvs degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

/--
theorem `eq_of_degrees_lt_of_eval_index_eq` / 定理 `eq_of_degrees_lt_of_eval_index_eq`

English:
theorem eq_of_degrees_lt_of_eval_index_eq
  statement: (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
  proof: by
  refine eq_of_degree_sub_lt_of_eval_index_eq _ hvs ?_ eval_fg
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt ⊢
  exact Submodule.sub_mem _ degree_f_lt degree_g_lt

中文:
定理 eq_of_degrees_lt_of_eval_index_eq
  结论: (hvs : 集合.单射限制 v s) (degree_f_lt : f.degree < #s)
  证明: by
  refine eq_of_degree_sub_lt_of_eval_index_eq _ hvs ?_ eval_fg
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt ⊢
  exact Submodule.sub_mem _ degree_f_lt degree_g_lt

Depends on / 依赖: Submodule, Submodule.sub_mem, degree_f_lt, degree_g_lt, eq_of_degree_sub_lt_of_eval_index_eq, eval_fg, mem_degreeLT, sub_mem
-/
theorem eq_of_degrees_lt_of_eval_index_eq (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
    (degree_g_lt : g.degree < #s) (eval_fg : forall i in s, f.eval (v i) = g.eval (v i)) : f = g := by
  refine eq_of_degree_sub_lt_of_eval_index_eq _ hvs ?_ eval_fg
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt ⊢
  exact Submodule.sub_mem _ degree_f_lt degree_g_lt

/--
theorem `eq_of_degree_le_of_eval_index_eq` / 定理 `eq_of_degree_le_of_eval_index_eq`

English:
theorem eq_of_degree_le_of_eval_index_eq
  statement: (hvs : Set.InjOn v s)
  proof: by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_index_eq s hvs
      (lt_of_lt_of_le (degree_sub_lt_left h_deg_eq hf hlc) h_deg_le)
      h_eval

中文:
定理 eq_of_degree_le_of_eval_index_eq
  结论: (hvs : 集合.单射限制 v s)
  证明: by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_index_eq s hvs
      (lt_of_lt_of_le (degree_sub_lt_left h_deg_eq hf hlc) h_deg_le)
      h_eval

Depends on / 依赖: degree_eq_bot, degree_sub_lt_left, degree_zero, eq_comm, eq_of_degree_sub_lt_of_eval_index_eq, eq_or_ne, h_deg_eq, h_deg_le, h_eval, lt_of_lt_of_le
-/
theorem eq_of_degree_le_of_eval_index_eq (hvs : Set.InjOn v s)
    (h_deg_le : f.degree <= #s)
    (h_deg_eq : f.degree = g.degree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (h_eval : forall i in s, f.eval (v i) = g.eval (v i)) : f = g := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_index_eq s hvs
      (lt_of_lt_of_le (degree_sub_lt_left h_deg_eq hf hlc) h_deg_le)
      h_eval

end Indexed

end Polynomial

end PolynomialDetermination

noncomputable section

namespace Lagrange

open Polynomial

section BasisDivisor
variable {F : Type*} [Field F]
variable {x y : F}

/--
Definition of `basisDivisor` / `basisDivisor` 的定义

English:
definition basisDivisor
  signature: (x y : F)
  body: C (x - y)⁻¹ * (X - C y)

中文:
定义 basisDivisor
  签名: (x y : F)
  定义体: C (x - y)⁻¹ * (X - C y)
-/
def basisDivisor (x y : F) : F[X] :=
  C (x - y)⁻¹ * (X - C y)

/--
theorem `basisDivisor_self` / 定理 `basisDivisor_self`

English:
theorem basisDivisor_self
  statement: basisDivisor x x = 0
  proof: by
  simp only [basisDivisor, sub_self, inv_zero, map_zero, zero_mul]

中文:
定理 basisDivisor_self
  结论: basisDivisor x x = 0
  证明: by
  simp only [basisDivisor, sub_self, inv_zero, map_zero, zero_mul]

Depends on / 依赖: basisDivisor, inv_zero, map_zero, sub_self, zero_mul
-/
theorem basisDivisor_self : basisDivisor x x = 0 := by
  simp only [basisDivisor, sub_self, inv_zero, map_zero, zero_mul]

/--
theorem `basisDivisor_inj` / 定理 `basisDivisor_inj`

English:
theorem basisDivisor_inj
  given: (hxy : basisDivisor x y = 0)
  statement: x = y
  proof: by
  simp_rw [basisDivisor, mul_eq_zero, X_sub_C_ne_zero, or_false, C_eq_zero, inv_eq_zero,
    sub_eq_zero] at hxy
  exact hxy

@[simp]

中文:
定理 basisDivisor_inj
  条件: (hxy : basisDivisor x y = 0)
  结论: x = y
  证明: by
  simp_rw [basisDivisor, mul_eq_zero, X_sub_C_ne_zero, or_false, C_eq_zero, inv_eq_zero,
    sub_eq_zero] at hxy
  exact hxy

@[simp]

Depends on / 依赖: C_eq_zero, X_sub_C_ne_zero, basisDivisor, inv_eq_zero, mul_eq_zero, or_false, simp_rw, sub_eq_zero
-/
theorem basisDivisor_inj (hxy : basisDivisor x y = 0) : x = y := by
  simp_rw [basisDivisor, mul_eq_zero, X_sub_C_ne_zero, or_false, C_eq_zero, inv_eq_zero,
    sub_eq_zero] at hxy
  exact hxy

@[simp]
/--
theorem `basisDivisor_eq_zero_iff` / 定理 `basisDivisor_eq_zero_iff`

English:
theorem basisDivisor_eq_zero_iff
  statement: basisDivisor x y = 0 ↔ x = y
  proof: ⟨basisDivisor_inj, fun H => H ▸ basisDivisor_self⟩

中文:
定理 basisDivisor_eq_zero_iff
  结论: basisDivisor x y = 0 ↔ x = y
  证明: ⟨basisDivisor_inj, fun H => H ▸ basisDivisor_self⟩

Depends on / 依赖: basisDivisor_inj, basisDivisor_self
-/
theorem basisDivisor_eq_zero_iff : basisDivisor x y = 0 ↔ x = y :=
  ⟨basisDivisor_inj, fun H => H ▸ basisDivisor_self⟩

/--
theorem `basisDivisor_ne_zero_iff` / 定理 `basisDivisor_ne_zero_iff`

English:
theorem basisDivisor_ne_zero_iff
  statement: basisDivisor x y != 0 ↔ x != y
  proof: by
  rw [Ne]; rw [basisDivisor_eq_zero_iff]

中文:
定理 basisDivisor_ne_zero_iff
  结论: basisDivisor x y != 0 ↔ x != y
  证明: by
  rw [Ne]; rw [basisDivisor_eq_zero_iff]

Depends on / 依赖: basisDivisor_eq_zero_iff
-/
theorem basisDivisor_ne_zero_iff : basisDivisor x y != 0 ↔ x != y := by
  rw [Ne]; rw [basisDivisor_eq_zero_iff]

/--
theorem `degree_basisDivisor_of_ne` / 定理 `degree_basisDivisor_of_ne`

English:
theorem degree_basisDivisor_of_ne
  given: (hxy : x != y)
  statement: (basisDivisor x y).degree = 1
  proof: by
  rw [basisDivisor]; rw [degree_mul]; rw [degree_X_sub_C]; rw [degree_C]; rw [zero_add]
  exact inv_ne_zero (sub_ne_zero_of_ne hxy)

@[simp]

中文:
定理 degree_basisDivisor_of_ne
  条件: (hxy : x != y)
  结论: (basisDivisor x y).degree = 1
  证明: by
  rw [basisDivisor]; rw [degree_mul]; rw [degree_X_sub_C]; rw [degree_C]; rw [zero_add]
  exact inv_ne_zero (sub_ne_zero_of_ne hxy)

@[simp]

Depends on / 依赖: basisDivisor, degree_C, degree_X_sub_C, degree_mul, inv_ne_zero, sub_ne_zero_of_ne, zero_add
-/
theorem degree_basisDivisor_of_ne (hxy : x != y) : (basisDivisor x y).degree = 1 := by
  rw [basisDivisor]; rw [degree_mul]; rw [degree_X_sub_C]; rw [degree_C]; rw [zero_add]
  exact inv_ne_zero (sub_ne_zero_of_ne hxy)

@[simp]
/--
theorem `degree_basisDivisor_self` / 定理 `degree_basisDivisor_self`

English:
theorem degree_basisDivisor_self
  statement: (basisDivisor x x).degree = ⊥
  proof: by
  rw [basisDivisor_self]; rw [degree_zero]

中文:
定理 degree_basisDivisor_self
  结论: (basisDivisor x x).degree = ⊥
  证明: by
  rw [basisDivisor_self]; rw [degree_zero]

Depends on / 依赖: basisDivisor_self, degree_zero
-/
theorem degree_basisDivisor_self : (basisDivisor x x).degree = ⊥ := by
  rw [basisDivisor_self]; rw [degree_zero]

/--
theorem `natDegree_basisDivisor_self` / 定理 `natDegree_basisDivisor_self`

English:
theorem natDegree_basisDivisor_self
  statement: (basisDivisor x x).natDegree = 0
  proof: by
  rw [basisDivisor_self]; rw [natDegree_zero]

中文:
定理 natDegree_basisDivisor_self
  结论: (basisDivisor x x).natDegree = 0
  证明: by
  rw [basisDivisor_self]; rw [natDegree_zero]

Depends on / 依赖: basisDivisor_self, natDegree_zero
-/
theorem natDegree_basisDivisor_self : (basisDivisor x x).natDegree = 0 := by
  rw [basisDivisor_self]; rw [natDegree_zero]

/--
theorem `natDegree_basisDivisor_of_ne` / 定理 `natDegree_basisDivisor_of_ne`

English:
theorem natDegree_basisDivisor_of_ne
  given: (hxy : x != y)
  statement: (basisDivisor x y).natDegree = 1
  proof: natDegree_eq_of_degree_eq_some (degree_basisDivisor_of_ne hxy)

@[simp]

中文:
定理 natDegree_basisDivisor_of_ne
  条件: (hxy : x != y)
  结论: (basisDivisor x y).natDegree = 1
  证明: natDegree_eq_of_degree_eq_some (degree_basisDivisor_of_ne hxy)

@[simp]

Depends on / 依赖: degree_basisDivisor_of_ne, natDegree_eq_of_degree_eq_some
-/
theorem natDegree_basisDivisor_of_ne (hxy : x != y) : (basisDivisor x y).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some (degree_basisDivisor_of_ne hxy)

@[simp]
/--
theorem `eval_basisDivisor_right` / 定理 `eval_basisDivisor_right`

English:
theorem eval_basisDivisor_right
  statement: eval y (basisDivisor x y) = 0
  proof: by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]

中文:
定理 eval_basisDivisor_right
  结论: eval y (basisDivisor x y) = 0
  证明: by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]

Depends on / 依赖: basisDivisor, eval_C, eval_X, eval_mul, eval_sub, mul_zero, sub_self
-/
theorem eval_basisDivisor_right : eval y (basisDivisor x y) = 0 := by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]

/--
theorem `eval_basisDivisor_left_of_ne` / 定理 `eval_basisDivisor_left_of_ne`

English:
theorem eval_basisDivisor_left_of_ne
  given: (hxy : x != y)
  statement: eval x (basisDivisor x y) = 1
  proof: by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  exact inv_mul_cancel₀ (sub_ne_zero_of_ne hxy)

中文:
定理 eval_basisDivisor_left_of_ne
  条件: (hxy : x != y)
  结论: eval x (basisDivisor x y) = 1
  证明: by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  exact inv_mul_cancel₀ (sub_ne_zero_of_ne hxy)

Depends on / 依赖: basisDivisor, eval_C, eval_X, eval_mul, eval_sub, sub_ne_zero_of_ne
-/
theorem eval_basisDivisor_left_of_ne (hxy : x != y) : eval x (basisDivisor x y) = 1 := by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  exact inv_mul_cancel₀ (sub_ne_zero_of_ne hxy)

end BasisDivisor

section Basis

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι -> F} {i j : ι}

open Finset

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: (s : Finset ι) (v : ι -> F) (i : ι)
  body: ∏ j in s.erase i, basisDivisor (v i) (v j)

@[simp]

中文:
定义 basis
  签名: (s : 有限集 ι) (v : ι -> F) (i : ι)
  定义体: ∏ j in s.erase i, basisDivisor (v i) (v j)

@[simp]
-/
protected def basis (s : Finset ι) (v : ι -> F) (i : ι) : F[X] :=
  ∏ j in s.erase i, basisDivisor (v i) (v j)

@[simp]
/--
theorem `basis_empty` / 定理 `basis_empty`

English:
theorem basis_empty
  statement: Lagrange.basis ∅ v i = 1
  proof: rfl

@[simp]

中文:
定理 basis_empty
  结论: Lagrange.basis ∅ v i = 1
  证明: rfl

@[simp]
-/
theorem basis_empty : Lagrange.basis ∅ v i = 1 :=
  rfl

@[simp]
/--
theorem `basis_singleton` / 定理 `basis_singleton`

English:
theorem basis_singleton
  given: (i : ι)
  statement: Lagrange.basis {i} v i = 1
  proof: by
  rw [Lagrange.basis]; rw [erase_singleton]; rw [prod_empty]

@[simp]

中文:
定理 basis_singleton
  条件: (i : ι)
  结论: Lagrange.basis {i} v i = 1
  证明: by
  rw [Lagrange.basis]; rw [erase_singleton]; rw [prod_empty]

@[simp]

Depends on / 依赖: Lagrange, Lagrange.basis, erase_singleton, prod_empty
-/
theorem basis_singleton (i : ι) : Lagrange.basis {i} v i = 1 := by
  rw [Lagrange.basis]; rw [erase_singleton]; rw [prod_empty]

@[simp]
/--
theorem `basis_pair_left` / 定理 `basis_pair_left`

English:
theorem basis_pair_left
  given: (hij : i != j)
  statement: Lagrange.basis {i, j} v i = basisDivisor (v i) (v j)
  proof: by
  simp only [Lagrange.basis, hij, erase_insert_eq_erase, erase_eq_of_notMem, mem_singleton,
    not_false_iff, prod_singleton]

@[simp]

中文:
定理 basis_pair_left
  条件: (hij : i != j)
  结论: Lagrange.basis {i, j} v i = basisDivisor (v i) (v j)
  证明: by
  simp only [Lagrange.basis, hij, erase_insert_eq_erase, erase_eq_of_notMem, mem_singleton,
    not_false_iff, prod_singleton]

@[simp]

Depends on / 依赖: Lagrange, Lagrange.basis, erase_eq_of_notMem, erase_insert_eq_erase, mem_singleton, not_false_iff, prod_singleton
-/
theorem basis_pair_left (hij : i != j) : Lagrange.basis {i, j} v i = basisDivisor (v i) (v j) := by
  simp only [Lagrange.basis, hij, erase_insert_eq_erase, erase_eq_of_notMem, mem_singleton,
    not_false_iff, prod_singleton]

@[simp]
/--
theorem `basis_pair_right` / 定理 `basis_pair_right`

English:
theorem basis_pair_right
  given: (hij : i != j)
  statement: Lagrange.basis {i, j} v j = basisDivisor (v j) (v i)
  proof: by
  rw [pair_comm]
  exact basis_pair_left hij.symm

中文:
定理 basis_pair_right
  条件: (hij : i != j)
  结论: Lagrange.basis {i, j} v j = basisDivisor (v j) (v i)
  证明: by
  rw [pair_comm]
  exact basis_pair_left hij.symm

Depends on / 依赖: basis_pair_left, hij.symm, pair_comm
-/
theorem basis_pair_right (hij : i != j) : Lagrange.basis {i, j} v j = basisDivisor (v j) (v i) := by
  rw [pair_comm]
  exact basis_pair_left hij.symm

/--
theorem `basis_ne_zero` / 定理 `basis_ne_zero`

English:
theorem basis_ne_zero
  given: (hvs : Set.InjOn v s) (hi : i in s)
  statement: Lagrange.basis s v i != 0
  proof: by
  simp_rw [Lagrange.basis, prod_ne_zero_iff, Ne, mem_erase]
  rintro j ⟨hij, hj⟩
  rw [basisDivisor_eq_zero_iff]; rw [hvs.eq_iff hi hj]
  exact hij.symm

@[simp]

中文:
定理 basis_ne_zero
  条件: (hvs : 集合.单射限制 v s) (hi : i in s)
  结论: Lagrange.basis s v i != 0
  证明: by
  simp_rw [Lagrange.basis, prod_ne_zero_iff, Ne, mem_erase]
  rintro j ⟨hij, hj⟩
  rw [basisDivisor_eq_zero_iff]; rw [hvs.eq_iff hi hj]
  exact hij.symm

@[simp]

Depends on / 依赖: Lagrange, Lagrange.basis, basisDivisor_eq_zero_iff, eq_iff, hij.symm, hvs.eq_iff, mem_erase, prod_ne_zero_iff, simp_rw
-/
theorem basis_ne_zero (hvs : Set.InjOn v s) (hi : i in s) : Lagrange.basis s v i != 0 := by
  simp_rw [Lagrange.basis, prod_ne_zero_iff, Ne, mem_erase]
  rintro j ⟨hij, hj⟩
  rw [basisDivisor_eq_zero_iff]; rw [hvs.eq_iff hi hj]
  exact hij.symm

@[simp]
/--
theorem `eval_basis_self` / 定理 `eval_basis_self`

English:
theorem eval_basis_self
  given: (hvs : Set.InjOn v s) (hi : i in s)
  proof: by
  rw [Lagrange.basis]; rw [eval_prod]
  refine prod_eq_one fun j H => ?_
  rw [eval_basisDivisor_left_of_ne]
  rcases mem_erase.mp H with ⟨hij, hj⟩
  exact mt (hvs hi hj) hij.symm

@[simp]

中文:
定理 eval_basis_self
  条件: (hvs : 集合.单射限制 v s) (hi : i in s)
  证明: by
  rw [Lagrange.basis]; rw [eval_prod]
  refine prod_eq_one fun j H => ?_
  rw [eval_basisDivisor_left_of_ne]
  rcases mem_erase.mp H with ⟨hij, hj⟩
  exact mt (hvs hi hj) hij.symm

@[simp]

Depends on / 依赖: Lagrange, Lagrange.basis, eval_basisDivisor_left_of_ne, eval_prod, hij.symm, mem_erase, mem_erase.mp, prod_eq_one
-/
theorem eval_basis_self (hvs : Set.InjOn v s) (hi : i in s) :
    (Lagrange.basis s v i).eval (v i) = 1 := by
  rw [Lagrange.basis]; rw [eval_prod]
  refine prod_eq_one fun j H => ?_
  rw [eval_basisDivisor_left_of_ne]
  rcases mem_erase.mp H with ⟨hij, hj⟩
  exact mt (hvs hi hj) hij.symm

@[simp]
/--
theorem `eval_basis_of_ne` / 定理 `eval_basis_of_ne`

English:
theorem eval_basis_of_ne
  given: (hij : i != j) (hj : j in s)
  statement: (Lagrange.basis s v i).eval (v j) = 0
  proof: by
  simp_rw [Lagrange.basis, eval_prod, prod_eq_zero_iff]
  exact ⟨j, ⟨mem_erase.mpr ⟨hij.symm, hj⟩, eval_basisDivisor_right⟩⟩

@[simp]

中文:
定理 eval_basis_of_ne
  条件: (hij : i != j) (hj : j in s)
  结论: (Lagrange.basis s v i).eval (v j) = 0
  证明: by
  simp_rw [Lagrange.basis, eval_prod, prod_eq_zero_iff]
  exact ⟨j, ⟨mem_erase.mpr ⟨hij.symm, hj⟩, eval_basisDivisor_right⟩⟩

@[simp]

Depends on / 依赖: Lagrange, Lagrange.basis, eval_basisDivisor_right, eval_prod, hij.symm, mem_erase, mem_erase.mpr, prod_eq_zero_iff, simp_rw
-/
theorem eval_basis_of_ne (hij : i != j) (hj : j in s) : (Lagrange.basis s v i).eval (v j) = 0 := by
  simp_rw [Lagrange.basis, eval_prod, prod_eq_zero_iff]
  exact ⟨j, ⟨mem_erase.mpr ⟨hij.symm, hj⟩, eval_basisDivisor_right⟩⟩

@[simp]
/--
theorem `natDegree_basis` / 定理 `natDegree_basis`

English:
theorem natDegree_basis
  given: (hvs : Set.InjOn v s) (hi : i in s)
  proof: by
  have H : forall j, j in s.erase i -> basisDivisor (v i) (v j) != 0 := by
    simp_rw [Ne, mem_erase, basisDivisor_eq_zero_iff]
    exact fun j ⟨hij₁, hj⟩ hij₂ => hij₁ (hvs hj hi hij₂.symm)
  rw [← card_erase_of_mem hi]; rw [card_eq_sum_ones]
  convert! natDegree_prod _ _ H using 1
  refine sum_congr rfl fun j hj => (natDegree_basisDivisor_of_ne ?_).symm
  rw [Ne]; rw [← basisDivisor_eq_zero_iff]
  exact H _ hj

中文:
定理 natDegree_basis
  条件: (hvs : 集合.单射限制 v s) (hi : i in s)
  证明: by
  have H : forall j, j in s.erase i -> basisDivisor (v i) (v j) != 0 := by
    simp_rw [Ne, mem_erase, basisDivisor_eq_zero_iff]
    exact fun j ⟨hij₁, hj⟩ hij₂ => hij₁ (hvs hj hi hij₂.symm)
  rw [← card_erase_of_mem hi]; rw [card_eq_sum_ones]
  convert! natDegree_prod _ _ H using 1
  refine sum_congr rfl fun j hj => (natDegree_basisDivisor_of_ne ?_).symm
  rw [Ne]; rw [← basisDivisor_eq_zero_iff]
  exact H _ hj

Depends on / 依赖: basisDivisor, basisDivisor_eq_zero_iff, card_eq_sum_ones, card_erase_of_mem, convert, mem_erase, natDegree_basisDivisor_of_ne, natDegree_prod, s.erase, simp_rw, sum_congr
-/
theorem natDegree_basis (hvs : Set.InjOn v s) (hi : i in s) :
    (Lagrange.basis s v i).natDegree = #s - 1 := by
  have H : forall j, j in s.erase i -> basisDivisor (v i) (v j) != 0 := by
    simp_rw [Ne, mem_erase, basisDivisor_eq_zero_iff]
    exact fun j ⟨hij₁, hj⟩ hij₂ => hij₁ (hvs hj hi hij₂.symm)
  rw [← card_erase_of_mem hi]; rw [card_eq_sum_ones]
  convert! natDegree_prod _ _ H using 1
  refine sum_congr rfl fun j hj => (natDegree_basisDivisor_of_ne ?_).symm
  rw [Ne]; rw [← basisDivisor_eq_zero_iff]
  exact H _ hj

/--
theorem `degree_basis` / 定理 `degree_basis`

English:
theorem degree_basis
  given: (hvs : Set.InjOn v s) (hi : i in s)
  proof: by
  rw [degree_eq_natDegree (basis_ne_zero hvs hi)]; rw [natDegree_basis hvs hi]

中文:
定理 degree_basis
  条件: (hvs : 集合.单射限制 v s) (hi : i in s)
  证明: by
  rw [degree_eq_natDegree (basis_ne_zero hvs hi)]; rw [natDegree_basis hvs hi]

Depends on / 依赖: basis_ne_zero, degree_eq_natDegree, natDegree_basis
-/
theorem degree_basis (hvs : Set.InjOn v s) (hi : i in s) :
    (Lagrange.basis s v i).degree = ↑(#s - 1) := by
  rw [degree_eq_natDegree (basis_ne_zero hvs hi)]; rw [natDegree_basis hvs hi]

/--
theorem `sum_basis` / 定理 `sum_basis`

English:
theorem sum_basis
  given: (hvs : Set.InjOn v s) (hs : s.Nonempty)
  proof: by
  refine eq_of_degrees_lt_of_eval_index_eq s hvs (lt_of_le_of_lt (degree_sum_le _ _) ?_) ?_ ?_
  · rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #s)]
    intro i hi
    rw [degree_basis hvs hi]; rw [Nat.cast_withBot]; rw [WithBot.coe_lt_coe]
    exact Nat.pred_lt (card_ne_zero_of_mem hi)
  · rw [degree_one, ← WithBot.coe_zero, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nonempty.card_pos hs
  · intro i hi
    rw [eval_finsetSum]; rw [eval_one]; rw [← add_sum_erase _ _ hi]; rw [eval_basis_self hvs hi]; rw [add_eq_left]
    refine sum_eq_zero fun j hj => ?_
    rcases mem_erase.mp hj with ⟨hij, _⟩
    rw [eval_basis_of_ne hij hi]

中文:
定理 sum_basis
  条件: (hvs : 集合.单射限制 v s) (hs : s.非空)
  证明: by
  refine eq_of_degrees_lt_of_eval_index_eq s hvs (lt_of_le_of_lt (degree_sum_le _ _) ?_) ?_ ?_
  · rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #s)]
    intro i hi
    rw [degree_basis hvs hi]; rw [Nat.cast_withBot]; rw [WithBot.coe_lt_coe]
    exact Nat.pred_lt (card_ne_zero_of_mem hi)
  · rw [degree_one, ← WithBot.coe_zero, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nonempty.card_pos hs
  · intro i hi
    rw [eval_finsetSum]; rw [eval_one]; rw [← add_sum_erase _ _ hi]; rw [eval_basis_self hvs hi]; rw [add_eq_left]
    refine sum_eq_zero fun j hj => ?_
    rcases mem_erase.mp hj with ⟨hij, _⟩
    rw [eval_basis_of_ne hij hi]

Depends on / 依赖: Finset, Finset.sup_lt_iff, Nat.cast_withBot, Nat.pred_lt, Nonempty, Nonempty.card_pos, WithBot, WithBot.bot_lt_coe, WithBot.coe_lt_coe, WithBot.coe_zero, add_sum_erase, bot_lt_coe, card_ne_zero_of_mem, card_pos, cast_withBot, coe_lt_coe, coe_zero, degree_basis, degree_one, degree_sum_le
-/
theorem sum_basis (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    ∑ j in s, Lagrange.basis s v j = 1 := by
  refine eq_of_degrees_lt_of_eval_index_eq s hvs (lt_of_le_of_lt (degree_sum_le _ _) ?_) ?_ ?_
  · rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #s)]
    intro i hi
    rw [degree_basis hvs hi]; rw [Nat.cast_withBot]; rw [WithBot.coe_lt_coe]
    exact Nat.pred_lt (card_ne_zero_of_mem hi)
  · rw [degree_one, ← WithBot.coe_zero, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nonempty.card_pos hs
  · intro i hi
    rw [eval_finsetSum]; rw [eval_one]; rw [← add_sum_erase _ _ hi]; rw [eval_basis_self hvs hi]; rw [add_eq_left]
    refine sum_eq_zero fun j hj => ?_
    rcases mem_erase.mp hj with ⟨hij, _⟩
    rw [eval_basis_of_ne hij hi]

/--
theorem `basisDivisor_add_symm` / 定理 `basisDivisor_add_symm`

English:
theorem basisDivisor_add_symm
  given: {x y : F} (hxy : x != y)
  proof: by
  classical
  rw [← sum_basis Function.injective_id.injOn ⟨x]; rw [mem_insert_self _ {y}⟩]; rw [sum_insert (notMem_singleton.mpr hxy)]; rw [sum_singleton]; rw [basis_pair_left hxy]; rw [basis_pair_right hxy]; rw [id]; rw [id]

中文:
定理 basisDivisor_add_symm
  条件: {x y : F} (hxy : x != y)
  证明: by
  classical
  rw [← sum_basis Function.injective_id.injOn ⟨x]; rw [mem_insert_self _ {y}⟩]; rw [sum_insert (notMem_singleton.mpr hxy)]; rw [sum_singleton]; rw [basis_pair_left hxy]; rw [basis_pair_right hxy]; rw [id]; rw [id]

Depends on / 依赖: Function, Function.injective_id.injOn, basis_pair_left, basis_pair_right, classical, injective_id, mem_insert_self, notMem_singleton, notMem_singleton.mpr, sum_basis, sum_insert, sum_singleton
-/
theorem basisDivisor_add_symm {x y : F} (hxy : x != y) :
    basisDivisor x y + basisDivisor y x = 1 := by
  classical
  rw [← sum_basis Function.injective_id.injOn ⟨x]; rw [mem_insert_self _ {y}⟩]; rw [sum_insert (notMem_singleton.mpr hxy)]; rw [sum_singleton]; rw [basis_pair_left hxy]; rw [basis_pair_right hxy]; rw [id]; rw [id]

/--
theorem `leadingCoeff_basis` / 定理 `leadingCoeff_basis`

English:
theorem leadingCoeff_basis
  given: (hvs : Set.InjOn v s) (hi : i in s)
  proof: by
  have : (∏ j in s.erase i, (X - C (v j))).coeff (#s - 1) = 1 := by
    simpa [hi] using (monic_prod_X_sub_C v (s.erase i)).coeff_natDegree
  simp_rw [leadingCoeff, natDegree_basis hvs hi, Lagrange.basis]
  simp [basisDivisor, Finset.prod_mul_distrib, ← map_prod, this]

中文:
定理 leadingCoeff_basis
  条件: (hvs : 集合.单射限制 v s) (hi : i in s)
  证明: by
  have : (∏ j in s.erase i, (X - C (v j))).coeff (#s - 1) = 1 := by
    simpa [hi] using (monic_prod_X_sub_C v (s.erase i)).coeff_natDegree
  simp_rw [leadingCoeff, natDegree_basis hvs hi, Lagrange.basis]
  simp [basisDivisor, Finset.prod_mul_distrib, ← map_prod, this]

Depends on / 依赖: Finset, Finset.prod_mul_distrib, Lagrange, Lagrange.basis, basisDivisor, coeff_natDegree, leadingCoeff, map_prod, monic_prod_X_sub_C, natDegree_basis, prod_mul_distrib, s.erase, simp_rw
-/
theorem leadingCoeff_basis (hvs : Set.InjOn v s) (hi : i in s) :
    (Lagrange.basis s v i).leadingCoeff = (∏ j in s.erase i, ((v i) - (v j)))⁻¹ := by
  have : (∏ j in s.erase i, (X - C (v j))).coeff (#s - 1) = 1 := by
    simpa [hi] using (monic_prod_X_sub_C v (s.erase i)).coeff_natDegree
  simp_rw [leadingCoeff, natDegree_basis hvs hi, Lagrange.basis]
  simp [basisDivisor, Finset.prod_mul_distrib, ← map_prod, this]

end Basis

section Interpolate

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s t : Finset ι} {i j : ι} {v : ι -> F} (r r' : ι -> F)

open Finset

/-- Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `v : ι → F` injective on
`s` and a value function `r : ι → F`, `interpolate s v r` is the unique
polynomial of degree `< #s` that takes value `r i` on `v i` for all `i` in `s`. -/
@[simps]
/--
Definition of `interpolate` / `interpolate` 的定义

English:
definition interpolate
  signature: (s : Finset ι) (v : ι -> F)
  body: ∑ i in s, C (r i) * Lagrange.basis s v i
  map_add' f g := by
    simp_rw [← Finset.sum_add_distrib]
    have h : (fun x => C (f x) * Lagrange.basis s v x + C (g x) * Lagrange.basis s v x) =
    (fun x => C ((f + g) x) * Lagrange.basis s v x) := by
      simp_rw [← add_mul, ← C_add, Pi.add_apply]
    rw [h]
  map_smul' c f := by
    simp_rw [Finset.smul_sum, C_mul', smul_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]

中文:
定义 interpolate
  签名: (s : 有限集 ι) (v : ι -> F)
  定义体: ∑ i in s, C (r i) * Lagrange.basis s v i
  map_add' f g := by
    simp_rw [← Finset.sum_add_distrib]
    have h : (fun x => C (f x) * Lagrange.basis s v x + C (g x) * Lagrange.basis s v x) =
    (fun x => C ((f + g) x) * Lagrange.basis s v x) := by
      simp_rw [← add_mul, ← C_add, Pi.add_apply]
    rw [h]
  map_smul' c f := by
    simp_rw [Finset.smul_sum, C_mul', smul_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]

Depends on / 依赖: Lagrange, Lagrange.basis
-/
def interpolate (s : Finset ι) (v : ι -> F) : (ι -> F) ->ₗ[F] F[X] where
  toFun r := ∑ i in s, C (r i) * Lagrange.basis s v i
  map_add' f g := by
    simp_rw [← Finset.sum_add_distrib]
    have h : (fun x => C (f x) * Lagrange.basis s v x + C (g x) * Lagrange.basis s v x) =
    (fun x => C ((f + g) x) * Lagrange.basis s v x) := by
      simp_rw [← add_mul, ← C_add, Pi.add_apply]
    rw [h]
  map_smul' c f := by
    simp_rw [Finset.smul_sum, C_mul', smul_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]

/--
theorem `interpolate_empty` / 定理 `interpolate_empty`

English:
theorem interpolate_empty
  statement: interpolate ∅ v r = 0
  proof: by rw [interpolate_apply, sum_empty]

中文:
定理 interpolate_empty
  结论: interpolate ∅ v r = 0
  证明: by rw [interpolate_apply, sum_empty]

Depends on / 依赖: interpolate_apply, sum_empty
-/
theorem interpolate_empty : interpolate ∅ v r = 0 := by rw [interpolate_apply, sum_empty]

/--
theorem `interpolate_singleton` / 定理 `interpolate_singleton`

English:
theorem interpolate_singleton
  statement: interpolate {i} v r = C (r i)
  proof: by
  rw [interpolate_apply]; rw [sum_singleton]; rw [basis_singleton]; rw [mul_one]

中文:
定理 interpolate_singleton
  结论: interpolate {i} v r = C (r i)
  证明: by
  rw [interpolate_apply]; rw [sum_singleton]; rw [basis_singleton]; rw [mul_one]

Depends on / 依赖: basis_singleton, interpolate_apply, mul_one, sum_singleton
-/
theorem interpolate_singleton : interpolate {i} v r = C (r i) := by
  rw [interpolate_apply]; rw [sum_singleton]; rw [basis_singleton]; rw [mul_one]

/--
theorem `interpolate_one` / 定理 `interpolate_one`

English:
theorem interpolate_one
  given: (hvs : Set.InjOn v s) (hs : s.Nonempty)
  statement: interpolate s v 1 = 1
  proof: by
  simp_rw [interpolate_apply, Pi.one_apply, map_one, one_mul]
  exact sum_basis hvs hs

中文:
定理 interpolate_one
  条件: (hvs : 集合.单射限制 v s) (hs : s.非空)
  结论: interpolate s v 1 = 1
  证明: by
  simp_rw [interpolate_apply, Pi.one_apply, map_one, one_mul]
  exact sum_basis hvs hs

Depends on / 依赖: Pi.one_apply, interpolate_apply, map_one, one_apply, one_mul, simp_rw, sum_basis
-/
theorem interpolate_one (hvs : Set.InjOn v s) (hs : s.Nonempty) : interpolate s v 1 = 1 := by
  simp_rw [interpolate_apply, Pi.one_apply, map_one, one_mul]
  exact sum_basis hvs hs

/--
theorem `eval_interpolate_at_node` / 定理 `eval_interpolate_at_node`

English:
theorem eval_interpolate_at_node
  given: (hvs : Set.InjOn v s) (hi : i in s)
  proof: by
  rw [interpolate_apply]; rw [eval_finsetSum]; rw [← add_sum_erase _ _ hi]
  simp_rw [eval_mul, eval_C, eval_basis_self hvs hi, mul_one, add_eq_left]
  refine sum_eq_zero fun j H => ?_
  rw [eval_basis_of_ne (mem_erase.mp H).1 hi]; rw [mul_zero]

中文:
定理 eval_interpolate_at_node
  条件: (hvs : 集合.单射限制 v s) (hi : i in s)
  证明: by
  rw [interpolate_apply]; rw [eval_finsetSum]; rw [← add_sum_erase _ _ hi]
  simp_rw [eval_mul, eval_C, eval_basis_self hvs hi, mul_one, add_eq_left]
  refine sum_eq_zero fun j H => ?_
  rw [eval_basis_of_ne (mem_erase.mp H).1 hi]; rw [mul_zero]

Depends on / 依赖: add_eq_left, add_sum_erase, eval_C, eval_basis_of_ne, eval_basis_self, eval_finsetSum, eval_mul, interpolate_apply, mem_erase, mem_erase.mp, mul_one, mul_zero, simp_rw, sum_eq_zero
-/
theorem eval_interpolate_at_node (hvs : Set.InjOn v s) (hi : i in s) :
    eval (v i) (interpolate s v r) = r i := by
  rw [interpolate_apply]; rw [eval_finsetSum]; rw [← add_sum_erase _ _ hi]
  simp_rw [eval_mul, eval_C, eval_basis_self hvs hi, mul_one, add_eq_left]
  refine sum_eq_zero fun j H => ?_
  rw [eval_basis_of_ne (mem_erase.mp H).1 hi]; rw [mul_zero]

/--
theorem `degree_interpolate_le` / 定理 `degree_interpolate_le`

English:
theorem degree_interpolate_le
  given: (hvs : Set.InjOn v s)
  proof: by
  refine (degree_sum_le _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro i hi
  rw [degree_mul]; rw [degree_basis hvs hi]
  by_cases hr : r i = 0
  · simpa only [hr, map_zero, degree_zero, WithBot.bot_add] using bot_le
  · rw [degree_C hr, zero_add]

中文:
定理 degree_interpolate_le
  条件: (hvs : 集合.单射限制 v s)
  证明: by
  refine (degree_sum_le _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro i hi
  rw [degree_mul]; rw [degree_basis hvs hi]
  by_cases hr : r i = 0
  · simpa only [hr, map_zero, degree_zero, WithBot.bot_add] using bot_le
  · rw [degree_C hr, zero_add]

Depends on / 依赖: Finset, Finset.sup_le_iff, WithBot, WithBot.bot_add, bot_add, bot_le, degree_C, degree_basis, degree_mul, degree_sum_le, degree_zero, map_zero, sup_le_iff, zero_add
-/
theorem degree_interpolate_le (hvs : Set.InjOn v s) :
    (interpolate s v r).degree <= ↑(#s - 1) := by
  refine (degree_sum_le _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro i hi
  rw [degree_mul]; rw [degree_basis hvs hi]
  by_cases hr : r i = 0
  · simpa only [hr, map_zero, degree_zero, WithBot.bot_add] using bot_le
  · rw [degree_C hr, zero_add]

/--
theorem `degree_interpolate_lt` / 定理 `degree_interpolate_lt`

English:
theorem degree_interpolate_lt
  given: (hvs : Set.InjOn v s)
  statement: (interpolate s v r).degree < #s
  proof: by
  rw [Nat.cast_withBot]
  rcases eq_empty_or_nonempty s with (rfl | h)
  · rw [interpolate_empty, degree_zero, card_empty]
    exact WithBot.bot_lt_coe _
  · refine lt_of_le_of_lt (degree_interpolate_le _ hvs) ?_
    rw [Nat.cast_withBot]; rw [WithBot.coe_lt_coe]
    exact Nat.sub_lt (Nonempty.card_pos h) zero_lt_one

中文:
定理 degree_interpolate_lt
  条件: (hvs : 集合.单射限制 v s)
  结论: (interpolate s v r).degree < #s
  证明: by
  rw [Nat.cast_withBot]
  rcases eq_empty_or_nonempty s with (rfl | h)
  · rw [interpolate_empty, degree_zero, card_empty]
    exact WithBot.bot_lt_coe _
  · refine lt_of_le_of_lt (degree_interpolate_le _ hvs) ?_
    rw [Nat.cast_withBot]; rw [WithBot.coe_lt_coe]
    exact Nat.sub_lt (Nonempty.card_pos h) zero_lt_one

Depends on / 依赖: Nat.cast_withBot, Nat.sub_lt, Nonempty, Nonempty.card_pos, WithBot, WithBot.bot_lt_coe, WithBot.coe_lt_coe, bot_lt_coe, card_empty, card_pos, cast_withBot, coe_lt_coe, degree_interpolate_le, degree_zero, eq_empty_or_nonempty, interpolate_empty, lt_of_le_of_lt, sub_lt, zero_lt_one
-/
theorem degree_interpolate_lt (hvs : Set.InjOn v s) : (interpolate s v r).degree < #s := by
  rw [Nat.cast_withBot]
  rcases eq_empty_or_nonempty s with (rfl | h)
  · rw [interpolate_empty, degree_zero, card_empty]
    exact WithBot.bot_lt_coe _
  · refine lt_of_le_of_lt (degree_interpolate_le _ hvs) ?_
    rw [Nat.cast_withBot]; rw [WithBot.coe_lt_coe]
    exact Nat.sub_lt (Nonempty.card_pos h) zero_lt_one

/--
theorem `degree_interpolate_erase_lt` / 定理 `degree_interpolate_erase_lt`

English:
theorem degree_interpolate_erase_lt
  given: (hvs : Set.InjOn v s) (hi : i in s)
  proof: by
  rw [← Finset.card_erase_of_mem hi]
  exact degree_interpolate_lt _ (Set.InjOn.mono (coe_subset.mpr (erase_subset _ _)) hvs)

中文:
定理 degree_interpolate_erase_lt
  条件: (hvs : 集合.单射限制 v s) (hi : i in s)
  证明: by
  rw [← Finset.card_erase_of_mem hi]
  exact degree_interpolate_lt _ (Set.InjOn.mono (coe_subset.mpr (erase_subset _ _)) hvs)

Depends on / 依赖: Finset, Finset.card_erase_of_mem, Set.InjOn.mono, card_erase_of_mem, coe_subset, coe_subset.mpr, degree_interpolate_lt, erase_subset
-/
theorem degree_interpolate_erase_lt (hvs : Set.InjOn v s) (hi : i in s) :
    (interpolate (s.erase i) v r).degree < ↑(#s - 1) := by
  rw [← Finset.card_erase_of_mem hi]
  exact degree_interpolate_lt _ (Set.InjOn.mono (coe_subset.mpr (erase_subset _ _)) hvs)

/--
theorem `values_eq_on_of_interpolate_eq` / 定理 `values_eq_on_of_interpolate_eq`

English:
theorem values_eq_on_of_interpolate_eq
  statement: (hvs : Set.InjOn v s)
  proof: fun _ hi => by
  rw [← eval_interpolate_at_node r hvs hi]; rw [hrr']; rw [eval_interpolate_at_node r' hvs hi]

中文:
定理 values_eq_on_of_interpolate_eq
  结论: (hvs : 集合.单射限制 v s)
  证明: fun _ hi => by
  rw [← eval_interpolate_at_node r hvs hi]; rw [hrr']; rw [eval_interpolate_at_node r' hvs hi]

Depends on / 依赖: eval_interpolate_at_node
-/
theorem values_eq_on_of_interpolate_eq (hvs : Set.InjOn v s)
    (hrr' : interpolate s v r = interpolate s v r') : forall i in s, r i = r' i := fun _ hi => by
  rw [← eval_interpolate_at_node r hvs hi]; rw [hrr']; rw [eval_interpolate_at_node r' hvs hi]

/--
theorem `interpolate_eq_of_values_eq_on` / 定理 `interpolate_eq_of_values_eq_on`

English:
theorem interpolate_eq_of_values_eq_on
  given: (hrr' : forall i in s, r i = r' i)
  proof: sum_congr rfl fun i hi => by rw [hrr' _ hi]

中文:
定理 interpolate_eq_of_values_eq_on
  条件: (hrr' : 对任意 i in s, r i = r' i)
  证明: sum_congr rfl fun i hi => by rw [hrr' _ hi]

Depends on / 依赖: sum_congr
-/
theorem interpolate_eq_of_values_eq_on (hrr' : forall i in s, r i = r' i) :
    interpolate s v r = interpolate s v r' :=
  sum_congr rfl fun i hi => by rw [hrr' _ hi]

/--
theorem `interpolate_eq_iff_values_eq_on` / 定理 `interpolate_eq_iff_values_eq_on`

English:
theorem interpolate_eq_iff_values_eq_on
  given: (hvs : Set.InjOn v s)
  proof: ⟨values_eq_on_of_interpolate_eq _ _ hvs, interpolate_eq_of_values_eq_on _ _⟩

中文:
定理 interpolate_eq_iff_values_eq_on
  条件: (hvs : 集合.单射限制 v s)
  证明: ⟨values_eq_on_of_interpolate_eq _ _ hvs, interpolate_eq_of_values_eq_on _ _⟩

Depends on / 依赖: interpolate_eq_of_values_eq_on, values_eq_on_of_interpolate_eq
-/
theorem interpolate_eq_iff_values_eq_on (hvs : Set.InjOn v s) :
    interpolate s v r = interpolate s v r' ↔ forall i in s, r i = r' i :=
  ⟨values_eq_on_of_interpolate_eq _ _ hvs, interpolate_eq_of_values_eq_on _ _⟩

/--
theorem `eq_interpolate` / 定理 `eq_interpolate`

English:
theorem eq_interpolate
  given: {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
  proof: eq_of_degrees_lt_of_eval_index_eq _ hvs degree_f_lt (degree_interpolate_lt _ hvs) fun _ hi =>
    (eval_interpolate_at_node (fun x => eval (v x) f) hvs hi).symm

中文:
定理 eq_interpolate
  条件: {f : F[X]} (hvs : 集合.单射限制 v s) (degree_f_lt : f.degree < #s)
  证明: eq_of_degrees_lt_of_eval_index_eq _ hvs degree_f_lt (degree_interpolate_lt _ hvs) fun _ hi =>
    (eval_interpolate_at_node (fun x => eval (v x) f) hvs hi).symm

Depends on / 依赖: degree_f_lt, degree_interpolate_lt, eq_of_degrees_lt_of_eval_index_eq, eval_interpolate_at_node
-/
theorem eq_interpolate {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s) :
    f = interpolate s v fun i => f.eval (v i) :=
  eq_of_degrees_lt_of_eval_index_eq _ hvs degree_f_lt (degree_interpolate_lt _ hvs) fun _ hi =>
    (eval_interpolate_at_node (fun x => eval (v x) f) hvs hi).symm

/--
theorem `eq_interpolate_of_eval_eq` / 定理 `eq_interpolate_of_eval_eq`

English:
theorem eq_interpolate_of_eval_eq
  statement: {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
  proof: by
  rw [eq_interpolate hvs degree_f_lt]
  exact interpolate_eq_of_values_eq_on _ _ eval_f

中文:
定理 eq_interpolate_of_eval_eq
  结论: {f : F[X]} (hvs : 集合.单射限制 v s) (degree_f_lt : f.degree < #s)
  证明: by
  rw [eq_interpolate hvs degree_f_lt]
  exact interpolate_eq_of_values_eq_on _ _ eval_f

Depends on / 依赖: degree_f_lt, eq_interpolate, eval_f, interpolate_eq_of_values_eq_on
-/
theorem eq_interpolate_of_eval_eq {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
    (eval_f : forall i in s, f.eval (v i) = r i) : f = interpolate s v r := by
  rw [eq_interpolate hvs degree_f_lt]
  exact interpolate_eq_of_values_eq_on _ _ eval_f

/--
theorem `eq_interpolate_iff` / 定理 `eq_interpolate_iff`

English:
theorem eq_interpolate_iff
  given: {f : F[X]} (hvs : Set.InjOn v s)
  proof: by
  constructor <;> intro h
  · exact eq_interpolate_of_eval_eq _ hvs h.1 h.2
  · rw [h]
    exact ⟨degree_interpolate_lt _ hvs, fun _ hi => eval_interpolate_at_node _ hvs hi⟩

中文:
定理 eq_interpolate_iff
  条件: {f : F[X]} (hvs : 集合.单射限制 v s)
  证明: by
  constructor <;> intro h
  · exact eq_interpolate_of_eval_eq _ hvs h.1 h.2
  · rw [h]
    exact ⟨degree_interpolate_lt _ hvs, fun _ hi => eval_interpolate_at_node _ hvs hi⟩

Depends on / 依赖: degree_interpolate_lt, eq_interpolate_of_eval_eq, eval_interpolate_at_node
-/
theorem eq_interpolate_iff {f : F[X]} (hvs : Set.InjOn v s) :
    (f.degree < #s ∧ forall i in s, eval (v i) f = r i) ↔ f = interpolate s v r := by
  constructor <;> intro h
  · exact eq_interpolate_of_eval_eq _ hvs h.1 h.2
  · rw [h]
    exact ⟨degree_interpolate_lt _ hvs, fun _ hi => eval_interpolate_at_node _ hvs hi⟩

/--
Definition of `funEquivDegreeLT` / `funEquivDegreeLT` 的定义

English:
definition funEquivDegreeLT
  signature: (hvs : Set.InjOn v s)
  body: f.1.eval (v i)
  map_add' _ _ := funext fun _ => eval_add
map_smul' c f := funext by simp
  invFun r :=
    ⟨interpolate s v fun x => if hx : x in s then r ⟨x, hx⟩ else 0,
mem_degreeLT.2 degree_interpolate_lt _ hvs⟩
  left_inv := by
    rintro ⟨f, hf⟩
    simp only [Subtype.mk_eq_mk, dite_eq_ite]
    rw [mem_degreeLT] at hf
    conv => rhs; rw [eq_interpolate hvs hf]
    exact interpolate_eq_of_values_eq_on _ _ fun _ hi => if_pos hi
  right_inv := by
    intro f
    ext ⟨i, hi⟩
    simp only [eval_interpolate_at_node _ hvs hi]
    exact dif_pos hi

中文:
定义 funEquivDegreeLT
  签名: (hvs : 集合.单射限制 v s)
  定义体: f.1.eval (v i)
  map_add' _ _ := funext fun _ => eval_add
map_smul' c f := funext by simp
  invFun r :=
    ⟨interpolate s v fun x => if hx : x in s then r ⟨x, hx⟩ else 0,
mem_degreeLT.2 degree_interpolate_lt _ hvs⟩
  left_inv := by
    rintro ⟨f, hf⟩
    simp only [Subtype.mk_eq_mk, dite_eq_ite]
    rw [mem_degreeLT] at hf
    conv => rhs; rw [eq_interpolate hvs hf]
    exact interpolate_eq_of_values_eq_on _ _ fun _ hi => if_pos hi
  right_inv := by
    intro f
    ext ⟨i, hi⟩
    simp only [eval_interpolate_at_node _ hvs hi]
    exact dif_pos hi
-/
def funEquivDegreeLT (hvs : Set.InjOn v s) : degreeLT F #s ≃ₗ[F] s -> F where
  toFun f i := f.1.eval (v i)
  map_add' _ _ := funext fun _ => eval_add
map_smul' c f := funext by simp
  invFun r :=
    ⟨interpolate s v fun x => if hx : x in s then r ⟨x, hx⟩ else 0,
mem_degreeLT.2 degree_interpolate_lt _ hvs⟩
  left_inv := by
    rintro ⟨f, hf⟩
    simp only [Subtype.mk_eq_mk, dite_eq_ite]
    rw [mem_degreeLT] at hf
    conv => rhs; rw [eq_interpolate hvs hf]
    exact interpolate_eq_of_values_eq_on _ _ fun _ hi => if_pos hi
  right_inv := by
    intro f
    ext ⟨i, hi⟩
    simp only [eval_interpolate_at_node _ hvs hi]
    exact dif_pos hi

/--
theorem `interpolate_eq_sum_interpolate_insert_sdiff` / 定理 `interpolate_eq_sum_interpolate_insert_sdiff`

English:
theorem interpolate_eq_sum_interpolate_insert_sdiff
  statement: (hvt : Set.InjOn v t) (hs : s.Nonempty)
  proof: by
  symm
  refine eq_interpolate_of_eval_eq _ hvt (lt_of_le_of_lt (degree_sum_le _ _) ?_) fun i hi => ?_
  · simp_rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #t), degree_mul]
    intro i hi
    have hs : 1 <= #s := Nonempty.card_pos ⟨_, hi⟩
    have hst' : #s <= #t := card_le_card hst
    have H : #t = 1 + (#t - #s) + (#s - 1) := by
      rw [add_assoc]; rw [tsub_add_tsub_cancel hst' hs]; rw [← add_tsub_assoc_of_le (hs.trans hst')]; rw [Nat.succ_add_sub_one]; rw [zero_add]
    rw [degree_basis (Set.InjOn.mono hst hvt) hi]; rw [H]; rw [WithBot.coe_add]; rw [Nat.cast_withBot]; rw [WithBot.add_lt_add_iff_right (@WithBot.coe_ne_bot _ (#s - 1))]
    convert!
      degree_interpolate_lt _
        (hvt.mono (coe_subset.mpr (insert_subset_iff.mpr ⟨hst hi, sdiff_subset⟩)))
    rw [card_insert_of_notMem (notMem_sdiff_of_mem_right hi)]; rw [card_sdiff_of_subset hst]; rw [add_comm]
  · simp_rw [eval_finsetSum, eval_mul]
    by_cases hi' : i in s
    · rw [← add_sum_erase _ _ hi', eval_basis_self (hvt.mono hst) hi',
        eval_interpolate_at_node _
          (hvt.mono (coe_subset.mpr (insert_subset_iff.mpr ⟨hi, sdiff_subset⟩)))
          (mem_insert_self _ _),
        mul_one, add_eq_left]
      refine sum_eq_zero fun j hj => ?_
      rcases mem_erase.mp hj with ⟨hij, _⟩
      rw [eval_basis_of_ne hij hi']; rw [mul_zero]
    · have H : (∑ j in s, eval (v i) (Lagrange.basis s v j)) = 1 := by
        rw [← eval_finsetSum]; rw [sum_basis (hvt.mono hst) hs]; rw [eval_one]
      rw [← mul_one (r i)]; rw [← H]; rw [mul_sum]
      refine sum_congr rfl fun j hj => ?_
      congr
      exact
        eval_interpolate_at_node _ (hvt.mono (insert_subset_iff.mpr ⟨hst hj, sdiff_subset⟩))
          (mem_insert.mpr (Or.inr (mem_sdiff.mpr ⟨hi, hi'⟩)))

中文:
定理 interpolate_eq_sum_interpolate_insert_sdiff
  结论: (hvt : 集合.单射限制 v t) (hs : s.非空)
  证明: by
  symm
  refine eq_interpolate_of_eval_eq _ hvt (lt_of_le_of_lt (degree_sum_le _ _) ?_) fun i hi => ?_
  · simp_rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #t), degree_mul]
    intro i hi
    have hs : 1 <= #s := Nonempty.card_pos ⟨_, hi⟩
    have hst' : #s <= #t := card_le_card hst
    have H : #t = 1 + (#t - #s) + (#s - 1) := by
      rw [add_assoc]; rw [tsub_add_tsub_cancel hst' hs]; rw [← add_tsub_assoc_of_le (hs.trans hst')]; rw [Nat.succ_add_sub_one]; rw [zero_add]
    rw [degree_basis (Set.InjOn.mono hst hvt) hi]; rw [H]; rw [WithBot.coe_add]; rw [Nat.cast_withBot]; rw [WithBot.add_lt_add_iff_right (@WithBot.coe_ne_bot _ (#s - 1))]
    convert!
      degree_interpolate_lt _
        (hvt.mono (coe_subset.mpr (insert_subset_iff.mpr ⟨hst hi, sdiff_subset⟩)))
    rw [card_insert_of_notMem (notMem_sdiff_of_mem_right hi)]; rw [card_sdiff_of_subset hst]; rw [add_comm]
  · simp_rw [eval_finsetSum, eval_mul]
    by_cases hi' : i in s
    · rw [← add_sum_erase _ _ hi', eval_basis_self (hvt.mono hst) hi',
        eval_interpolate_at_node _
          (hvt.mono (coe_subset.mpr (insert_subset_iff.mpr ⟨hi, sdiff_subset⟩)))
          (mem_insert_self _ _),
        mul_one, add_eq_left]
      refine sum_eq_zero fun j hj => ?_
      rcases mem_erase.mp hj with ⟨hij, _⟩
      rw [eval_basis_of_ne hij hi']; rw [mul_zero]
    · have H : (∑ j in s, eval (v i) (Lagrange.basis s v j)) = 1 := by
        rw [← eval_finsetSum]; rw [sum_basis (hvt.mono hst) hs]; rw [eval_one]
      rw [← mul_one (r i)]; rw [← H]; rw [mul_sum]
      refine sum_congr rfl fun j hj => ?_
      congr
      exact
        eval_interpolate_at_node _ (hvt.mono (insert_subset_iff.mpr ⟨hst hj, sdiff_subset⟩))
          (mem_insert.mpr (Or.inr (mem_sdiff.mpr ⟨hi, hi'⟩)))

Depends on / 依赖: Finset, Finset.sup_lt_iff, Nat.cast_withBot, Nat.succ_add_sub_one, Nonempty, Nonempty.card_pos, Set.InjOn.mono, WithBot, WithBot.bot_lt_coe, add_assoc, add_tsub_assoc_of_le, bot_lt_coe, card_le_card, card_pos, cast_withBot, degree_basis, degree_mul, degree_sum_le, eq_interpolate_of_eval_eq, hs.trans
-/
theorem interpolate_eq_sum_interpolate_insert_sdiff (hvt : Set.InjOn v t) (hs : s.Nonempty)
    (hst : s subseteq t) :
    interpolate t v r = ∑ i in s, interpolate (insert i (t \ s)) v r * Lagrange.basis s v i := by
  symm
  refine eq_interpolate_of_eval_eq _ hvt (lt_of_le_of_lt (degree_sum_le _ _) ?_) fun i hi => ?_
  · simp_rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #t), degree_mul]
    intro i hi
    have hs : 1 <= #s := Nonempty.card_pos ⟨_, hi⟩
    have hst' : #s <= #t := card_le_card hst
    have H : #t = 1 + (#t - #s) + (#s - 1) := by
      rw [add_assoc]; rw [tsub_add_tsub_cancel hst' hs]; rw [← add_tsub_assoc_of_le (hs.trans hst')]; rw [Nat.succ_add_sub_one]; rw [zero_add]
    rw [degree_basis (Set.InjOn.mono hst hvt) hi]; rw [H]; rw [WithBot.coe_add]; rw [Nat.cast_withBot]; rw [WithBot.add_lt_add_iff_right (@WithBot.coe_ne_bot _ (#s - 1))]
    convert!
      degree_interpolate_lt _
        (hvt.mono (coe_subset.mpr (insert_subset_iff.mpr ⟨hst hi, sdiff_subset⟩)))
    rw [card_insert_of_notMem (notMem_sdiff_of_mem_right hi)]; rw [card_sdiff_of_subset hst]; rw [add_comm]
  · simp_rw [eval_finsetSum, eval_mul]
    by_cases hi' : i in s
    · rw [← add_sum_erase _ _ hi', eval_basis_self (hvt.mono hst) hi',
        eval_interpolate_at_node _
          (hvt.mono (coe_subset.mpr (insert_subset_iff.mpr ⟨hi, sdiff_subset⟩)))
          (mem_insert_self _ _),
        mul_one, add_eq_left]
      refine sum_eq_zero fun j hj => ?_
      rcases mem_erase.mp hj with ⟨hij, _⟩
      rw [eval_basis_of_ne hij hi']; rw [mul_zero]
    · have H : (∑ j in s, eval (v i) (Lagrange.basis s v j)) = 1 := by
        rw [← eval_finsetSum]; rw [sum_basis (hvt.mono hst) hs]; rw [eval_one]
      rw [← mul_one (r i)]; rw [← H]; rw [mul_sum]
      refine sum_congr rfl fun j hj => ?_
      congr
      exact
        eval_interpolate_at_node _ (hvt.mono (insert_subset_iff.mpr ⟨hst hj, sdiff_subset⟩))
          (mem_insert.mpr (Or.inr (mem_sdiff.mpr ⟨hi, hi'⟩)))

/--
theorem `interpolate_eq_add_interpolate_erase` / 定理 `interpolate_eq_add_interpolate_erase`

English:
theorem interpolate_eq_add_interpolate_erase
  statement: (hvs : Set.InjOn v s) (hi : i in s) (hj : j in s)
  proof: by
  rw [interpolate_eq_sum_interpolate_insert_sdiff _ hvs ⟨i]; rw [mem_insert_self i {j}⟩ _]; rw [sum_insert (notMem_singleton.mpr hij)]; rw [sum_singleton]; rw [basis_pair_left hij]; rw [basis_pair_right hij]; rw [sdiff_insert_insert_of_mem_of_notMem hi (notMem_singleton.mpr hij)]; rw [sdiff_singleton_eq_erase]; rw [pair_comm]; rw [sdiff_insert_insert_of_mem_of_notMem hj (notMem_singleton.mpr hij.symm)]; rw [sdiff_singleton_eq_erase]
  exact insert_subset_iff.mpr ⟨hi, singleton_subset_iff.mpr hj⟩

中文:
定理 interpolate_eq_add_interpolate_erase
  结论: (hvs : 集合.单射限制 v s) (hi : i in s) (hj : j in s)
  证明: by
  rw [interpolate_eq_sum_interpolate_insert_sdiff _ hvs ⟨i]; rw [mem_insert_self i {j}⟩ _]; rw [sum_insert (notMem_singleton.mpr hij)]; rw [sum_singleton]; rw [basis_pair_left hij]; rw [basis_pair_right hij]; rw [sdiff_insert_insert_of_mem_of_notMem hi (notMem_singleton.mpr hij)]; rw [sdiff_singleton_eq_erase]; rw [pair_comm]; rw [sdiff_insert_insert_of_mem_of_notMem hj (notMem_singleton.mpr hij.symm)]; rw [sdiff_singleton_eq_erase]
  exact insert_subset_iff.mpr ⟨hi, singleton_subset_iff.mpr hj⟩

Depends on / 依赖: basis_pair_left, basis_pair_right, hij.symm, insert_subset_iff, insert_subset_iff.mpr, interpolate_eq_sum_interpolate_insert_sdiff, mem_insert_self, notMem_singleton, notMem_singleton.mpr, pair_comm, sdiff_insert_insert_of_mem_of_notMem, sdiff_singleton_eq_erase, singleton_subset_iff, singleton_subset_iff.mpr, sum_insert, sum_singleton
-/
theorem interpolate_eq_add_interpolate_erase (hvs : Set.InjOn v s) (hi : i in s) (hj : j in s)
    (hij : i != j) :
    interpolate s v r =
      interpolate (s.erase j) v r * basisDivisor (v i) (v j) +
        interpolate (s.erase i) v r * basisDivisor (v j) (v i) := by
  rw [interpolate_eq_sum_interpolate_insert_sdiff _ hvs ⟨i]; rw [mem_insert_self i {j}⟩ _]; rw [sum_insert (notMem_singleton.mpr hij)]; rw [sum_singleton]; rw [basis_pair_left hij]; rw [basis_pair_right hij]; rw [sdiff_insert_insert_of_mem_of_notMem hi (notMem_singleton.mpr hij)]; rw [sdiff_singleton_eq_erase]; rw [pair_comm]; rw [sdiff_insert_insert_of_mem_of_notMem hj (notMem_singleton.mpr hij.symm)]; rw [sdiff_singleton_eq_erase]
  exact insert_subset_iff.mpr ⟨hi, singleton_subset_iff.mpr hj⟩

/--
theorem `interpolate_eq_sum` / 定理 `interpolate_eq_sum`

English:
theorem interpolate_eq_sum
  statement: interpolate s v r =
  proof: by
  simp [Lagrange.basis, basisDivisor, div_eq_mul_inv, prod_mul_distrib, ← map_prod,
    ← prod_inv_distrib, mul_assoc]

中文:
定理 interpolate_eq_sum
  结论: interpolate s v r =
  证明: by
  simp [Lagrange.basis, basisDivisor, div_eq_mul_inv, prod_mul_distrib, ← map_prod,
    ← prod_inv_distrib, mul_assoc]

Depends on / 依赖: Lagrange, Lagrange.basis, basisDivisor, div_eq_mul_inv, map_prod, mul_assoc, prod_inv_distrib, prod_mul_distrib
-/
theorem interpolate_eq_sum : interpolate s v r =
    ∑ i in s, C (r i / ∏ j in s.erase i, (v i - v j)) * (∏ j in s.erase i, (X - C (v j))) := by
  simp [Lagrange.basis, basisDivisor, div_eq_mul_inv, prod_mul_distrib, ← map_prod,
    ← prod_inv_distrib, mul_assoc]

/--
theorem `iterate_derivative_interpolate` / 定理 `iterate_derivative_interpolate`

English:
theorem iterate_derivative_interpolate
  given: (hvs : Set.InjOn v s) {k : Nat} (hk : k < #s)
  proof: by
  classical
  simp_rw [interpolate_eq_sum, iterate_derivative_sum, iterate_derivative_C_mul, mul_sum s,
    ← mul_assoc, mul_comm (k.factorial : F[X]), mul_assoc]
  congr! 2 with i hi
  have hvs' := hvs.mono (coe_subset.mpr (erase_subset i s))
  calc
    derivative^[k] (∏ j in s.erase i, (X - C (v j))) =
    derivative^[k] (∏ vj in (s.erase i).image v, (X - C vj)) := by rw [Finset.prod_image hvs']
    _ = k.factorial * ∑ t in ((s.erase i).image v).powersetCard (#s - (k + 1)),
          ∏ va in t, (X - C va) := by
        grind [iterate_derivative_prod_X_sub_C]
    _ = k.factorial * ∑ t in (s.erase i).powersetCard (#s - (k + 1)), ∏ a in t, (X - C (v a)) := by
        rw [powersetCard_eq_filter]; rw [powerset_image]; rw [eq_comm]
        congrm k.factorial * ?_
        refine sum_nbij (·.image v) (fun a ha => ?hi) ?i_inj (fun t ht => ?i_surj) fun a ha => ?h
        case hi => grind [card_image_of_injOn, hvs'.mono]
        case i_inj => exact (image_injOn_powerset_of_injOn hvs').mono (by grind)
        case i_surj => grind [card_image_of_injOn, hvs'.mono]
case h => exact eq_comm.mp prod_image by grind [hvs'.mono]

中文:
定理 iterate_derivative_interpolate
  条件: (hvs : 集合.单射限制 v s) {k : 自然数} (hk : k < #s)
  证明: by
  classical
  simp_rw [interpolate_eq_sum, iterate_derivative_sum, iterate_derivative_C_mul, mul_sum s,
    ← mul_assoc, mul_comm (k.factorial : F[X]), mul_assoc]
  congr! 2 with i hi
  have hvs' := hvs.mono (coe_subset.mpr (erase_subset i s))
  calc
    derivative^[k] (∏ j in s.erase i, (X - C (v j))) =
    derivative^[k] (∏ vj in (s.erase i).image v, (X - C vj)) := by rw [Finset.prod_image hvs']
    _ = k.factorial * ∑ t in ((s.erase i).image v).powersetCard (#s - (k + 1)),
          ∏ va in t, (X - C va) := by
        grind [iterate_derivative_prod_X_sub_C]
    _ = k.factorial * ∑ t in (s.erase i).powersetCard (#s - (k + 1)), ∏ a in t, (X - C (v a)) := by
        rw [powersetCard_eq_filter]; rw [powerset_image]; rw [eq_comm]
        congrm k.factorial * ?_
        refine sum_nbij (·.image v) (fun a ha => ?hi) ?i_inj (fun t ht => ?i_surj) fun a ha => ?h
        case hi => grind [card_image_of_injOn, hvs'.mono]
        case i_inj => exact (image_injOn_powerset_of_injOn hvs').mono (by grind)
        case i_surj => grind [card_image_of_injOn, hvs'.mono]
case h => exact eq_comm.mp prod_image by grind [hvs'.mono]

Depends on / 依赖: Finset, Finset.prod_image, classical, coe_subset, coe_subset.mpr, derivative, erase_subset, factorial, hvs.mono, interpolate_eq_sum, iterate, iterate_derivative_C_mul, iterate_derivative_sum, k.factorial, mul_assoc, mul_comm, mul_sum, powersetCard, prod_image, s.erase
-/
theorem iterate_derivative_interpolate (hvs : Set.InjOn v s) {k : Nat} (hk : k < #s) :
    derivative^[k] (interpolate s v r) =
      k.factorial * ∑ i in s, C (r i / ∏ j in s.erase i, (v i - v j)) *
        ∑ t in (s.erase i).powersetCard (#s - (k + 1)), ∏ a in t, (X - C (v a)) := by
  classical
  simp_rw [interpolate_eq_sum, iterate_derivative_sum, iterate_derivative_C_mul, mul_sum s,
    ← mul_assoc, mul_comm (k.factorial : F[X]), mul_assoc]
  congr! 2 with i hi
  have hvs' := hvs.mono (coe_subset.mpr (erase_subset i s))
  calc
    derivative^[k] (∏ j in s.erase i, (X - C (v j))) =
    derivative^[k] (∏ vj in (s.erase i).image v, (X - C vj)) := by rw [Finset.prod_image hvs']
    _ = k.factorial * ∑ t in ((s.erase i).image v).powersetCard (#s - (k + 1)),
          ∏ va in t, (X - C va) := by
        grind [iterate_derivative_prod_X_sub_C]
    _ = k.factorial * ∑ t in (s.erase i).powersetCard (#s - (k + 1)), ∏ a in t, (X - C (v a)) := by
        rw [powersetCard_eq_filter]; rw [powerset_image]; rw [eq_comm]
        congrm k.factorial * ?_
        refine sum_nbij (·.image v) (fun a ha => ?hi) ?i_inj (fun t ht => ?i_surj) fun a ha => ?h
        case hi => grind [card_image_of_injOn, hvs'.mono]
        case i_inj => exact (image_injOn_powerset_of_injOn hvs').mono (by grind)
        case i_surj => grind [card_image_of_injOn, hvs'.mono]
case h => exact eq_comm.mp prod_image by grind [hvs'.mono]

/--
theorem `eval_iterate_derivative_eq_sum` / 定理 `eval_iterate_derivative_eq_sum`

English:
theorem eval_iterate_derivative_eq_sum
  statement: (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.degree < #s)
  proof: by
  nth_rewrite 1 [eq_interpolate hvs hP, iterate_derivative_interpolate _ hvs hk]
  simp [eval_finsetSum, eval_prod]

@[deprecated eq_interpolate (since := "2026-01-14")]

中文:
定理 eval_iterate_derivative_eq_sum
  结论: (hvs : 集合.单射限制 v s) {P : 多项式 F} (hP : P.degree < #s)
  证明: by
  nth_rewrite 1 [eq_interpolate hvs hP, iterate_derivative_interpolate _ hvs hk]
  simp [eval_finsetSum, eval_prod]

@[deprecated eq_interpolate (since := "2026-01-14")]

Depends on / 依赖: eq_interpolate, eval_finsetSum, eval_prod, iterate_derivative_interpolate, nth_rewrite
-/
theorem eval_iterate_derivative_eq_sum (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.degree < #s)
    {k : Nat} (hk : k < #s) (x : F) :
    (derivative^[k] P).eval x =
      k.factorial * ∑ i in s, (P.eval (v i) / ∏ j in s.erase i, (v i - v j)) *
        ∑ t in (s.erase i).powersetCard (#s - (k + 1)), ∏ a in t, (x - v a) := by
  nth_rewrite 1 [eq_interpolate hvs hP, iterate_derivative_interpolate _ hvs hk]
  simp [eval_finsetSum, eval_prod]

@[deprecated eq_interpolate (since := "2026-01-14")]
/--
theorem `interpolate_poly_eq_self` / 定理 `interpolate_poly_eq_self`

English:
theorem interpolate_poly_eq_self
  proof: (eq_interpolate hvs hP).symm

中文:
定理 interpolate_poly_eq_self
  证明: (eq_interpolate hvs hP).symm

Depends on / 依赖: eq_interpolate
-/
theorem interpolate_poly_eq_self
    (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.degree < s.card) :
    interpolate s v (fun i => P.eval (v i)) = P := (eq_interpolate hvs hP).symm

/--
theorem `coeff_eq_sum` / 定理 `coeff_eq_sum`

English:
theorem coeff_eq_sum
  proof: by
  nth_rewrite 1 [eq_interpolate hvs hP, interpolate_apply, finsetSum_coeff]
  congr! with i hi
  rw [coeff_C_mul]; rw [← natDegree_basis hvs hi]; rw [← leadingCoeff]; rw [leadingCoeff_basis hvs hi]
  field_simp

中文:
定理 coeff_eq_sum
  证明: by
  nth_rewrite 1 [eq_interpolate hvs hP, interpolate_apply, finsetSum_coeff]
  congr! with i hi
  rw [coeff_C_mul]; rw [← natDegree_basis hvs hi]; rw [← leadingCoeff]; rw [leadingCoeff_basis hvs hi]
  field_simp

Depends on / 依赖: coeff_C_mul, eq_interpolate, finsetSum_coeff, interpolate_apply, leadingCoeff, leadingCoeff_basis, natDegree_basis, nth_rewrite
-/
theorem coeff_eq_sum
    (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.degree < #s) :
    P.coeff (#s - 1) = ∑ i in s, (P.eval (v i)) / ∏ j in s.erase i, (v i - v j) := by
  nth_rewrite 1 [eq_interpolate hvs hP, interpolate_apply, finsetSum_coeff]
  congr! with i hi
  rw [coeff_C_mul]; rw [← natDegree_basis hvs hi]; rw [← leadingCoeff]; rw [leadingCoeff_basis hvs hi]
  field_simp

/--
theorem `leadingCoeff_eq_sum` / 定理 `leadingCoeff_eq_sum`

English:
theorem leadingCoeff_eq_sum
  proof: by
  lift P.degree to Nat using (by contrapose! hP; simp [hP]) with deg hdeg
  rw [← WithBot.coe_one]; rw [← WithBot.coe_add] at hP
  replace hP : #s = deg + 1 := WithBot.coe_eq_coe.mp hP
  have hdegree : P.degree = ↑(#s - 1) := hdeg.symm.trans (WithBot.coe_eq_coe.mpr (by grind))
  rw [leadingCoeff]; rw [natDegree_eq_of_degree_eq_some hdegree]
  exact coeff_eq_sum hvs (by rw [hdegree]; norm_cast; lia)

中文:
定理 leadingCoeff_eq_sum
  证明: by
  lift P.degree to Nat using (by contrapose! hP; simp [hP]) with deg hdeg
  rw [← WithBot.coe_one]; rw [← WithBot.coe_add] at hP
  replace hP : #s = deg + 1 := WithBot.coe_eq_coe.mp hP
  have hdegree : P.degree = ↑(#s - 1) := hdeg.symm.trans (WithBot.coe_eq_coe.mpr (by grind))
  rw [leadingCoeff]; rw [natDegree_eq_of_degree_eq_some hdegree]
  exact coeff_eq_sum hvs (by rw [hdegree]; norm_cast; lia)

Depends on / 依赖: P.degree, WithBot, WithBot.coe_add, WithBot.coe_eq_coe.mp, WithBot.coe_eq_coe.mpr, WithBot.coe_one, coe_add, coe_eq_coe, coe_one, coeff_eq_sum, contrapose, degree, hdeg.symm.trans, hdegree, leadingCoeff, natDegree_eq_of_degree_eq_some, replace
-/
theorem leadingCoeff_eq_sum
    (hvs : Set.InjOn v s) {P : Polynomial F} (hP : #s = P.degree + 1) :
    P.leadingCoeff = ∑ i in s, (P.eval (v i)) / ∏ j in s.erase i, (v i - v j) := by
  lift P.degree to Nat using (by contrapose! hP; simp [hP]) with deg hdeg
  rw [← WithBot.coe_one]; rw [← WithBot.coe_add] at hP
  replace hP : #s = deg + 1 := WithBot.coe_eq_coe.mp hP
  have hdegree : P.degree = ↑(#s - 1) := hdeg.symm.trans (WithBot.coe_eq_coe.mpr (by grind))
  rw [leadingCoeff]; rw [natDegree_eq_of_degree_eq_some hdegree]
  exact coeff_eq_sum hvs (by rw [hdegree]; norm_cast; lia)

/--
lemma `_root_.Polynomial.exists_eval_eq_iff` / 引理 `_root_.Polynomial.exists_eval_eq_iff`

English:
lemma _root_.Polynomial.exists_eval_eq_iff
  given: {ι : Type*} [Finite ι] (x y : ι -> F)
  proof: by
  refine ⟨fun ⟨q, hq⟩ i j hij => by rw [← hq, ← hq, hij], fun hwd => ?_⟩
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hinj : Set.InjOn (fun d : F => d) (Finset.univ.image x) := Function.injective_id.injOn
  set v : F -> F := fun z => if h : exists i, x i = z then y h.choose else 0 with v_def
  refine ⟨Lagrange.interpolate (Finset.univ.image x) (fun d : F => d) v, fun i => ?_⟩
  rw [Lagrange.eval_interpolate_at_node _ hinj (by simp)]; rw [v_def]
  simp only
  split_ifs with h
  · exact hwd _ _ h.choose_spec
  · aesop

中文:
引理 _root_.多项式.存在_eval_eq_iff
  条件: {ι : 类型} [有限 ι] (x y : ι -> F)
  证明: by
  refine ⟨fun ⟨q, hq⟩ i j hij => by rw [← hq, ← hq, hij], fun hwd => ?_⟩
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hinj : Set.InjOn (fun d : F => d) (Finset.univ.image x) := Function.injective_id.injOn
  set v : F -> F := fun z => if h : exists i, x i = z then y h.choose else 0 with v_def
  refine ⟨Lagrange.interpolate (Finset.univ.image x) (fun d : F => d) v, fun i => ?_⟩
  rw [Lagrange.eval_interpolate_at_node _ hinj (by simp)]; rw [v_def]
  simp only
  split_ifs with h
  · exact hwd _ _ h.choose_spec
  · aesop

Depends on / 依赖: Finset, Finset.univ.image, Fintype, Fintype.ofFinite, Function, Function.injective_id.injOn, Lagrange, Lagrange.eval_interpolate_at_node, Lagrange.interpolate, Set.InjOn, classical, eval_interpolate_at_node, h.ch, h.choose, injective_id, interpolate, ofFinite, split_ifs, v_def
-/
lemma _root_.Polynomial.exists_eval_eq_iff {ι : Type*} [Finite ι] (x y : ι -> F) :
    (exists q : F[X], forall i, q.eval (x i) = y i) ↔ forall i j, x i = x j -> y i = y j := by
  refine ⟨fun ⟨q, hq⟩ i j hij => by rw [← hq, ← hq, hij], fun hwd => ?_⟩
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hinj : Set.InjOn (fun d : F => d) (Finset.univ.image x) := Function.injective_id.injOn
  set v : F -> F := fun z => if h : exists i, x i = z then y h.choose else 0 with v_def
  refine ⟨Lagrange.interpolate (Finset.univ.image x) (fun d : F => d) v, fun i => ?_⟩
  rw [Lagrange.eval_interpolate_at_node _ hinj (by simp)]; rw [v_def]
  simp only
  split_ifs with h
  · exact hwd _ _ h.choose_spec
  · aesop

end Interpolate

section Nodal

variable {R : Type*} [CommRing R] {ι : Type*}
variable {s : Finset ι} {v : ι -> R}

open Finset Polynomial

/--
Definition of `nodal` / `nodal` 的定义

English:
definition nodal
  signature: (s : Finset ι) (v : ι -> R)
  body: ∏ i in s, (X - C (v i))

中文:
定义 nodal
  签名: (s : 有限集 ι) (v : ι -> R)
  定义体: ∏ i in s, (X - C (v i))
-/
def nodal (s : Finset ι) (v : ι -> R) : R[X] :=
  ∏ i in s, (X - C (v i))

/--
theorem `nodal_eq` / 定理 `nodal_eq`

English:
theorem nodal_eq
  given: (s : Finset ι) (v : ι -> R)
  statement: nodal s v = ∏ i in s, (X - C (v i))
  proof: rfl

@[simp]

中文:
定理 nodal_eq
  条件: (s : 有限集 ι) (v : ι -> R)
  结论: nodal s v = ∏ i in s, (X - C (v i))
  证明: rfl

@[simp]
-/
theorem nodal_eq (s : Finset ι) (v : ι -> R) : nodal s v = ∏ i in s, (X - C (v i)) :=
  rfl

@[simp]
/--
theorem `nodal_empty` / 定理 `nodal_empty`

English:
theorem nodal_empty
  statement: nodal ∅ v = 1
  proof: by
  rfl

@[simp]

中文:
定理 nodal_empty
  结论: nodal ∅ v = 1
  证明: by
  rfl

@[simp]
-/
theorem nodal_empty : nodal ∅ v = 1 := by
  rfl

@[simp]
/--
theorem `natDegree_nodal` / 定理 `natDegree_nodal`

English:
theorem natDegree_nodal
  given: [Nontrivial R]
  statement: (nodal s v).natDegree = #s
  proof: by
  simp_rw [nodal, natDegree_prod_of_monic (h := fun i _ => monic_X_sub_C (v i)),
    natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]

中文:
定理 natDegree_nodal
  条件: [非平凡 R]
  结论: (nodal s v).natDegree = #s
  证明: by
  simp_rw [nodal, natDegree_prod_of_monic (h := fun i _ => monic_X_sub_C (v i)),
    natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]

Depends on / 依赖: monic_X_sub_C, mul_one, natDegree_X_sub_C, natDegree_prod_of_monic, simp_rw, smul_eq_mul, sum_const
-/
theorem natDegree_nodal [Nontrivial R] : (nodal s v).natDegree = #s := by
  simp_rw [nodal, natDegree_prod_of_monic (h := fun i _ => monic_X_sub_C (v i)),
    natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]

/--
theorem `nodal_ne_zero` / 定理 `nodal_ne_zero`

English:
theorem nodal_ne_zero
  given: [Nontrivial R]
  statement: nodal s v != 0
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · exact one_ne_zero
  · apply ne_zero_of_natDegree_gt (n := 0)
    simp only [natDegree_nodal, h.card_pos]

@[simp]

中文:
定理 nodal_ne_zero
  条件: [非平凡 R]
  结论: nodal s v != 0
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · exact one_ne_zero
  · apply ne_zero_of_natDegree_gt (n := 0)
    simp only [natDegree_nodal, h.card_pos]

@[simp]

Depends on / 依赖: card_pos, eq_empty_or_nonempty, h.card_pos, natDegree_nodal, ne_zero_of_natDegree_gt, one_ne_zero, s.eq_empty_or_nonempty
-/
theorem nodal_ne_zero [Nontrivial R] : nodal s v != 0 := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · exact one_ne_zero
  · apply ne_zero_of_natDegree_gt (n := 0)
    simp only [natDegree_nodal, h.card_pos]

@[simp]
/--
theorem `degree_nodal` / 定理 `degree_nodal`

English:
theorem degree_nodal
  given: [Nontrivial R]
  statement: (nodal s v).degree = #s
  proof: by
  simp_rw [degree_eq_natDegree nodal_ne_zero, natDegree_nodal]

中文:
定理 degree_nodal
  条件: [非平凡 R]
  结论: (nodal s v).degree = #s
  证明: by
  simp_rw [degree_eq_natDegree nodal_ne_zero, natDegree_nodal]

Depends on / 依赖: degree_eq_natDegree, natDegree_nodal, nodal_ne_zero, simp_rw
-/
theorem degree_nodal [Nontrivial R] : (nodal s v).degree = #s := by
  simp_rw [degree_eq_natDegree nodal_ne_zero, natDegree_nodal]

/--
theorem `nodal_monic` / 定理 `nodal_monic`

English:
theorem nodal_monic
  statement: (nodal s v).Monic
  proof: monic_prod_of_monic s (fun i => X - C (v i)) fun i _ => monic_X_sub_C (v i)

中文:
定理 nodal_monic
  结论: (nodal s v).Monic
  证明: monic_prod_of_monic s (fun i => X - C (v i)) fun i _ => monic_X_sub_C (v i)

Depends on / 依赖: monic_X_sub_C, monic_prod_of_monic
-/
theorem nodal_monic : (nodal s v).Monic :=
  monic_prod_of_monic s (fun i => X - C (v i)) fun i _ => monic_X_sub_C (v i)

/--
theorem `eval_nodal` / 定理 `eval_nodal`

English:
theorem eval_nodal
  given: {x : R}
  statement: (nodal s v).eval x = ∏ i in s, (x - v i)
  proof: by
  simp_rw [nodal, eval_prod, eval_sub, eval_X, eval_C]

中文:
定理 eval_nodal
  条件: {x : R}
  结论: (nodal s v).eval x = ∏ i in s, (x - v i)
  证明: by
  simp_rw [nodal, eval_prod, eval_sub, eval_X, eval_C]

Depends on / 依赖: eval_C, eval_X, eval_prod, eval_sub, simp_rw
-/
theorem eval_nodal {x : R} : (nodal s v).eval x = ∏ i in s, (x - v i) := by
  simp_rw [nodal, eval_prod, eval_sub, eval_X, eval_C]

/--
theorem `eval_nodal_at_node` / 定理 `eval_nodal_at_node`

English:
theorem eval_nodal_at_node
  given: {i : ι} (hi : i in s)
  statement: eval (v i) (nodal s v) = 0
  proof: by
  rw [eval_nodal]
  exact s.prod_eq_zero hi (sub_self (v i))

中文:
定理 eval_nodal_at_node
  条件: {i : ι} (hi : i in s)
  结论: eval (v i) (nodal s v) = 0
  证明: by
  rw [eval_nodal]
  exact s.prod_eq_zero hi (sub_self (v i))

Depends on / 依赖: eval_nodal, prod_eq_zero, s.prod_eq_zero, sub_self
-/
theorem eval_nodal_at_node {i : ι} (hi : i in s) : eval (v i) (nodal s v) = 0 := by
  rw [eval_nodal]
  exact s.prod_eq_zero hi (sub_self (v i))

/--
theorem `eval_nodal_not_at_node` / 定理 `eval_nodal_not_at_node`

English:
theorem eval_nodal_not_at_node
  statement: [Nontrivial R] [NoZeroDivisors R] {x : R}
  proof: by
  simp_rw [nodal, eval_prod, prod_ne_zero_iff, eval_sub, eval_X, eval_C, sub_ne_zero]
  exact hx

中文:
定理 eval_nodal_not_at_node
  结论: [非平凡 R] [无零因子 R] {x : R}
  证明: by
  simp_rw [nodal, eval_prod, prod_ne_zero_iff, eval_sub, eval_X, eval_C, sub_ne_zero]
  exact hx

Depends on / 依赖: eval_C, eval_X, eval_prod, eval_sub, prod_ne_zero_iff, simp_rw, sub_ne_zero
-/
theorem eval_nodal_not_at_node [Nontrivial R] [NoZeroDivisors R] {x : R}
    (hx : forall i in s, x != v i) : eval x (nodal s v) != 0 := by
  simp_rw [nodal, eval_prod, prod_ne_zero_iff, eval_sub, eval_X, eval_C, sub_ne_zero]
  exact hx

/--
theorem `nodal_eq_mul_nodal_erase` / 定理 `nodal_eq_mul_nodal_erase`

English:
theorem nodal_eq_mul_nodal_erase
  given: [DecidableEq ι] {i : ι} (hi : i in s)
  proof: by
    simp_rw [nodal, Finset.mul_prod_erase _ (fun x => X - C (v x)) hi]

中文:
定理 nodal_eq_mul_nodal_erase
  条件: [DecidableEq ι] {i : ι} (hi : i in s)
  证明: by
    simp_rw [nodal, Finset.mul_prod_erase _ (fun x => X - C (v x)) hi]

Depends on / 依赖: Finset, Finset.mul_prod_erase, mul_prod_erase, simp_rw
-/
theorem nodal_eq_mul_nodal_erase [DecidableEq ι] {i : ι} (hi : i in s) :
    nodal s v = (X - C (v i)) * nodal (s.erase i) v := by
    simp_rw [nodal, Finset.mul_prod_erase _ (fun x => X - C (v x)) hi]

/--
theorem `X_sub_C_dvd_nodal` / 定理 `X_sub_C_dvd_nodal`

English:
theorem X_sub_C_dvd_nodal
  given: (v : ι -> R) {i : ι} (hi : i in s)
  statement: X - C (v i) ∣ nodal s v
  proof: by
  classical
  exact ⟨nodal (s.erase i) v, nodal_eq_mul_nodal_erase hi⟩

中文:
定理 X_sub_C_dvd_nodal
  条件: (v : ι -> R) {i : ι} (hi : i in s)
  结论: X - C (v i) ∣ nodal s v
  证明: by
  classical
  exact ⟨nodal (s.erase i) v, nodal_eq_mul_nodal_erase hi⟩

Depends on / 依赖: classical, nodal_eq_mul_nodal_erase, s.erase
-/
theorem X_sub_C_dvd_nodal (v : ι -> R) {i : ι} (hi : i in s) : X - C (v i) ∣ nodal s v := by
  classical
  exact ⟨nodal (s.erase i) v, nodal_eq_mul_nodal_erase hi⟩

/--
theorem `nodal_insert_eq_nodal` / 定理 `nodal_insert_eq_nodal`

English:
theorem nodal_insert_eq_nodal
  given: [DecidableEq ι] {i : ι} (hi : i ∉ s)
  proof: by
  simp_rw [nodal, prod_insert hi]

中文:
定理 nodal_insert_eq_nodal
  条件: [DecidableEq ι] {i : ι} (hi : i ∉ s)
  证明: by
  simp_rw [nodal, prod_insert hi]

Depends on / 依赖: prod_insert, simp_rw
-/
theorem nodal_insert_eq_nodal [DecidableEq ι] {i : ι} (hi : i ∉ s) :
    nodal (insert i s) v = (X - C (v i)) * nodal s v := by
  simp_rw [nodal, prod_insert hi]

/--
theorem `derivative_nodal` / 定理 `derivative_nodal`

English:
theorem derivative_nodal
  given: [DecidableEq ι]
  proof: by
  refine s.induction_on ?_ fun i t hit IH => ?_
  · rw [nodal_empty, derivative_one, sum_empty]
  · rw [nodal_insert_eq_nodal hit, derivative_mul, IH, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, sum_insert hit, mul_sum, erase_insert hit, add_right_inj]
    refine sum_congr rfl fun j hjt => ?_
    rw [t.erase_insert_of_ne (ne_of_mem_of_not_mem hjt hit).symm]; rw [nodal_insert_eq_nodal (mem_of_mem_erase.mt hit)]

中文:
定理 derivative_nodal
  条件: [DecidableEq ι]
  证明: by
  refine s.induction_on ?_ fun i t hit IH => ?_
  · rw [nodal_empty, derivative_one, sum_empty]
  · rw [nodal_insert_eq_nodal hit, derivative_mul, IH, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, sum_insert hit, mul_sum, erase_insert hit, add_right_inj]
    refine sum_congr rfl fun j hjt => ?_
    rw [t.erase_insert_of_ne (ne_of_mem_of_not_mem hjt hit).symm]; rw [nodal_insert_eq_nodal (mem_of_mem_erase.mt hit)]

Depends on / 依赖: add_right_inj, derivative_C, derivative_X, derivative_mul, derivative_one, derivative_sub, erase_insert, erase_insert_of_ne, induction_on, mem_of_mem_erase, mem_of_mem_erase.mt, mul_sum, ne_of_mem_of_not_mem, nodal_empty, nodal_insert_eq_nodal, one_mul, s.induction_on, sub_zero, sum_congr, sum_empty
-/
theorem derivative_nodal [DecidableEq ι] :
    derivative (nodal s v) = ∑ i in s, nodal (s.erase i) v := by
  refine s.induction_on ?_ fun i t hit IH => ?_
  · rw [nodal_empty, derivative_one, sum_empty]
  · rw [nodal_insert_eq_nodal hit, derivative_mul, IH, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, sum_insert hit, mul_sum, erase_insert hit, add_right_inj]
    refine sum_congr rfl fun j hjt => ?_
    rw [t.erase_insert_of_ne (ne_of_mem_of_not_mem hjt hit).symm]; rw [nodal_insert_eq_nodal (mem_of_mem_erase.mt hit)]

/--
theorem `eval_nodal_derivative_eval_node_eq` / 定理 `eval_nodal_derivative_eval_node_eq`

English:
theorem eval_nodal_derivative_eval_node_eq
  given: [DecidableEq ι] {i : ι} (hi : i in s)
  proof: by
  rw [derivative_nodal]; rw [eval_finsetSum]; rw [← add_sum_erase _ _ hi]; rw [add_eq_left]
  exact sum_eq_zero fun j hj => (eval_nodal_at_node (mem_erase.mpr ⟨(mem_erase.mp hj).1.symm, hi⟩))

中文:
定理 eval_nodal_derivative_eval_node_eq
  条件: [DecidableEq ι] {i : ι} (hi : i in s)
  证明: by
  rw [derivative_nodal]; rw [eval_finsetSum]; rw [← add_sum_erase _ _ hi]; rw [add_eq_left]
  exact sum_eq_zero fun j hj => (eval_nodal_at_node (mem_erase.mpr ⟨(mem_erase.mp hj).1.symm, hi⟩))

Depends on / 依赖: add_eq_left, add_sum_erase, derivative_nodal, eval_finsetSum, eval_nodal_at_node, mem_erase, mem_erase.mp, mem_erase.mpr, sum_eq_zero
-/
theorem eval_nodal_derivative_eval_node_eq [DecidableEq ι] {i : ι} (hi : i in s) :
    eval (v i) (derivative (nodal s v)) = eval (v i) (nodal (s.erase i) v) := by
  rw [derivative_nodal]; rw [eval_finsetSum]; rw [← add_sum_erase _ _ hi]; rw [add_eq_left]
  exact sum_eq_zero fun j hj => (eval_nodal_at_node (mem_erase.mpr ⟨(mem_erase.mp hj).1.symm, hi⟩))

/--
theorem `nodal_subgroup_eq_X_pow_card_sub_one` / 定理 `nodal_subgroup_eq_X_pow_card_sub_one`

English:
theorem nodal_subgroup_eq_X_pow_card_sub_one
  statement: [IsDomain R]
  proof: by
  have h : degree (1 : R[X]) < degree ((X : R[X]) ^ Fintype.card G) := by simp [Fintype.card_pos]
  apply eq_of_degree_le_of_eval_index_eq (v := ((↑) : Rˣ -> R)) (G : Set Rˣ).toFinset
  · exact Units.val_injective.injOn
  · simp
  · rw [degree_sub_eq_left_of_degree_lt h, degree_nodal, Set.toFinset_card, degree_pow, degree_X,
      nsmul_eq_mul, mul_one, Nat.cast_inj]
    exact rfl
  · rw [nodal_monic, leadingCoeff_sub_of_degree_lt h, monic_X_pow]
  · intro i hi
    rw [eval_nodal_at_node hi]
    replace hi : i in G := by simpa using hi
    obtain ⟨g, rfl⟩ : exists g : G, g.val = i := ⟨⟨i, hi⟩, rfl⟩
    simp [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow G]

中文:
定理 nodal_subgroup_eq_X_pow_card_sub_one
  结论: [是整环 R]
  证明: by
  have h : degree (1 : R[X]) < degree ((X : R[X]) ^ Fintype.card G) := by simp [Fintype.card_pos]
  apply eq_of_degree_le_of_eval_index_eq (v := ((↑) : Rˣ -> R)) (G : Set Rˣ).toFinset
  · exact Units.val_injective.injOn
  · simp
  · rw [degree_sub_eq_left_of_degree_lt h, degree_nodal, Set.toFinset_card, degree_pow, degree_X,
      nsmul_eq_mul, mul_one, Nat.cast_inj]
    exact rfl
  · rw [nodal_monic, leadingCoeff_sub_of_degree_lt h, monic_X_pow]
  · intro i hi
    rw [eval_nodal_at_node hi]
    replace hi : i in G := by simpa using hi
    obtain ⟨g, rfl⟩ : exists g : G, g.val = i := ⟨⟨i, hi⟩, rfl⟩
    simp [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow G]
-/
@[simp] theorem nodal_subgroup_eq_X_pow_card_sub_one [IsDomain R]
    (G : Subgroup Rˣ) [Fintype G] :
    nodal (G : Set Rˣ).toFinset ((↑) : Rˣ -> R) = X ^ (Fintype.card G) - 1 := by
  have h : degree (1 : R[X]) < degree ((X : R[X]) ^ Fintype.card G) := by simp [Fintype.card_pos]
  apply eq_of_degree_le_of_eval_index_eq (v := ((↑) : Rˣ -> R)) (G : Set Rˣ).toFinset
  · exact Units.val_injective.injOn
  · simp
  · rw [degree_sub_eq_left_of_degree_lt h, degree_nodal, Set.toFinset_card, degree_pow, degree_X,
      nsmul_eq_mul, mul_one, Nat.cast_inj]
    exact rfl
  · rw [nodal_monic, leadingCoeff_sub_of_degree_lt h, monic_X_pow]
  · intro i hi
    rw [eval_nodal_at_node hi]
    replace hi : i in G := by simpa using hi
    obtain ⟨g, rfl⟩ : exists g : G, g.val = i := ⟨⟨i, hi⟩, rfl⟩
    simp [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow G]

end Nodal

section NodalWeight

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι -> F} {i : ι}

open Finset

/--
Definition of `nodalWeight` / `nodalWeight` 的定义

English:
definition nodalWeight
  signature: (s : Finset ι) (v : ι -> F) (i : ι)
  body: ∏ j in s.erase i, (v i - v j)⁻¹

中文:
定义 nodalWeight
  签名: (s : 有限集 ι) (v : ι -> F) (i : ι)
  定义体: ∏ j in s.erase i, (v i - v j)⁻¹

Depends on / 依赖: s.erase
-/
def nodalWeight (s : Finset ι) (v : ι -> F) (i : ι) :=
  ∏ j in s.erase i, (v i - v j)⁻¹

/--
theorem `nodalWeight_eq_eval_nodal_erase_inv` / 定理 `nodalWeight_eq_eval_nodal_erase_inv`

English:
theorem nodalWeight_eq_eval_nodal_erase_inv
  proof: by
  rw [eval_nodal]; rw [nodalWeight]; rw [prod_inv_distrib]

中文:
定理 nodalWeight_eq_eval_nodal_erase_inv
  证明: by
  rw [eval_nodal]; rw [nodalWeight]; rw [prod_inv_distrib]

Depends on / 依赖: eval_nodal, nodalWeight, prod_inv_distrib
-/
theorem nodalWeight_eq_eval_nodal_erase_inv :
    nodalWeight s v i = (eval (v i) (nodal (s.erase i) v))⁻¹ := by
  rw [eval_nodal]; rw [nodalWeight]; rw [prod_inv_distrib]

/--
theorem `nodal_erase_eq_nodal_div` / 定理 `nodal_erase_eq_nodal_div`

English:
theorem nodal_erase_eq_nodal_div
  given: (hi : i in s)
  proof: by
  rw [nodal_eq_mul_nodal_erase hi]; rw [mul_div_cancel_left₀]
  exact X_sub_C_ne_zero _

中文:
定理 nodal_erase_eq_nodal_div
  条件: (hi : i in s)
  证明: by
  rw [nodal_eq_mul_nodal_erase hi]; rw [mul_div_cancel_left₀]
  exact X_sub_C_ne_zero _

Depends on / 依赖: X_sub_C_ne_zero, nodal_eq_mul_nodal_erase
-/
theorem nodal_erase_eq_nodal_div (hi : i in s) :
    nodal (s.erase i) v = nodal s v / (X - C (v i)) := by
  rw [nodal_eq_mul_nodal_erase hi]; rw [mul_div_cancel_left₀]
  exact X_sub_C_ne_zero _

/--
theorem `nodalWeight_eq_eval_derivative_nodal` / 定理 `nodalWeight_eq_eval_derivative_nodal`

English:
theorem nodalWeight_eq_eval_derivative_nodal
  given: (hi : i in s)
  proof: by
  rw [eval_nodal_derivative_eval_node_eq hi]; rw [nodalWeight_eq_eval_nodal_erase_inv]

中文:
定理 nodalWeight_eq_eval_derivative_nodal
  条件: (hi : i in s)
  证明: by
  rw [eval_nodal_derivative_eval_node_eq hi]; rw [nodalWeight_eq_eval_nodal_erase_inv]

Depends on / 依赖: eval_nodal_derivative_eval_node_eq, nodalWeight_eq_eval_nodal_erase_inv
-/
theorem nodalWeight_eq_eval_derivative_nodal (hi : i in s) :
    nodalWeight s v i = (eval (v i) (Polynomial.derivative (nodal s v)))⁻¹ := by
  rw [eval_nodal_derivative_eval_node_eq hi]; rw [nodalWeight_eq_eval_nodal_erase_inv]

/--
theorem `nodalWeight_ne_zero` / 定理 `nodalWeight_ne_zero`

English:
theorem nodalWeight_ne_zero
  given: (hvs : Set.InjOn v s) (hi : i in s)
  statement: nodalWeight s v i != 0
  proof: by
  rw [nodalWeight]; rw [prod_ne_zero_iff]
  intro j hj
  rcases mem_erase.mp hj with ⟨hij, hj⟩
  exact inv_ne_zero (sub_ne_zero_of_ne (mt (hvs.eq_iff hi hj).mp hij.symm))

中文:
定理 nodalWeight_ne_zero
  条件: (hvs : 集合.单射限制 v s) (hi : i in s)
  结论: nodalWeight s v i != 0
  证明: by
  rw [nodalWeight]; rw [prod_ne_zero_iff]
  intro j hj
  rcases mem_erase.mp hj with ⟨hij, hj⟩
  exact inv_ne_zero (sub_ne_zero_of_ne (mt (hvs.eq_iff hi hj).mp hij.symm))

Depends on / 依赖: eq_iff, hij.symm, hvs.eq_iff, inv_ne_zero, mem_erase, mem_erase.mp, nodalWeight, prod_ne_zero_iff, sub_ne_zero_of_ne
-/
theorem nodalWeight_ne_zero (hvs : Set.InjOn v s) (hi : i in s) : nodalWeight s v i != 0 := by
  rw [nodalWeight]; rw [prod_ne_zero_iff]
  intro j hj
  rcases mem_erase.mp hj with ⟨hij, hj⟩
  exact inv_ne_zero (sub_ne_zero_of_ne (mt (hvs.eq_iff hi hj).mp hij.symm))

end NodalWeight

section LagrangeBarycentric

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι -> F} (r : ι -> F) {i : ι} {x : F}

open Finset

/--
theorem `basis_eq_prod_sub_inv_mul_nodal_div` / 定理 `basis_eq_prod_sub_inv_mul_nodal_div`

English:
theorem basis_eq_prod_sub_inv_mul_nodal_div
  given: (hi : i in s)
  proof: by
  simp_rw [Lagrange.basis, basisDivisor, nodalWeight, prod_mul_distrib, map_prod, ←
    nodal_erase_eq_nodal_div hi, nodal]

中文:
定理 basis_eq_prod_sub_inv_mul_nodal_div
  条件: (hi : i in s)
  证明: by
  simp_rw [Lagrange.basis, basisDivisor, nodalWeight, prod_mul_distrib, map_prod, ←
    nodal_erase_eq_nodal_div hi, nodal]

Depends on / 依赖: Lagrange, Lagrange.basis, basisDivisor, map_prod, nodalWeight, nodal_erase_eq_nodal_div, prod_mul_distrib, simp_rw
-/
theorem basis_eq_prod_sub_inv_mul_nodal_div (hi : i in s) :
    Lagrange.basis s v i = C (nodalWeight s v i) * (nodal s v / (X - C (v i))) := by
  simp_rw [Lagrange.basis, basisDivisor, nodalWeight, prod_mul_distrib, map_prod, ←
    nodal_erase_eq_nodal_div hi, nodal]

/--
theorem `eval_basis_not_at_node` / 定理 `eval_basis_not_at_node`

English:
theorem eval_basis_not_at_node
  given: (hi : i in s) (hxi : x != v i)
  proof: by
  rw [mul_comm]; rw [basis_eq_prod_sub_inv_mul_nodal_div hi]; rw [eval_mul]; rw [eval_C]; rw [←
    nodal_erase_eq_nodal_div hi]; rw [eval_nodal]; rw [eval_nodal]; rw [mul_assoc]; rw [← mul_prod_erase _ _ hi]; rw [←
    mul_assoc (x - v i)⁻¹]; rw [inv_mul_cancel₀ (sub_ne_zero_of_ne hxi)]; rw [one_mul]

中文:
定理 eval_basis_not_at_node
  条件: (hi : i in s) (hxi : x != v i)
  证明: by
  rw [mul_comm]; rw [basis_eq_prod_sub_inv_mul_nodal_div hi]; rw [eval_mul]; rw [eval_C]; rw [←
    nodal_erase_eq_nodal_div hi]; rw [eval_nodal]; rw [eval_nodal]; rw [mul_assoc]; rw [← mul_prod_erase _ _ hi]; rw [←
    mul_assoc (x - v i)⁻¹]; rw [inv_mul_cancel₀ (sub_ne_zero_of_ne hxi)]; rw [one_mul]

Depends on / 依赖: basis_eq_prod_sub_inv_mul_nodal_div, eval_C, eval_mul, eval_nodal, mul_assoc, mul_comm, mul_prod_erase, nodal_erase_eq_nodal_div, one_mul, sub_ne_zero_of_ne
-/
theorem eval_basis_not_at_node (hi : i in s) (hxi : x != v i) :
    eval x (Lagrange.basis s v i) = eval x (nodal s v) * (nodalWeight s v i * (x - v i)⁻¹) := by
  rw [mul_comm]; rw [basis_eq_prod_sub_inv_mul_nodal_div hi]; rw [eval_mul]; rw [eval_C]; rw [←
    nodal_erase_eq_nodal_div hi]; rw [eval_nodal]; rw [eval_nodal]; rw [mul_assoc]; rw [← mul_prod_erase _ _ hi]; rw [←
    mul_assoc (x - v i)⁻¹]; rw [inv_mul_cancel₀ (sub_ne_zero_of_ne hxi)]; rw [one_mul]

/--
theorem `interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C` / 定理 `interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C`

English:
theorem interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C
  proof: sum_congr rfl fun j hj => by rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hj]

中文:
定理 interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C
  证明: sum_congr rfl fun j hj => by rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hj]

Depends on / 依赖: basis_eq_prod_sub_inv_mul_nodal_div, mul_comm, sum_congr
-/
theorem interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C :
    interpolate s v r = ∑ i in s, C (nodalWeight s v i) * (nodal s v / (X - C (v i))) * C (r i) :=
  sum_congr rfl fun j hj => by rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hj]

/--
theorem `eval_interpolate_not_at_node` / 定理 `eval_interpolate_not_at_node`

English:
theorem eval_interpolate_not_at_node
  given: (hx : forall i in s, x != v i)
  proof: by
  simp_rw [interpolate_apply, mul_sum, eval_finsetSum, eval_mul, eval_C]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_assoc]; rw [mul_comm]; rw [eval_basis_not_at_node hi (hx _ hi)]

中文:
定理 eval_interpolate_not_at_node
  条件: (hx : 对任意 i in s, x != v i)
  证明: by
  simp_rw [interpolate_apply, mul_sum, eval_finsetSum, eval_mul, eval_C]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_assoc]; rw [mul_comm]; rw [eval_basis_not_at_node hi (hx _ hi)]

Depends on / 依赖: eval_C, eval_basis_not_at_node, eval_finsetSum, eval_mul, interpolate_apply, mul_assoc, mul_comm, mul_sum, simp_rw, sum_congr
-/
theorem eval_interpolate_not_at_node (hx : forall i in s, x != v i) :
    eval x (interpolate s v r) =
      eval x (nodal s v) * ∑ i in s, nodalWeight s v i * (x - v i)⁻¹ * r i := by
  simp_rw [interpolate_apply, mul_sum, eval_finsetSum, eval_mul, eval_C]
  refine sum_congr rfl fun i hi => ?_
  rw [← mul_assoc]; rw [mul_comm]; rw [eval_basis_not_at_node hi (hx _ hi)]

/--
theorem `sum_nodalWeight_mul_inv_sub_ne_zero` / 定理 `sum_nodalWeight_mul_inv_sub_ne_zero`

English:
theorem sum_nodalWeight_mul_inv_sub_ne_zero
  statement: (hvs : Set.InjOn v s) (hx : forall i in s, x != v i)
  proof: @right_ne_zero_of_mul_eq_one _ _ _ (eval x (nodal s v)) _ by
    simpa only [Pi.one_apply, interpolate_one hvs hs, eval_one, mul_one] using
      (eval_interpolate_not_at_node 1 hx).symm

中文:
定理 sum_nodalWeight_mul_inv_sub_ne_zero
  结论: (hvs : 集合.单射限制 v s) (hx : 对任意 i in s, x != v i)
  证明: @right_ne_zero_of_mul_eq_one _ _ _ (eval x (nodal s v)) _ by
    simpa only [Pi.one_apply, interpolate_one hvs hs, eval_one, mul_one] using
      (eval_interpolate_not_at_node 1 hx).symm

Depends on / 依赖: Pi.one_apply, eval_interpolate_not_at_node, eval_one, interpolate_one, mul_one, one_apply, right_ne_zero_of_mul_eq_one
-/
theorem sum_nodalWeight_mul_inv_sub_ne_zero (hvs : Set.InjOn v s) (hx : forall i in s, x != v i)
    (hs : s.Nonempty) : (∑ i in s, nodalWeight s v i * (x - v i)⁻¹) != 0 :=
@right_ne_zero_of_mul_eq_one _ _ _ (eval x (nodal s v)) _ by
    simpa only [Pi.one_apply, interpolate_one hvs hs, eval_one, mul_one] using
      (eval_interpolate_not_at_node 1 hx).symm

/--
theorem `eval_interpolate_not_at_node'` / 定理 `eval_interpolate_not_at_node'`

English:
theorem eval_interpolate_not_at_node'
  statement: (hvs : Set.InjOn v s) (hs : s.Nonempty)
  proof: by
  rw [← div_one (eval x (interpolate s v r))]; rw [← @eval_one _ _ x]; rw [← interpolate_one hvs hs]; rw [eval_interpolate_not_at_node r hx]; rw [eval_interpolate_not_at_node 1 hx]
  simp only [mul_div_mul_left _ _ (eval_nodal_not_at_node hx), Pi.one_apply, mul_one]

中文:
定理 eval_interpolate_not_at_node'
  结论: (hvs : 集合.单射限制 v s) (hs : s.非空)
  证明: by
  rw [← div_one (eval x (interpolate s v r))]; rw [← @eval_one _ _ x]; rw [← interpolate_one hvs hs]; rw [eval_interpolate_not_at_node r hx]; rw [eval_interpolate_not_at_node 1 hx]
  simp only [mul_div_mul_left _ _ (eval_nodal_not_at_node hx), Pi.one_apply, mul_one]

Depends on / 依赖: Pi.one_apply, div_one, eval_interpolate_not_at_node, eval_nodal_not_at_node, eval_one, interpolate, interpolate_one, mul_div_mul_left, mul_one, one_apply
-/
theorem eval_interpolate_not_at_node' (hvs : Set.InjOn v s) (hs : s.Nonempty)
    (hx : forall i in s, x != v i) :
    eval x (interpolate s v r) =
      (∑ i in s, nodalWeight s v i * (x - v i)⁻¹ * r i) /
        ∑ i in s, nodalWeight s v i * (x - v i)⁻¹ := by
  rw [← div_one (eval x (interpolate s v r))]; rw [← @eval_one _ _ x]; rw [← interpolate_one hvs hs]; rw [eval_interpolate_not_at_node r hx]; rw [eval_interpolate_not_at_node 1 hx]
  simp only [mul_div_mul_left _ _ (eval_nodal_not_at_node hx), Pi.one_apply, mul_one]

end LagrangeBarycentric

end Lagrange
