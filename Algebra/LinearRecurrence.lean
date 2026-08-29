/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Linear recurrence

Informally, a "linear recurrence" is an assertion of the form
`∀ n : ℕ, u (n + d) = a 0 * u n + a 1 * u (n+1) + ... + a (d-1) * u (n+d-1)`,
where `u` is a sequence, `d` is the *order* of the recurrence and the `a i`
are its *coefficients*.

In this file, we define the structure `LinearRecurrence` so that
`LinearRecurrence.mk d a` represents the above relation, and we call
a sequence `u` which verifies it a *solution* of the linear recurrence.

We prove a few basic lemmas about this concept, such as :

* the space of solutions is a submodule of `(ℕ → α)` (i.e a vector space if `α`
  is a field)
* the function that maps a solution `u` to its first `d` terms builds a `LinearEquiv`
  between the solution space and `Fin d → α`, aka `α ^ d`. As a consequence, two
  solutions are equal if and only if their first `d` terms are equal.
* a geometric sequence `q ^ n` is solution iff `q` is a root of a particular polynomial,
  which we call the *characteristic polynomial* of the recurrence

Of course, although we can inductively generate solutions (cf `mkSol`), the
interesting part would be to determine closed-forms for the solutions.
This is currently *not implemented*, as we are waiting for definition and
properties of eigenvalues and eigenvectors.

-/

@[expose] public section

noncomputable section

open Finset

open Polynomial

/-- A "linear recurrence relation" over a commutative semiring is given by its
  order `n` and `n` coefficients. -/
@[wikidata Q364089]
/--
Definition of `LinearRecurrence` / `LinearRecurrence` 的定义

English:
structure LinearRecurrence
  parameters: (R : Type*) [CommSemiring R]
  axioms and operations (2):
    - order : Nat
    - coeffs : Fin order -> R

中文:
结构 LinearRecurrence
  参数: (R : 类型) [交换半环 R]
  公理与运算 (2 个):
    - order : 自然数
    - coeffs : 有限集 order -> R
-/
structure LinearRecurrence (R : Type*) [CommSemiring R] where
  /-- Order of the linear recurrence -/
  order : Nat
  /-- Coefficients of the linear recurrence -/
  coeffs : Fin order -> R

instance (R : Type*) [CommSemiring R] : Inhabited (LinearRecurrence R) :=
  ⟨⟨0, default⟩⟩

namespace LinearRecurrence

section CommSemiring

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

/--
Definition of `IsSolution` / `IsSolution` 的定义

English:
definition IsSolution
  signature: (u : Nat -> R)
  body: forall n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i)

中文:
定义 IsSolution
  签名: (u : 自然数 -> R)
  定义体: forall n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i)

Depends on / 依赖: E.coeffs, E.order, coeffs
-/
def IsSolution (u : Nat -> R) :=
  forall n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i)

/--
Definition of `mkSol` / `mkSol` 的定义

English:
definition mkSol
  signature: (init : Fin E.order -> R)
  body: by lia
        E.coeffs k * mkSol init (n - E.order + k)

中文:
定义 mkSol
  签名: (init : 有限集 E.order -> R)
  定义体: by lia
        E.coeffs k * mkSol init (n - E.order + k)

Depends on / 依赖: E.coeffs, E.order, coeffs
-/
def mkSol (init : Fin E.order -> R) : Nat -> R
  | n =>
    if h : n < E.order then init ⟨n, h⟩
    else
      ∑ k : Fin E.order,
        have _ : n - E.order + k < n := by lia
        E.coeffs k * mkSol init (n - E.order + k)

/--
theorem `is_sol_mkSol` / 定理 `is_sol_mkSol`

English:
theorem is_sol_mkSol
  given: (init : Fin E.order -> R)
  statement: E.IsSolution (E.mkSol init)
  proof: by
  intro n
  rw [mkSol]
  simp

中文:
定理 is_sol_mkSol
  条件: (init : 有限集 E.order -> R)
  结论: E.IsSolution (E.mkSol init)
  证明: by
  intro n
  rw [mkSol]
  simp
-/
theorem is_sol_mkSol (init : Fin E.order -> R) : E.IsSolution (E.mkSol init) := by
  intro n
  rw [mkSol]
  simp

/--
theorem `mkSol_eq_init` / 定理 `mkSol_eq_init`

English:
theorem mkSol_eq_init
  given: (init : Fin E.order -> R)
  statement: forall n : Fin E.order, E.mkSol init n = init n
  proof: by
  intro n
  rw [mkSol]
  simp only [n.is_lt, dif_pos, Fin.mk_val]

中文:
定理 mkSol_eq_init
  条件: (init : 有限集 E.order -> R)
  结论: 对任意 n : 有限集 E.order, E.mkSol init n = init n
  证明: by
  intro n
  rw [mkSol]
  simp only [n.is_lt, dif_pos, Fin.mk_val]

Depends on / 依赖: Fin.mk_val, dif_pos, is_lt, mk_val, n.is_lt
-/
theorem mkSol_eq_init (init : Fin E.order -> R) : forall n : Fin E.order, E.mkSol init n = init n := by
  intro n
  rw [mkSol]
  simp only [n.is_lt, dif_pos, Fin.mk_val]

/--
theorem `eq_mk_of_is_sol_of_eq_init` / 定理 `eq_mk_of_is_sol_of_eq_init`

English:
theorem eq_mk_of_is_sol_of_eq_init
  statement: {u : Nat -> R} {init : Fin E.order -> R} (h : E.IsSolution u)
  proof: by
  intro n
  rw [mkSol]
  split_ifs with h'
  · exact mod_cast heq ⟨n, h'⟩
  · dsimp only
    rw [← tsub_add_cancel_of_le (le_of_not_gt h')]; rw [h (n - E.order)]
    congr with k
    rw [eq_mk_of_is_sol_of_eq_init h heq (n - E.order + k)]
    simp

中文:
定理 eq_mk_of_is_sol_of_eq_init
  结论: {u : 自然数 -> R} {init : 有限集 E.order -> R} (h : E.IsSolution u)
  证明: by
  intro n
  rw [mkSol]
  split_ifs with h'
  · exact mod_cast heq ⟨n, h'⟩
  · dsimp only
    rw [← tsub_add_cancel_of_le (le_of_not_gt h')]; rw [h (n - E.order)]
    congr with k
    rw [eq_mk_of_is_sol_of_eq_init h heq (n - E.order + k)]
    simp

Depends on / 依赖: E.order, eq_mk_of_is_sol_of_eq_init, le_of_not_gt, mod_cast, split_ifs, tsub_add_cancel_of_le
-/
theorem eq_mk_of_is_sol_of_eq_init {u : Nat -> R} {init : Fin E.order -> R} (h : E.IsSolution u)
    (heq : forall n : Fin E.order, u n = init n) : forall n, u n = E.mkSol init n := by
  intro n
  rw [mkSol]
  split_ifs with h'
  · exact mod_cast heq ⟨n, h'⟩
  · dsimp only
    rw [← tsub_add_cancel_of_le (le_of_not_gt h')]; rw [h (n - E.order)]
    congr with k
    rw [eq_mk_of_is_sol_of_eq_init h heq (n - E.order + k)]
    simp

/--
theorem `eq_mk_of_is_sol_of_eq_init'` / 定理 `eq_mk_of_is_sol_of_eq_init'`

English:
theorem eq_mk_of_is_sol_of_eq_init'
  statement: {u : Nat -> R} {init : Fin E.order -> R} (h : E.IsSolution u)
  proof: funext (E.eq_mk_of_is_sol_of_eq_init h heq)

中文:
定理 eq_mk_of_is_sol_of_eq_init'
  结论: {u : 自然数 -> R} {init : 有限集 E.order -> R} (h : E.IsSolution u)
  证明: funext (E.eq_mk_of_is_sol_of_eq_init h heq)

Depends on / 依赖: E.eq_mk_of_is_sol_of_eq_init, eq_mk_of_is_sol_of_eq_init
-/
theorem eq_mk_of_is_sol_of_eq_init' {u : Nat -> R} {init : Fin E.order -> R} (h : E.IsSolution u)
    (heq : forall n : Fin E.order, u n = init n) : u = E.mkSol init :=
  funext (E.eq_mk_of_is_sol_of_eq_init h heq)

/--
Definition of `solSpace` / `solSpace` 的定义

English:
definition solSpace
  signature: : Submodule R (Nat -> R) where
  body: { u | E.IsSolution u }
  zero_mem' n := by simp
  add_mem' {u v} hu hv n := by simp [mul_add, sum_add_distrib, hu n, hv n]
  smul_mem' a u hu n := by simp [hu n, mul_sum]; ac_rfl

中文:
定义 solSpace
  签名: : 子模 R (自然数 -> R) where
  定义体: { u | E.IsSolution u }
  zero_mem' n := by simp
  add_mem' {u v} hu hv n := by simp [mul_add, sum_add_distrib, hu n, hv n]
  smul_mem' a u hu n := by simp [hu n, mul_sum]; ac_rfl

Depends on / 依赖: E.IsSolution, IsSolution
-/
def solSpace : Submodule R (Nat -> R) where
  carrier := { u | E.IsSolution u }
  zero_mem' n := by simp
  add_mem' {u v} hu hv n := by simp [mul_add, sum_add_distrib, hu n, hv n]
  smul_mem' a u hu n := by simp [hu n, mul_sum]; ac_rfl

/--
theorem `is_sol_iff_mem_solSpace` / 定理 `is_sol_iff_mem_solSpace`

English:
theorem is_sol_iff_mem_solSpace
  given: (u : Nat -> R)
  statement: E.IsSolution u ↔ u in E.solSpace
  proof: Iff.rfl

中文:
定理 is_sol_iff_mem_solSpace
  条件: (u : 自然数 -> R)
  结论: E.IsSolution u ↔ u in E.solSpace
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem is_sol_iff_mem_solSpace (u : Nat -> R) : E.IsSolution u ↔ u in E.solSpace :=
  Iff.rfl

/--
Definition of `toInit` / `toInit` 的定义

English:
definition toInit
  signature: : E.solSpace ≃ₗ[R] Fin E.order -> R where
  body: (u : Nat -> R) x
  map_add' u v := by
    ext
    simp
  map_smul' a u := by
    ext
    simp
  invFun u := ⟨E.mkSol u, E.is_sol_mkSol u⟩
  left_inv u := by ext n; symm; apply E.eq_mk_of_is_sol_of_eq_init u.2; intro k; rfl
  right_inv u := funext_iff.mpr fun n => E.mkSol_eq_init u n

中文:
定义 toInit
  签名: : E.solSpace ≃ₗ[R] 有限集 E.order -> R where
  定义体: (u : Nat -> R) x
  map_add' u v := by
    ext
    simp
  map_smul' a u := by
    ext
    simp
  invFun u := ⟨E.mkSol u, E.is_sol_mkSol u⟩
  left_inv u := by ext n; symm; apply E.eq_mk_of_is_sol_of_eq_init u.2; intro k; rfl
  right_inv u := funext_iff.mpr fun n => E.mkSol_eq_init u n
-/
def toInit : E.solSpace ≃ₗ[R] Fin E.order -> R where
  toFun u x := (u : Nat -> R) x
  map_add' u v := by
    ext
    simp
  map_smul' a u := by
    ext
    simp
  invFun u := ⟨E.mkSol u, E.is_sol_mkSol u⟩
  left_inv u := by ext n; symm; apply E.eq_mk_of_is_sol_of_eq_init u.2; intro k; rfl
  right_inv u := funext_iff.mpr fun n => E.mkSol_eq_init u n

/--
theorem `mkSol_injective` / 定理 `mkSol_injective`

English:
theorem mkSol_injective
  statement: E.mkSol.Injective
  proof: Subtype.val_injective.comp E.toInit.symm.injective

中文:
定理 mkSol_injective
  结论: E.mkSol.单射
  证明: Subtype.val_injective.comp E.toInit.symm.injective

Depends on / 依赖: E.toInit.symm.injective, Subtype, Subtype.val_injective.comp, injective, toInit, val_injective
-/
theorem mkSol_injective : E.mkSol.Injective :=
  Subtype.val_injective.comp E.toInit.symm.injective

/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: : Module.Basis (Fin E.order) R E.solSpace
  body: .ofEquivFun E.toInit

中文:
定义 basis
  签名: : 模.基 (有限集 E.order) R E.solSpace
  定义体: .ofEquivFun E.toInit

Depends on / 依赖: E.toInit, ofEquivFun, toInit
-/
def basis : Module.Basis (Fin E.order) R E.solSpace :=
  .ofEquivFun E.toInit

/--
theorem `repr_basis_eq` / 定理 `repr_basis_eq`

English:
theorem repr_basis_eq
  given: (u : E.solSpace)
  proof: rfl

中文:
定理 repr_basis_eq
  条件: (u : E.solSpace)
  证明: rfl
-/
theorem repr_basis_eq (u : E.solSpace) :
    E.basis.repr u = .ofSupportFinite (u ∘ Fin.val) (Set.toFinite _) :=
  rfl

/-- The nth coordinate of a solution in the basis equals its nth value -/
@[simp]
/--
theorem `repr_basis_apply` / 定理 `repr_basis_apply`

English:
theorem repr_basis_apply
  given: (u : E.solSpace) (n : Fin E.order)
  statement: E.basis.repr u n = u.val n
  proof: rfl

中文:
定理 repr_basis_apply
  条件: (u : E.solSpace) (n : 有限集 E.order)
  结论: E.basis.repr u n = u.val n
  证明: rfl
-/
theorem repr_basis_apply (u : E.solSpace) (n : Fin E.order) : E.basis.repr u n = u.val n :=
  rfl

/--
theorem `eq_iff_eqOn_range_order` / 定理 `eq_iff_eqOn_range_order`

English:
theorem eq_iff_eqOn_range_order
  given: (u v : Nat -> R) (hu : E.IsSolution u) (hv : E.IsSolution v)
  proof: by
  replace hu : u in E.solSpace := (is_sol_iff_mem_solSpace _ _).mp hu
  replace hv : v in E.solSpace := (is_sol_iff_mem_solSpace _ _).mp hv
  rw [← Subtype.mk.injEq u hu v hv]; rw [← E.basis.repr.injective.eq_iff]
  constructor
  · exact fun h n hn => congr($h ⟨n, Finset.mem_range.mp hn⟩)
· exact

中文:
定理 eq_iff_eqOn_range_order
  条件: (u v : 自然数 -> R) (hu : E.IsSolution u) (hv : E.IsSolution v)
  证明: by
  replace hu : u in E.solSpace := (is_sol_iff_mem_solSpace _ _).mp hu
  replace hv : v in E.solSpace := (is_sol_iff_mem_solSpace _ _).mp hv
  rw [← Subtype.mk.injEq u hu v hv]; rw [← E.basis.repr.injective.eq_iff]
  constructor
  · exact fun h n hn => congr($h ⟨n, Finset.mem_range.mp hn⟩)
· exact

Depends on / 依赖: E.basis.repr.injective.eq_iff, E.solSpace, Finset, Finset.mem_range.mp, Finset.mem_range.mpr, Finsupp, Finsupp.ext, Subtype, Subtype.mk.injEq, eq_iff, injective, is_sol_iff_mem_solSpace, mem_range, n.prop, replace, solSpace
-/
theorem eq_iff_eqOn_range_order (u v : Nat -> R) (hu : E.IsSolution u) (hv : E.IsSolution v) :
    u = v ↔ Set.EqOn u v ↑(range E.order) := by
  replace hu : u in E.solSpace := (is_sol_iff_mem_solSpace _ _).mp hu
  replace hv : v in E.solSpace := (is_sol_iff_mem_solSpace _ _).mp hv
  rw [← Subtype.mk.injEq u hu v hv]; rw [← E.basis.repr.injective.eq_iff]
  constructor
  · exact fun h n hn => congr($h ⟨n, Finset.mem_range.mp hn⟩)
· exact fun h => Finsupp.ext fun n => h Finset.mem_range.mpr n.prop

@[deprecated (since := "2026-04-16")] alias sol_eq_of_eq_init := eq_iff_eqOn_range_order

/-! `E.tupleSucc` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
where `n := E.order`. This operation is quite useful for determining closed-form
solutions of `E`. -/

/--
Definition of `tupleSucc` / `tupleSucc` 的定义

English:
definition tupleSucc
  signature: : (Fin E.order -> R) ->ₗ[R] Fin E.order -> R where
  body: if h : (i : Nat) + 1 < E.order then X ⟨i + 1, h⟩ else ∑ i, E.coeffs i * X i
  map_add' x y := by
    ext i
    split_ifs with h <;> simp [h, mul_add, sum_add_distrib]
  map_smul' x y := by
    ext i
    split_ifs with h <;>
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, h, ↓reduceDIt

中文:
定义 tupleSucc
  签名: : (有限集 E.order -> R) ->ₗ[R] 有限集 E.order -> R where
  定义体: if h : (i : Nat) + 1 < E.order then X ⟨i + 1, h⟩ else ∑ i, E.coeffs i * X i
  map_add' x y := by
    ext i
    split_ifs with h <;> simp [h, mul_add, sum_add_distrib]
  map_smul' x y := by
    ext i
    split_ifs with h <;>
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, h, ↓reduceDIt

Depends on / 依赖: E.coeffs, E.order, coeffs
-/
def tupleSucc : (Fin E.order -> R) ->ₗ[R] Fin E.order -> R where
  toFun X i := if h : (i : Nat) + 1 < E.order then X ⟨i + 1, h⟩ else ∑ i, E.coeffs i * X i
  map_add' x y := by
    ext i
    split_ifs with h <;> simp [h, mul_add, sum_add_distrib]
  map_smul' x y := by
    ext i
    split_ifs with h <;>
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, h, ↓reduceDIte, mul_sum]
    exact sum_congr rfl fun x _ => by ac_rfl

end CommSemiring

section StrongRankCondition

-- note: `StrongRankCondition` is the same as `Nontrivial` on `CommRing`s, but that result,
-- `commRing_strongRankCondition`, is in a much later file.
variable {R : Type*} [CommRing R] [StrongRankCondition R] (E : LinearRecurrence R)

/--
theorem `solSpace_rank` / 定理 `solSpace_rank`

English:
theorem solSpace_rank
  statement: Module.rank R E.solSpace = E.order
  proof: by
  simp [rank_eq_card_basis E.basis]

中文:
定理 solSpace_rank
  结论: 模.rank R E.solSpace = E.order
  证明: by
  simp [rank_eq_card_basis E.basis]

Depends on / 依赖: E.basis, rank_eq_card_basis
-/
theorem solSpace_rank : Module.rank R E.solSpace = E.order := by
  simp [rank_eq_card_basis E.basis]

end StrongRankCondition

section CommRing

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

/--
Definition of `charPoly` / `charPoly` 的定义

English:
definition charPoly
  signature: : R[X]
  body: Polynomial.monomial E.order 1 - ∑ i : Fin E.order, Polynomial.monomial i (E.coeffs i)

@[simp]

中文:
定义 charPoly
  签名: : R[X]
  定义体: Polynomial.monomial E.order 1 - ∑ i : Fin E.order, Polynomial.monomial i (E.coeffs i)

@[simp]

Depends on / 依赖: E.coeffs, E.order, Polynomial, Polynomial.monomial, coeffs, monomial
-/
def charPoly : R[X] :=
  Polynomial.monomial E.order 1 - ∑ i : Fin E.order, Polynomial.monomial i (E.coeffs i)

@[simp]
/--
theorem `charPoly_degree_eq_order` / 定理 `charPoly_degree_eq_order`

English:
theorem charPoly_degree_eq_order
  given: [Nontrivial R]
  statement: (charPoly E).degree = E.order
  proof: by
  rw [charPoly]; rw [degree_sub_eq_left_of_degree_lt]
    <;> rw [degree_monomial E.order one_ne_zero]
  simp_rw [← C_mul_X_pow_eq_monomial]
  exact degree_sum_fin_lt E.coeffs

.Monic := by theorem charPoly_monic : charPoly E
  nontriviality R
  rw [Monic]; rw [leadingCoeff]; rw [natDegree_eq_of_

中文:
定理 charPoly_degree_eq_order
  条件: [非平凡 R]
  结论: (charPoly E).degree = E.order
  证明: by
  rw [charPoly]; rw [degree_sub_eq_left_of_degree_lt]
    <;> rw [degree_monomial E.order one_ne_zero]
  simp_rw [← C_mul_X_pow_eq_monomial]
  exact degree_sum_fin_lt E.coeffs

.Monic := by theorem charPoly_monic : charPoly E
  nontriviality R
  rw [Monic]; rw [leadingCoeff]; rw [natDegree_eq_of_

Depends on / 依赖: C_mul_X_pow_eq_monomial, E.coeffs, E.order, charPoly, coeffs, degree_monomial, degree_sub_eq_left_of_degree_lt, degree_sum_fin_lt, one_ne_zero, simp_rw
-/
theorem charPoly_degree_eq_order [Nontrivial R] : (charPoly E).degree = E.order := by
  rw [charPoly]; rw [degree_sub_eq_left_of_degree_lt]
    <;> rw [degree_monomial E.order one_ne_zero]
  simp_rw [← C_mul_X_pow_eq_monomial]
  exact degree_sum_fin_lt E.coeffs

.Monic := by theorem charPoly_monic : charPoly E
  nontriviality R
  rw [Monic]; rw [leadingCoeff]; rw [natDegree_eq_of_degree_eq_some <| charPoly_degree_eq_order _]; rw [charPoly]; rw [coeff_sub]; rw [coeff_monomial_same]; rw [finsetSum_coeff]; rw [sub_eq_self]
  refine sum_eq_zero fun _ _ => coeff_eq_zero_of_degree_lt ?_
  grw [degree_monomial_le]
  simp

/--
theorem `geom_sol_iff_root_charPoly` / 定理 `geom_sol_iff_root_charPoly`

English:
theorem geom_sol_iff_root_charPoly
  given: (q : R)
  proof: by
  rw [charPoly]; rw [Polynomial.IsRoot.def]; rw [Polynomial.eval]
  simp only [Polynomial.eval₂_finsetSum, one_mul, RingHom.id_apply, Polynomial.eval₂_monomial,
    Polynomial.eval₂_sub]
  constructor
  · intro h
    simpa [sub_eq_zero] using h 0
  · intro h n
    simp only [pow_add, sub_eq_zero.

中文:
定理 geom_sol_iff_root_charPoly
  条件: (q : R)
  证明: by
  rw [charPoly]; rw [Polynomial.IsRoot.def]; rw [Polynomial.eval]
  simp only [Polynomial.eval₂_finsetSum, one_mul, RingHom.id_apply, Polynomial.eval₂_monomial,
    Polynomial.eval₂_sub]
  constructor
  · intro h
    simpa [sub_eq_zero] using h 0
  · intro h n
    simp only [pow_add, sub_eq_zero.

Depends on / 依赖: IsRoot, Polynomial, Polynomial.IsRoot.def, Polynomial.eval, RingHom, RingHom.id_apply, charPoly, id_apply, mul_sum, one_mul, pow_add, sub_eq_zero, sub_eq_zero.mp, sum_congr
-/
theorem geom_sol_iff_root_charPoly (q : R) :
    (E.IsSolution fun n => q ^ n) ↔ E.charPoly.IsRoot q := by
  rw [charPoly]; rw [Polynomial.IsRoot.def]; rw [Polynomial.eval]
  simp only [Polynomial.eval₂_finsetSum, one_mul, RingHom.id_apply, Polynomial.eval₂_monomial,
    Polynomial.eval₂_sub]
  constructor
  · intro h
    simpa [sub_eq_zero] using h 0
  · intro h n
    simp only [pow_add, sub_eq_zero.mp h, mul_sum]
    exact sum_congr rfl fun _ _ => by ring

end CommRing

end LinearRecurrence
