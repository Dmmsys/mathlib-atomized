/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Logic.Function.Basic

/-!
# Very basic algebraic operations on pi types

This file provides very basic algebraic operations on functions.
-/

@[expose] public section

assert_not_exists Monoid Preorder

open Function

variable {ι ι' α β : Type*} {G M N O : ι -> Type*}

namespace Pi
variable [forall i, One (M i)] [forall i, One (N i)] [forall i, One (O i)] [DecidableEq ι] {i : ι} {x : M i}

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive /-- The function supported at `i`, with value `x` there, and `0` elsewhere. -/]
/--
Definition of `mulSingle` / `mulSingle` 的定义

English:
definition mulSingle
  signature: (i : ι) (x : M i)
  body: Function.update 1 i x

@[to_additive (attr := simp)]

中文:
定义 mulSingle
  签名: (i : ι) (x : M i)
  定义体: Function.update 1 i x

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.update, update
-/
def mulSingle (i : ι) (x : M i) : forall j, M j := Function.update 1 i x

@[to_additive (attr := simp)]
/--
lemma `mulSingle_eq_same` / 引理 `mulSingle_eq_same`

English:
lemma mulSingle_eq_same
  given: (i : ι) (x : M i)
  statement: mulSingle i x i = x
  proof: Function.update_self i x _

@[to_additive (attr := simp)]

中文:
引理 mulSingle_eq_same
  条件: (i : ι) (x : M i)
  结论: mulSingle i x i = x
  证明: Function.update_self i x _

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.update_self, update_self
-/
lemma mulSingle_eq_same (i : ι) (x : M i) : mulSingle i x i = x := Function.update_self i x _

@[to_additive (attr := simp)]
/--
lemma `mulSingle_eq_of_ne` / 引理 `mulSingle_eq_of_ne`

English:
lemma mulSingle_eq_of_ne
  given: {i i' : ι} (h : i' != i) (x : M i)
  statement: mulSingle i x i' = 1
  proof: Function.update_of_ne h x _

中文:
引理 mulSingle_eq_of_ne
  条件: {i i' : ι} (h : i' != i) (x : M i)
  结论: mulSingle i x i' = 1
  证明: Function.update_of_ne h x _

Depends on / 依赖: Function, Function.update_of_ne, update_of_ne
-/
lemma mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : M i) : mulSingle i x i' = 1 :=
  Function.update_of_ne h x _

/-- Abbreviation for `mulSingle_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[to_additive (attr := simp)
  /-- Abbreviation for `single_eq_of_ne h.symm`, for ease of use by `simp`. -/]
/--
lemma `mulSingle_eq_of_ne'` / 引理 `mulSingle_eq_of_ne'`

English:
lemma mulSingle_eq_of_ne'
  given: {i i' : ι} (h : i != i') (x : M i)
  statement: mulSingle i x i' = 1
  proof: mulSingle_eq_of_ne h.symm x

@[to_additive (attr := simp)]

中文:
引理 mulSingle_eq_of_ne'
  条件: {i i' : ι} (h : i != i') (x : M i)
  结论: mulSingle i x i' = 1
  证明: mulSingle_eq_of_ne h.symm x

@[to_additive (attr := simp)]

Depends on / 依赖: h.symm, mulSingle_eq_of_ne
-/
lemma mulSingle_eq_of_ne' {i i' : ι} (h : i != i') (x : M i) : mulSingle i x i' = 1 :=
  mulSingle_eq_of_ne h.symm x

@[to_additive (attr := simp)]
/--
lemma `mulSingle_one` / 引理 `mulSingle_one`

English:
lemma mulSingle_one
  given: (i : ι)
  statement: mulSingle i (1 : M i) = 1
  proof: Function.update_eq_self _ _

@[to_additive (attr := simp)]

中文:
引理 mulSingle_one
  条件: (i : ι)
  结论: mulSingle i (1 : M i) = 1
  证明: Function.update_eq_self _ _

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.update_eq_self, update_eq_self
-/
lemma mulSingle_one (i : ι) : mulSingle i (1 : M i) = 1 := Function.update_eq_self _ _

@[to_additive (attr := simp)]
/--
lemma `mulSingle_eq_one_iff` / 引理 `mulSingle_eq_one_iff`

English:
lemma mulSingle_eq_one_iff
  statement: mulSingle i x = 1 ↔ x = 1
  proof: by
  refine ⟨fun h => ?_, fun h => h.symm ▸ mulSingle_one i⟩
  rw [← mulSingle_eq_same i x]; rw [h]; rw [one_apply]

@[to_additive]

中文:
引理 mulSingle_eq_one_iff
  结论: mulSingle i x = 1 ↔ x = 1
  证明: by
  refine ⟨fun h => ?_, fun h => h.symm ▸ mulSingle_one i⟩
  rw [← mulSingle_eq_same i x]; rw [h]; rw [one_apply]

@[to_additive]

Depends on / 依赖: h.symm, mulSingle_eq_same, mulSingle_one, one_apply
-/
lemma mulSingle_eq_one_iff : mulSingle i x = 1 ↔ x = 1 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ mulSingle_one i⟩
  rw [← mulSingle_eq_same i x]; rw [h]; rw [one_apply]

@[to_additive]
/--
lemma `mulSingle_ne_one_iff` / 引理 `mulSingle_ne_one_iff`

English:
lemma mulSingle_ne_one_iff
  statement: mulSingle i x != 1 ↔ x != 1
  proof: mulSingle_eq_one_iff.ne

@[to_additive]

中文:
引理 mulSingle_ne_one_iff
  结论: mulSingle i x != 1 ↔ x != 1
  证明: mulSingle_eq_one_iff.ne

@[to_additive]

Depends on / 依赖: mulSingle_eq_one_iff, mulSingle_eq_one_iff.ne
-/
lemma mulSingle_ne_one_iff : mulSingle i x != 1 ↔ x != 1 :=
  mulSingle_eq_one_iff.ne

@[to_additive]
/--
lemma `apply_mulSingle` / 引理 `apply_mulSingle`

English:
lemma apply_mulSingle
  given: (f' : forall i, M i -> N i) (hf' : forall i, f' i 1 = 1) (i : ι) (x : M i) (j : ι)
  proof: by
  simpa only [Pi.one_apply, hf', mulSingle] using! Function.apply_update f' 1 i x j

@[to_additive apply_single₂]

中文:
引理 apply_mulSingle
  条件: (f' : 对任意 i, M i -> N i) (hf' : 对任意 i, f' i 1 = 1) (i : ι) (x : M i) (j : ι)
  证明: by
  simpa only [Pi.one_apply, hf', mulSingle] using! Function.apply_update f' 1 i x j

@[to_additive apply_single₂]

Depends on / 依赖: Function, Function.apply_update, Pi.one_apply, apply_update, mulSingle, one_apply
-/
lemma apply_mulSingle (f' : forall i, M i -> N i) (hf' : forall i, f' i 1 = 1) (i : ι) (x : M i) (j : ι) :
    f' j (mulSingle i x j) = mulSingle i (f' i x) j := by
  simpa only [Pi.one_apply, hf', mulSingle] using! Function.apply_update f' 1 i x j

@[to_additive apply_single₂]
/--
lemma `apply_mulSingle₂` / 引理 `apply_mulSingle₂`

English:
lemma apply_mulSingle₂
  statement: (f' : forall i, M i -> N i -> O i) (hf' : forall i, f' i 1 1 = 1) (i : ι)
  proof: by
  by_cases h : j = i
  · subst h
    simp only [mulSingle_eq_same]
  · simp only [mulSingle_eq_of_ne h, hf']

@[to_additive]

中文:
引理 apply_mulSingle₂
  结论: (f' : 对任意 i, M i -> N i -> O i) (hf' : 对任意 i, f' i 1 1 = 1) (i : ι)
  证明: by
  by_cases h : j = i
  · subst h
    simp only [mulSingle_eq_same]
  · simp only [mulSingle_eq_of_ne h, hf']

@[to_additive]

Depends on / 依赖: mulSingle_eq_of_ne, mulSingle_eq_same
-/
lemma apply_mulSingle₂ (f' : forall i, M i -> N i -> O i) (hf' : forall i, f' i 1 1 = 1) (i : ι)
    (x : M i) (y : N i) (j : ι) :
    f' j (mulSingle i x j) (mulSingle i y j) = mulSingle i (f' i x y) j := by
  by_cases h : j = i
  · subst h
    simp only [mulSingle_eq_same]
  · simp only [mulSingle_eq_of_ne h, hf']

@[to_additive]
/--
lemma `mulSingle_op` / 引理 `mulSingle_op`

English:
lemma mulSingle_op
  given: (op : forall i, M i -> N i) (h : forall i, op i 1 = 1) (i : ι) (x : M i)
  proof: .symm funext apply_mulSingle op h i x

@[to_additive]

中文:
引理 mulSingle_op
  条件: (op : 对任意 i, M i -> N i) (h : 对任意 i, op i 1 = 1) (i : ι) (x : M i)
  证明: .symm funext apply_mulSingle op h i x

@[to_additive]

Depends on / 依赖: apply_mulSingle
-/
lemma mulSingle_op (op : forall i, M i -> N i) (h : forall i, op i 1 = 1) (i : ι) (x : M i) :
    mulSingle i (op i x) = fun j => op j (mulSingle i x j) :=
.symm funext apply_mulSingle op h i x

@[to_additive]
/--
lemma `mulSingle_op₂` / 引理 `mulSingle_op₂`

English:
lemma mulSingle_op₂
  statement: (op : forall i, M i -> N i -> O i) (h : forall i, op i 1 1 = 1) (i : ι) (x : M i)
  proof: .symm funext apply_mulSingle₂ op h i x y

@[to_additive]

中文:
引理 mulSingle_op₂
  结论: (op : 对任意 i, M i -> N i -> O i) (h : 对任意 i, op i 1 1 = 1) (i : ι) (x : M i)
  证明: .symm funext apply_mulSingle₂ op h i x y

@[to_additive]
-/
lemma mulSingle_op₂ (op : forall i, M i -> N i -> O i) (h : forall i, op i 1 1 = 1) (i : ι) (x : M i)
    (y : N i) : mulSingle i (op i x y) = fun j => op j (mulSingle i x j) (mulSingle i y j) :=
.symm funext apply_mulSingle₂ op h i x y

@[to_additive]
/--
lemma `mulSingle_injective` / 引理 `mulSingle_injective`

English:
lemma mulSingle_injective
  given: (i : ι)
  statement: Function.Injective (mulSingle i : M i -> forall i, M i)
  proof: Function.update_injective _ i

@[to_additive (attr := simp)]

中文:
引理 mulSingle_injective
  条件: (i : ι)
  结论: Function.Injective (mulSingle i : M i -> 对任意 i, M i)
  证明: Function.update_injective _ i

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.update_injective, update_injective
-/
lemma mulSingle_injective (i : ι) : Function.Injective (mulSingle i : M i -> forall i, M i) :=
  Function.update_injective _ i

@[to_additive (attr := simp)]
/--
lemma `mulSingle_inj` / 引理 `mulSingle_inj`

English:
lemma mulSingle_inj
  given: (i : ι) {x y : M i}
  statement: mulSingle i x = mulSingle i y ↔ x = y
  proof: (mulSingle_injective _).eq_iff

中文:
引理 mulSingle_inj
  条件: (i : ι) {x y : M i}
  结论: mulSingle i x = mulSingle i y ↔ x = y
  证明: (mulSingle_injective _).eq_iff

Depends on / 依赖: eq_iff, mulSingle_injective
-/
lemma mulSingle_inj (i : ι) {x y : M i} : mulSingle i x = mulSingle i y ↔ x = y :=
  (mulSingle_injective _).eq_iff

variable {M : Type*} [One M]

/--
A congruence lemma for `Pi.mulSingle`, specialized for the non-dependent case. Without this,
`simp` can't rewrite in the first and third argument (`i` and `j`) because of dependence.
See also https://github.com/leanprover/lean4/issues/12478.
-/
@[to_additive (attr := congr) /--
A congruence lemma for `Pi.single`, specialized for the non-dependent case. Without this,
`simp` can't rewrite in the first and third argument (`i` and `j`) because of dependence.
See also https://github.com/leanprover/lean4/issues/12478.
-/]
/--
lemma `mulSingle_congr` / 引理 `mulSingle_congr`

English:
lemma mulSingle_congr
  statement: {i₁ i₂ : ι} (hi : i₁ = i₂)
  proof: update_congr rfl hi hx hj

中文:
引理 mulSingle_congr
  结论: {i₁ i₂ : ι} (hi : i₁ = i₂)
  证明: update_congr rfl hi hx hj

Depends on / 依赖: update_congr
-/
lemma mulSingle_congr {i₁ i₂ : ι} (hi : i₁ = i₂)
    {x₁ x₂ : M} (hx : x₁ = x₂) {j₁ j₂ : ι} (hj : j₁ = j₂) :
    (mulSingle i₁ x₁ : ι -> M) j₁ = (mulSingle i₂ x₂ : ι -> M) j₂ :=
  update_congr rfl hi hx hj

/-- On non-dependent functions, `Pi.mulSingle` can be expressed as an `ite` -/
@[to_additive (attr := grind =)
  /-- On non-dependent functions, `Pi.single` can be expressed as an `ite` -/]
/--
lemma `mulSingle_apply` / 引理 `mulSingle_apply`

English:
lemma mulSingle_apply
  given: (i : ι) (x : M) (i' : ι)
  proof: Function.update_apply (1 : ι -> M) i x i'

中文:
引理 mulSingle_apply
  条件: (i : ι) (x : M) (i' : ι)
  证明: Function.update_apply (1 : ι -> M) i x i'

Depends on / 依赖: Function, Function.update_apply, update_apply
-/
lemma mulSingle_apply (i : ι) (x : M) (i' : ι) :
    (mulSingle i x : ι -> M) i' = if i' = i then x else 1 :=
  Function.update_apply (1 : ι -> M) i x i'

-- Porting note: added type ascription (_ : ι → M)
/-- On non-dependent functions, `Pi.mulSingle` is symmetric in the two indices. -/
@[to_additive /-- On non-dependent functions, `Pi.single` is symmetric in the two indices. -/]
/--
lemma `mulSingle_comm` / 引理 `mulSingle_comm`

English:
lemma mulSingle_comm
  given: (i : ι) (x : M) (j : ι)
  proof: by simp [mulSingle_apply, eq_comm]

中文:
引理 mulSingle_comm
  条件: (i : ι) (x : M) (j : ι)
  证明: by simp [mulSingle_apply, eq_comm]

Depends on / 依赖: eq_comm, mulSingle_apply
-/
lemma mulSingle_comm (i : ι) (x : M) (j : ι) :
    (mulSingle i x : ι -> M) j = (mulSingle j x : ι -> M) i := by simp [mulSingle_apply, eq_comm]

variable [DecidableEq ι']

@[to_additive (attr := simp)]
/--
theorem `curry_mulSingle` / 定理 `curry_mulSingle`

English:
theorem curry_mulSingle
  given: (i : ι × ι') (b : M)
  proof: curry_update _ _ _

@[to_additive (attr := simp)]

中文:
定理 curry_mulSingle
  条件: (i : ι × ι') (b : M)
  证明: curry_update _ _ _

@[to_additive (attr := simp)]

Depends on / 依赖: curry_update
-/
theorem curry_mulSingle (i : ι × ι') (b : M) :
    curry (Pi.mulSingle i b) = Pi.mulSingle i.1 (Pi.mulSingle i.2 b) :=
  curry_update _ _ _

@[to_additive (attr := simp)]
/--
theorem `uncurry_mulSingle_mulSingle` / 定理 `uncurry_mulSingle_mulSingle`

English:
theorem uncurry_mulSingle_mulSingle
  given: (i : ι) (i' : ι') (b : M)
  proof: uncurry_update_update _ _ _ _

中文:
定理 uncurry_mulSingle_mulSingle
  条件: (i : ι) (i' : ι') (b : M)
  证明: uncurry_update_update _ _ _ _

Depends on / 依赖: uncurry_update_update
-/
theorem uncurry_mulSingle_mulSingle (i : ι) (i' : ι') (b : M) :
    uncurry (Pi.mulSingle i (Pi.mulSingle i' b)) = Pi.mulSingle (i, i') b :=
  uncurry_update_update _ _ _ _

end Pi
