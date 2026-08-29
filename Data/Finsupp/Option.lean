/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.Module.Defs

/-!
# Operations on `Finsupp`s with an `Option` domain

Similar to how `Finsupp.cons` and `Finsupp.tail` construct
an object of type `Fin (n + 1) →₀ M` from a map `Fin n →₀ M` and vice versa,
we define `Finsupp.optionElim` and `Finsupp.some`
to construct `Option α →₀ M` from a map α →₀ M, and vice versa.

As functions, these behave as `Option.elim'`, and as an application of `some` hence the names.

We prove a variety of API lemmas, see `Mathlib/Data/Finsupp/Fin.lean` for comparison.

## Main declarations

* `Finsupp.some`: restrict a finitely supported function on `Option α` to a finitely supported
  function on `α`.
* `Finsupp.optionElim`: extend a finitely supported function on `α`
  to a finitely supported function on `Option α`, provided a default value for `none`.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

-/

@[expose] public section


noncomputable section

open Finset Function

variable {α M N R : Type*}

namespace Finsupp

section Option

section Zero

variable [Zero M]

/--
Definition of `some` / `some` 的定义

English:
definition some
  signature: (f : Option α ->₀ M)
  body: f.comapDomain Option.some fun _ => by simp

@[simp]

中文:
定义 some
  签名: (f : 选项类型 α ->₀ M)
  定义体: f.comapDomain Option.some fun _ => by simp

@[simp]

Depends on / 依赖: Option.some, comapDomain, f.comapDomain
-/
def some (f : Option α ->₀ M) : α ->₀ M :=
  f.comapDomain Option.some fun _ => by simp

@[simp]
/--
theorem `some_apply` / 定理 `some_apply`

English:
theorem some_apply
  given: (f : Option α ->₀ M) (a : α)
  statement: f.some a = f (Option.some a)
  proof: rfl

@[simp]

中文:
定理 some_apply
  条件: (f : 选项类型 α ->₀ M) (a : α)
  结论: f.some a = f (选项类型.some a)
  证明: rfl

@[simp]
-/
theorem some_apply (f : Option α ->₀ M) (a : α) : f.some a = f (Option.some a) :=
  rfl

@[simp]
/--
theorem `some_zero` / 定理 `some_zero`

English:
theorem some_zero
  statement: (0 : Option α ->₀ M).some = 0
  proof: by
  ext
  simp

中文:
定理 some_zero
  结论: (0 : 选项类型 α ->₀ M).some = 0
  证明: by
  ext
  simp
-/
theorem some_zero : (0 : Option α ->₀ M).some = 0 := by
  ext
  simp

end Zero

@[simp]
/--
theorem `some_add` / 定理 `some_add`

English:
theorem some_add
  given: [AddZeroClass M] (f g : Option α ->₀ M)
  statement: (f + g).some = f.some + g.some
  proof: by
  ext
  simp

中文:
定理 some_add
  条件: [加法零类 M] (f g : 选项类型 α ->₀ M)
  结论: (f + g).some = f.some + g.some
  证明: by
  ext
  simp
-/
theorem some_add [AddZeroClass M] (f g : Option α ->₀ M) : (f + g).some = f.some + g.some := by
  ext
  simp

section Zero

variable [Zero M]

@[simp]
/--
theorem `some_single_none` / 定理 `some_single_none`

English:
theorem some_single_none
  given: (m : M)
  statement: (single none m : Option α ->₀ M).some = 0
  proof: by
  ext
  simp

@[simp]

中文:
定理 some_single_none
  条件: (m : M)
  结论: (single none m : 选项类型 α ->₀ M).some = 0
  证明: by
  ext
  simp

@[simp]
-/
theorem some_single_none (m : M) : (single none m : Option α ->₀ M).some = 0 := by
  ext
  simp

@[simp]
/--
theorem `some_single_some` / 定理 `some_single_some`

English:
theorem some_single_some
  given: (a : α) (m : M)
  proof: by
  classical
    ext b
    simp [single_apply]

中文:
定理 some_single_some
  条件: (a : α) (m : M)
  证明: by
  classical
    ext b
    simp [single_apply]

Depends on / 依赖: classical, single_apply
-/
theorem some_single_some (a : α) (m : M) :
    (single (Option.some a) m : Option α ->₀ M).some = single a m := by
  classical
    ext b
    simp [single_apply]

/--
lemma `some_embDomain_some` / 引理 `some_embDomain_some`

English:
lemma some_embDomain_some
  given: (f : α ->₀ M)
  statement: (f.embDomain .some).some = f
  proof: by
  ext; rw [some_apply]; exact embDomain_apply_self _ _ _

中文:
引理 some_embDomain_some
  条件: (f : α ->₀ M)
  结论: (f.embDomain .some).some = f
  证明: by
  ext; rw [some_apply]; exact embDomain_apply_self _ _ _
-/
@[simp] lemma some_embDomain_some (f : α ->₀ M) : (f.embDomain .some).some = f := by
  ext; rw [some_apply]; exact embDomain_apply_self _ _ _

/--
lemma `embDomain_some_none` / 引理 `embDomain_some_none`

English:
lemma embDomain_some_none
  given: (f : α ->₀ M)
  statement: f.embDomain .some .none = 0
  proof: embDomain_of_notMem_range _ _ _ (by simp)

@[simp]

中文:
引理 embDomain_some_none
  条件: (f : α ->₀ M)
  结论: f.embDomain .some .none = 0
  证明: embDomain_of_notMem_range _ _ _ (by simp)

@[simp]
-/
@[simp] lemma embDomain_some_none (f : α ->₀ M) : f.embDomain .some .none = 0 :=
  embDomain_of_notMem_range _ _ _ (by simp)

@[simp]
/--
theorem `embDomain_some_some` / 定理 `embDomain_some_some`

English:
theorem embDomain_some_some
  given: (f : α ->₀ M) (x)
  statement: f.embDomain .some (.some x) = f x
  proof: by
  simp [← Function.Embedding.some_apply]

@[simp]

中文:
定理 embDomain_some_some
  条件: (f : α ->₀ M) (x)
  结论: f.embDomain .some (.some x) = f x
  证明: by
  simp [← Function.Embedding.some_apply]

@[simp]

Depends on / 依赖: Embedding, Function, Function.Embedding.some_apply, some_apply
-/
theorem embDomain_some_some (f : α ->₀ M) (x) : f.embDomain .some (.some x) = f x := by
  simp [← Function.Embedding.some_apply]

@[simp]
/--
theorem `some_update_none` / 定理 `some_update_none`

English:
theorem some_update_none
  given: (f : Option α ->₀ M) (a : M)
  proof: by
  ext
  simp [Finsupp.update]

中文:
定理 some_update_none
  条件: (f : 选项类型 α ->₀ M) (a : M)
  证明: by
  ext
  simp [Finsupp.update]

Depends on / 依赖: Finsupp, Finsupp.update, update
-/
theorem some_update_none (f : Option α ->₀ M) (a : M) :
    (f.update none a).some = f.some := by
  ext
  simp [Finsupp.update]

/-- `Finsupp`s from `Option` are equivalent to
pairs of an element and a `Finsupp` on the original type. -/
@[simps]
noncomputable
/--
Definition of `optionEquiv` / `optionEquiv` 的定义

English:
definition optionEquiv
  signature: : (Option α ->₀ M) ≃ M × (α ->₀ M) where
  body: (P none, P.some)
  invFun P := (P.2.embDomain .some).update none P.1
  left_inv P := by ext (_ | a) <;> simp [Finsupp.update]
  right_inv P := by ext <;> simp [Finsupp.update]

中文:
定义 optionEquiv
  签名: : (选项类型 α ->₀ M) ≃ M × (α ->₀ M) where
  定义体: (P none, P.some)
  invFun P := (P.2.embDomain .some).update none P.1
  left_inv P := by ext (_ | a) <;> simp [Finsupp.update]
  right_inv P := by ext <;> simp [Finsupp.update]

Depends on / 依赖: P.some
-/
def optionEquiv : (Option α ->₀ M) ≃ M × (α ->₀ M) where
  toFun P := (P none, P.some)
  invFun P := (P.2.embDomain .some).update none P.1
  left_inv P := by ext (_ | a) <;> simp [Finsupp.update]
  right_inv P := by ext <;> simp [Finsupp.update]

/--
Definition of `optionElim` / `optionElim` 的定义

English:
definition optionElim
  signature: (y : M) (f : α ->₀ M)
  body: optionEquiv.invFun (y, f)

中文:
定义 optionElim
  签名: (y : M) (f : α ->₀ M)
  定义体: optionEquiv.invFun (y, f)

Depends on / 依赖: invFun, optionEquiv, optionEquiv.invFun
-/
def optionElim (y : M) (f : α ->₀ M) : Option α ->₀ M :=
  optionEquiv.invFun (y, f)

/--
lemma `optionElim_apply_none` / 引理 `optionElim_apply_none`

English:
lemma optionElim_apply_none
  given: (y : M) (f : α ->₀ M)
  statement: f.optionElim y none = y
  proof: by
  classical
  simp [optionElim]

中文:
引理 optionElim_apply_none
  条件: (y : M) (f : α ->₀ M)
  结论: f.optionElim y none = y
  证明: by
  classical
  simp [optionElim]

Depends on / 依赖: classical, optionElim
-/
lemma optionElim_apply_none (y : M) (f : α ->₀ M) : f.optionElim y none = y := by
  classical
  simp [optionElim]

/--
lemma `optionElim_apply_some` / 引理 `optionElim_apply_some`

English:
lemma optionElim_apply_some
  given: (y : M) (f : α ->₀ M) (x : α)
  proof: by
  classical
  simp [optionElim]

@[simp]

中文:
引理 optionElim_apply_some
  条件: (y : M) (f : α ->₀ M) (x : α)
  证明: by
  classical
  simp [optionElim]

@[simp]

Depends on / 依赖: classical, optionElim
-/
lemma optionElim_apply_some (y : M) (f : α ->₀ M) (x : α) :
    f.optionElim y (Option.some x) = f x := by
  classical
  simp [optionElim]

@[simp]
/--
lemma `optionElim_apply_eq_elim` / 引理 `optionElim_apply_eq_elim`

English:
lemma optionElim_apply_eq_elim
  given: (y : M) (f : α ->₀ M) (a : Option α)
  proof: by
  cases a with
  | none => exact optionElim_apply_none y f
  | some x => simp only [optionElim_apply_some, Option.elim_some]

中文:
引理 optionElim_apply_eq_elim
  条件: (y : M) (f : α ->₀ M) (a : 选项类型 α)
  证明: by
  cases a with
  | none => exact optionElim_apply_none y f
  | some x => simp only [optionElim_apply_some, Option.elim_some]

Depends on / 依赖: Option.elim_some, elim_some, optionElim_apply_none, optionElim_apply_some
-/
lemma optionElim_apply_eq_elim (y : M) (f : α ->₀ M) (a : Option α) :
    f.optionElim y a = a.elim y f := by
  cases a with
  | none => exact optionElim_apply_none y f
  | some x => simp only [optionElim_apply_some, Option.elim_some]

/--
lemma `optionElim_eq_elim'` / 引理 `optionElim_eq_elim'`

English:
lemma optionElim_eq_elim'
  given: (y : M) (f : α ->₀ M) (a : Option α)
  proof: by
  rw [optionElim_apply_eq_elim]; rw [Option.elim'_eq_elim]

@[simp]

中文:
引理 optionElim_eq_elim'
  条件: (y : M) (f : α ->₀ M) (a : 选项类型 α)
  证明: by
  rw [optionElim_apply_eq_elim]; rw [Option.elim'_eq_elim]

@[simp]

Depends on / 依赖: Option.elim, _eq_elim, optionElim_apply_eq_elim
-/
lemma optionElim_eq_elim' (y : M) (f : α ->₀ M) (a : Option α) :
    optionElim y f a = Option.elim' y f a := by
  rw [optionElim_apply_eq_elim]; rw [Option.elim'_eq_elim]

@[simp]
/--
lemma `some_optionElim` / 引理 `some_optionElim`

English:
lemma some_optionElim
  given: (y : M) (f : α ->₀ M)
  statement: (f.optionElim y).some = f
  proof: by
  ext
  simp

@[simp]

中文:
引理 some_optionElim
  条件: (y : M) (f : α ->₀ M)
  结论: (f.optionElim y).some = f
  证明: by
  ext
  simp

@[simp]
-/
lemma some_optionElim (y : M) (f : α ->₀ M) : (f.optionElim y).some = f := by
  ext
  simp

@[simp]
/--
lemma `optionElim_some` / 引理 `optionElim_some`

English:
lemma optionElim_some
  given: (f : Option α ->₀ M)
  statement: f.some.optionElim (f none) = f
  proof: by
  ext a
  cases a
  · rw [optionElim_apply_none]
  · simp

@[simp]

中文:
引理 optionElim_some
  条件: (f : 选项类型 α ->₀ M)
  结论: f.some.optionElim (f none) = f
  证明: by
  ext a
  cases a
  · rw [optionElim_apply_none]
  · simp

@[simp]

Depends on / 依赖: optionElim_apply_none
-/
lemma optionElim_some (f : Option α ->₀ M) : f.some.optionElim (f none) = f := by
  ext a
  cases a
  · rw [optionElim_apply_none]
  · simp

@[simp]
/--
theorem `optionElim_zero` / 定理 `optionElim_zero`

English:
theorem optionElim_zero
  given: (y : M)
  statement: (0 : α ->₀ M).optionElim y = single none y
  proof: by
  ext a
  cases a
  · simp
  · simp

中文:
定理 optionElim_zero
  条件: (y : M)
  结论: (0 : α ->₀ M).optionElim y = single none y
  证明: by
  ext a
  cases a
  · simp
  · simp
-/
theorem optionElim_zero (y : M) : (0 : α ->₀ M).optionElim y = single none y := by
  ext a
  cases a
  · simp
  · simp

/--
theorem `optionElim_ne_zero_of_left` / 定理 `optionElim_ne_zero_of_left`

English:
theorem optionElim_ne_zero_of_left
  given: (y : M) (f : α ->₀ M) (h : y != 0)
  statement: f.optionElim y != 0
  proof: by
  contrapose h with c
  have : f.optionElim y none = (0 : Option α ->₀ M) none := by
    rw [c]
  simp only [optionElim_apply_eq_elim, Option.elim_none, coe_zero, Pi.zero_apply] at this
  exact this

中文:
定理 optionElim_ne_zero_of_left
  条件: (y : M) (f : α ->₀ M) (h : y != 0)
  结论: f.optionElim y != 0
  证明: by
  contrapose h with c
  have : f.optionElim y none = (0 : Option α ->₀ M) none := by
    rw [c]
  simp only [optionElim_apply_eq_elim, Option.elim_none, coe_zero, Pi.zero_apply] at this
  exact this

Depends on / 依赖: Option.elim_none, Pi.zero_apply, coe_zero, contrapose, elim_none, f.optionElim, optionElim, optionElim_apply_eq_elim, zero_apply
-/
theorem optionElim_ne_zero_of_left (y : M) (f : α ->₀ M) (h : y != 0) : f.optionElim y != 0 := by
  contrapose h with c
  have : f.optionElim y none = (0 : Option α ->₀ M) none := by
    rw [c]
  simp only [optionElim_apply_eq_elim, Option.elim_none, coe_zero, Pi.zero_apply] at this
  exact this

/--
theorem `optionElim_ne_zero_of_right` / 定理 `optionElim_ne_zero_of_right`

English:
theorem optionElim_ne_zero_of_right
  given: (y : M) (f : α ->₀ M) (h : f != 0)
  statement: f.optionElim y != 0
  proof: by
  contrapose h with c
  ext a
  have : f.optionElim y (Option.some a) = (0 : Option α ->₀ M) (Option.some a) := by
    rw [c]
  simp only [optionElim_apply_eq_elim, Option.elim_some, coe_zero, Pi.zero_apply] at this
  exact this

中文:
定理 optionElim_ne_zero_of_right
  条件: (y : M) (f : α ->₀ M) (h : f != 0)
  结论: f.optionElim y != 0
  证明: by
  contrapose h with c
  ext a
  have : f.optionElim y (Option.some a) = (0 : Option α ->₀ M) (Option.some a) := by
    rw [c]
  simp only [optionElim_apply_eq_elim, Option.elim_some, coe_zero, Pi.zero_apply] at this
  exact this

Depends on / 依赖: Option.elim_some, Option.some, Pi.zero_apply, coe_zero, contrapose, elim_some, f.optionElim, optionElim, optionElim_apply_eq_elim, zero_apply
-/
theorem optionElim_ne_zero_of_right (y : M) (f : α ->₀ M) (h : f != 0) : f.optionElim y != 0 := by
  contrapose h with c
  ext a
  have : f.optionElim y (Option.some a) = (0 : Option α ->₀ M) (Option.some a) := by
    rw [c]
  simp only [optionElim_apply_eq_elim, Option.elim_some, coe_zero, Pi.zero_apply] at this
  exact this

/--
theorem `optionElim_ne_zero_iff` / 定理 `optionElim_ne_zero_iff`

English:
theorem optionElim_ne_zero_iff
  given: (y : M) (f : α ->₀ M)
  proof: by
  constructor
  · intro h
    contrapose! h
    rcases h with ⟨rfl, rfl⟩
    rw [optionElim_zero]; rw [single_zero]
  · intro h
    cases h with
    | inl h => exact optionElim_ne_zero_of_right y f h
    | inr h => exact optionElim_ne_zero_of_left y f h

中文:
定理 optionElim_ne_zero_iff
  条件: (y : M) (f : α ->₀ M)
  证明: by
  constructor
  · intro h
    contrapose! h
    rcases h with ⟨rfl, rfl⟩
    rw [optionElim_zero]; rw [single_zero]
  · intro h
    cases h with
    | inl h => exact optionElim_ne_zero_of_right y f h
    | inr h => exact optionElim_ne_zero_of_left y f h

Depends on / 依赖: contrapose, optionElim_ne_zero_of_left, optionElim_ne_zero_of_right, optionElim_zero, single_zero
-/
theorem optionElim_ne_zero_iff (y : M) (f : α ->₀ M) :
    f.optionElim y != 0 ↔ f != 0 ∨ y != 0 := by
  constructor
  · intro h
    contrapose! h
    rcases h with ⟨rfl, rfl⟩
    rw [optionElim_zero]; rw [single_zero]
  · intro h
    cases h with
    | inl h => exact optionElim_ne_zero_of_right y f h
    | inr h => exact optionElim_ne_zero_of_left y f h

/--
theorem `eq_option_embedding_update_none_iff` / 定理 `eq_option_embedding_update_none_iff`

English:
theorem eq_option_embedding_update_none_iff
  given: {n : Option α ->₀ M} {m : α ->₀ M} {i : M}
  proof: (optionEquiv.eq_symm_apply (x := (_, _))).trans Prod.ext_iff

中文:
定理 eq_option_embedding_update_none_iff
  条件: {n : 选项类型 α ->₀ M} {m : α ->₀ M} {i : M}
  证明: (optionEquiv.eq_symm_apply (x := (_, _))).trans Prod.ext_iff

Depends on / 依赖: Prod.ext_iff, eq_symm_apply, ext_iff, optionEquiv, optionEquiv.eq_symm_apply
-/
theorem eq_option_embedding_update_none_iff {n : Option α ->₀ M} {m : α ->₀ M} {i : M} :
    n = (embDomain Embedding.some m).update none i ↔ n none = i ∧ n.some = m :=
  (optionEquiv.eq_symm_apply (x := (_, _))).trans Prod.ext_iff

end Zero

@[to_additive]
/--
theorem `prod_option_index` / 定理 `prod_option_index`

English:
theorem prod_option_index
  statement: [AddZeroClass M] [CommMonoid N] (f : Option α ->₀ M)
  proof: by
  classical
    induction f using induction_linear with
    | zero => simp [some_zero, h_zero]
    | add f₁ f₂ h₁ h₂ =>
      rw [Finsupp.prod_add_index]; rw [h₁]; rw [h₂]; rw [some_add]; rw [Finsupp.prod_add_index]
      · simp only [h_add, Pi.add_apply, Finsupp.coe_add]
        rw [mul_mul_mul_

中文:
定理 prod_option_index
  结论: [加法零类 M] [交换幺半群 N] (f : 选项类型 α ->₀ M)
  证明: by
  classical
    induction f using induction_linear with
    | zero => simp [some_zero, h_zero]
    | add f₁ f₂ h₁ h₂ =>
      rw [Finsupp.prod_add_index]; rw [h₁]; rw [h₂]; rw [some_add]; rw [Finsupp.prod_add_index]
      · simp only [h_add, Pi.add_apply, Finsupp.coe_add]
        rw [mul_mul_mul_

Depends on / 依赖: Finsupp, Finsupp.coe_add, Finsupp.prod_add_index, Pi.add_apply, add_apply, all_goals, classical, coe_add, h_add, h_zero, induction_linear, mul_mul_mul_comm, prod_add_index, single, some_add, some_zero
-/
theorem prod_option_index [AddZeroClass M] [CommMonoid N] (f : Option α ->₀ M)
    (b : Option α -> M -> N) (h_zero : forall o, b o 0 = 1)
    (h_add : forall o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂) :
    f.prod b = b none (f none) * f.some.prod fun a => b (Option.some a) := by
  classical
    induction f using induction_linear with
    | zero => simp [some_zero, h_zero]
    | add f₁ f₂ h₁ h₂ =>
      rw [Finsupp.prod_add_index]; rw [h₁]; rw [h₂]; rw [some_add]; rw [Finsupp.prod_add_index]
      · simp only [h_add, Pi.add_apply, Finsupp.coe_add]
        rw [mul_mul_mul_comm]
      all_goals simp [h_zero, h_add]
    | single a m => cases a <;> simp [h_zero]

/--
theorem `sum_option_index_smul` / 定理 `sum_option_index_smul`

English:
theorem sum_option_index_smul
  statement: [Semiring R] [AddCommMonoid M] [Module R M] (f : Option α ->₀ R)
  proof: f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

@[simp]

中文:
定理 sum_option_index_smul
  结论: [半环 R] [加法交换幺半群 M] [模 R M] (f : 选项类型 α ->₀ R)
  证明: f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

@[simp]

Depends on / 依赖: add_smul, f.sum_option_index, sum_option_index, zero_smul
-/
theorem sum_option_index_smul [Semiring R] [AddCommMonoid M] [Module R M] (f : Option α ->₀ R)
    (b : Option α -> M) :
    (f.sum fun o r => r • b o) = f none • b none + f.some.sum fun a r => r • b (Option.some a) :=
  f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

@[simp]
/--
lemma `optionElim_add` / 引理 `optionElim_add`

English:
lemma optionElim_add
  given: [AddZeroClass M] (a b : α ->₀ M) (i j : M)
  proof: by
  ext x; cases x <;> simp

中文:
引理 optionElim_add
  条件: [加法零类 M] (a b : α ->₀ M) (i j : M)
  证明: by
  ext x; cases x <;> simp
-/
lemma optionElim_add [AddZeroClass M] (a b : α ->₀ M) (i j : M) :
    (a + b).optionElim (i + j) = a.optionElim i + b.optionElim j := by
  ext x; cases x <;> simp

end Option

end Finsupp
