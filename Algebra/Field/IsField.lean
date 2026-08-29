/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Tactic.Common

/-!
# `IsField` predicate

Predicate on a (semi)ring that it is a (semi)field, i.e. that the multiplication is
commutative, that it has more than one element and that all non-zero elements have a
multiplicative inverse. In contrast to `Field`, which contains the data of a function associating
to an element of the field its multiplicative inverse, this predicate only assumes the existence
and can therefore more easily be used to e.g. transfer along ring isomorphisms.
-/

@[expose] public section

universe u

section IsField

/--
Definition of `IsField` / `IsField` 的定义

English:
structure IsField
  parameters: (R : Type u) [Semiring R]
  axioms and operations (3):
    - exists_pair_ne : exists x y : R, x != y
    - mul_comm : forall x y : R, x * y = y * x
    - mul_inv_cancel : forall {a : R}, a != 0 -> exists b, a * b = 1

中文:
结构 IsField
  参数: (R : 类型u) [Semiring R]
  公理与运算 (3 个):
    - exists_pair_ne : 存在 x y : R, x != y
    - mul_comm : 对任意 x y : R, x * y = y * x
    - mul_inv_cancel : 对任意 {a : R}, a != 0 -> 存在 b, a * b = 1
-/
structure IsField (R : Type u) [Semiring R] : Prop where
  /-- For a semiring to be a field, it must have two distinct elements. -/
  exists_pair_ne : exists x y : R, x != y
  /-- Fields are commutative. -/
  mul_comm : forall x y : R, x * y = y * x
  /-- Nonzero elements have multiplicative inverses. -/
  mul_inv_cancel : forall {a : R}, a != 0 -> exists b, a * b = 1

/--
theorem `Semifield.toIsField` / 定理 `Semifield.toIsField`

English:
theorem Semifield.toIsField
  given: (R : Type u) [Semifield R]
  statement: IsField R where
  proof: ‹Semifield R›
  mul_inv_cancel {a} ha := ⟨a⁻¹, mul_inv_cancel₀ ha⟩

中文:
定理 Semifield.toIsField
  条件: (R : 类型u) [Semifield R]
  结论: IsField R where
  证明: ‹Semifield R›
  mul_inv_cancel {a} ha := ⟨a⁻¹, mul_inv_cancel₀ ha⟩

Depends on / 依赖: Semifield
-/
theorem Semifield.toIsField (R : Type u) [Semifield R] : IsField R where
  __ := ‹Semifield R›
  mul_inv_cancel {a} ha := ⟨a⁻¹, mul_inv_cancel₀ ha⟩

/--
theorem `Field.toIsField` / 定理 `Field.toIsField`

English:
theorem Field.toIsField
  given: (R : Type u) [Field R]
  statement: IsField R
  proof: Semifield.toIsField _

@[simp]

中文:
定理 Field.toIsField
  条件: (R : 类型u) [Field R]
  结论: IsField R
  证明: Semifield.toIsField _

@[simp]

Depends on / 依赖: Semifield, Semifield.toIsField, toIsField
-/
theorem Field.toIsField (R : Type u) [Field R] : IsField R :=
  Semifield.toIsField _

@[simp]
/--
theorem `IsField.nontrivial` / 定理 `IsField.nontrivial`

English:
theorem IsField.nontrivial
  given: {R : Type u} [Semiring R] (h : IsField R)
  statement: Nontrivial R
  proof: ⟨h.exists_pair_ne⟩

中文:
定理 IsField.nontrivial
  条件: {R : 类型u} [Semiring R] (h : IsField R)
  结论: Nontrivial R
  证明: ⟨h.exists_pair_ne⟩

Depends on / 依赖: exists_pair_ne, h.exists_pair_ne
-/
theorem IsField.nontrivial {R : Type u} [Semiring R] (h : IsField R) : Nontrivial R :=
  ⟨h.exists_pair_ne⟩

/--
lemma `IsField.isDomain` / 引理 `IsField.isDomain`

English:
lemma IsField.isDomain
  given: {R : Type u} [Semiring R] (h : IsField R)
  statement: IsDomain R where
  proof: by
    obtain ⟨x, hx⟩ := h.mul_inv_cancel ha
    simpa [← mul_assoc, h.mul_comm, hx] using congr_arg (x * ·) hb
  mul_right_cancel_of_ne_zero ha _ _ hb := by
    obtain ⟨x, hx⟩ := h.mul_inv_cancel ha
    simpa [mul_assoc, hx] using congr_arg (· * x) hb
  exists_pair_ne := h.exists_pair_ne

中文:
引理 IsField.isDomain
  条件: {R : 类型u} [Semiring R] (h : IsField R)
  结论: IsDomain R where
  证明: by
    obtain ⟨x, hx⟩ := h.mul_inv_cancel ha
    simpa [← mul_assoc, h.mul_comm, hx] using congr_arg (x * ·) hb
  mul_right_cancel_of_ne_zero ha _ _ hb := by
    obtain ⟨x, hx⟩ := h.mul_inv_cancel ha
    simpa [mul_assoc, hx] using congr_arg (· * x) hb
  exists_pair_ne := h.exists_pair_ne

Depends on / 依赖: congr_arg, exists_pair_ne, h.exists_pair_ne, h.mul_comm, h.mul_inv_cancel, mul_assoc, mul_comm, mul_inv_cancel, mul_right_cancel_of_ne_zero
-/
lemma IsField.isDomain {R : Type u} [Semiring R] (h : IsField R) : IsDomain R where
  mul_left_cancel_of_ne_zero ha _ _ hb := by
    obtain ⟨x, hx⟩ := h.mul_inv_cancel ha
    simpa [← mul_assoc, h.mul_comm, hx] using congr_arg (x * ·) hb
  mul_right_cancel_of_ne_zero ha _ _ hb := by
    obtain ⟨x, hx⟩ := h.mul_inv_cancel ha
    simpa [mul_assoc, hx] using congr_arg (· * x) hb
  exists_pair_ne := h.exists_pair_ne

instance {R : Type u} [Semifield R] : IsDomain R :=
  (Semifield.toIsField _).isDomain

@[simp]
/--
theorem `not_isField_of_subsingleton` / 定理 `not_isField_of_subsingleton`

English:
theorem not_isField_of_subsingleton
  given: (R : Type u) [Semiring R] [Subsingleton R]
  statement: ¬IsField R
  proof: fun h =>
  let ⟨_, _, h⟩ := h.exists_pair_ne
  h (Subsingleton.elim _ _)

中文:
定理 not_isField_of_subsingleton
  条件: (R : 类型u) [Semiring R] [Subsingleton R]
  结论: ¬IsField R
  证明: fun h =>
  let ⟨_, _, h⟩ := h.exists_pair_ne
  h (Subsingleton.elim _ _)

Depends on / 依赖: Subsingleton, Subsingleton.elim, exists_pair_ne, h.exists_pair_ne
-/
theorem not_isField_of_subsingleton (R : Type u) [Semiring R] [Subsingleton R] : ¬IsField R :=
  fun h =>
  let ⟨_, _, h⟩ := h.exists_pair_ne
  h (Subsingleton.elim _ _)

open scoped Classical in
/-- Transferring from `IsField` to `Semifield`. -/
@[instance_reducible]
/--
Definition of `IsField.toSemifield` / `IsField.toSemifield` 的定义

English:
definition IsField.toSemifield
  signature: {R : Type u} [Semiring R] (h : IsField R)
  body: ‹Semiring R›
  __ := h
  inv a := if ha : a = 0 then 0 else Classical.choose (h.mul_inv_cancel ha)
  inv_zero := dif_pos rfl
  mul_inv_cancel a ha := by convert! Classical.choose_spec (h.mul_inv_cancel ha); exact dif_neg ha
  nnqsmul := _
  nnqsmul_def _ _ := rfl

中文:
定义 IsField.toSemifield
  签名: {R : 类型u} [Semiring R] (h : IsField R)
  定义体: ‹Semiring R›
  __ := h
  inv a := if ha : a = 0 then 0 else Classical.choose (h.mul_inv_cancel ha)
  inv_zero := dif_pos rfl
  mul_inv_cancel a ha := by convert! Classical.choose_spec (h.mul_inv_cancel ha); exact dif_neg ha
  nnqsmul := _
  nnqsmul_def _ _ := rfl

Depends on / 依赖: Semiring
-/
noncomputable def IsField.toSemifield {R : Type u} [Semiring R] (h : IsField R) : Semifield R where
  __ := ‹Semiring R›
  __ := h
  inv a := if ha : a = 0 then 0 else Classical.choose (h.mul_inv_cancel ha)
  inv_zero := dif_pos rfl
  mul_inv_cancel a ha := by convert! Classical.choose_spec (h.mul_inv_cancel ha); exact dif_neg ha
  nnqsmul := _
  nnqsmul_def _ _ := rfl

/-- Transferring from `IsField` to `Field`. -/
@[instance_reducible]
/--
Definition of `IsField.toField` / `IsField.toField` 的定义

English:
definition IsField.toField
  signature: {R : Type u} [Ring R] (h : IsField R)
  body: (‹Ring R› :) -- this also works without the `( :)`, but it's slow
  __ := h.toSemifield
  qsmul := _
  qsmul_def := fun _ _ => rfl

中文:
定义 IsField.toField
  签名: {R : 类型u} [Ring R] (h : IsField R)
  定义体: (‹Ring R› :) -- this also works without the `( :)`, but it's slow
  __ := h.toSemifield
  qsmul := _
  qsmul_def := fun _ _ => rfl

Depends on / 依赖: without
-/
noncomputable def IsField.toField {R : Type u} [Ring R] (h : IsField R) : Field R where
  __ := (‹Ring R› :) -- this also works without the `( :)`, but it's slow
  __ := h.toSemifield
  qsmul := _
  qsmul_def := fun _ _ => rfl

/--
theorem `uniq_inv_of_isField` / 定理 `uniq_inv_of_isField`

English:
theorem uniq_inv_of_isField
  given: (R : Type u) [Ring R] (hf : IsField R)
  proof: by
  intro x hx
  apply existsUnique_of_exists_of_unique
  · exact hf.mul_inv_cancel hx
  · intro y z hxy hxz
    calc
      y = y * (x * z) := by rw [hxz, mul_one]
      _ = x * y * z := by rw [← mul_assoc, hf.mul_comm y x]
      _ = z := by rw [hxy, one_mul]

中文:
定理 uniq_inv_of_isField
  条件: (R : 类型u) [Ring R] (hf : IsField R)
  证明: by
  intro x hx
  apply existsUnique_of_exists_of_unique
  · exact hf.mul_inv_cancel hx
  · intro y z hxy hxz
    calc
      y = y * (x * z) := by rw [hxz, mul_one]
      _ = x * y * z := by rw [← mul_assoc, hf.mul_comm y x]
      _ = z := by rw [hxy, one_mul]

Depends on / 依赖: existsUnique_of_exists_of_unique, hf.mul_comm, hf.mul_inv_cancel, mul_assoc, mul_comm, mul_inv_cancel, mul_one, one_mul
-/
theorem uniq_inv_of_isField (R : Type u) [Ring R] (hf : IsField R) :
    forall x : R, x != 0 -> exists! y : R, x * y = 1 := by
  intro x hx
  apply existsUnique_of_exists_of_unique
  · exact hf.mul_inv_cancel hx
  · intro y z hxy hxz
    calc
      y = y * (x * z) := by rw [hxz, mul_one]
      _ = x * y * z := by rw [← mul_assoc, hf.mul_comm y x]
      _ = z := by rw [hxy, one_mul]

end IsField
