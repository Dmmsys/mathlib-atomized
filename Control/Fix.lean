/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.Part
public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Upto
public import Mathlib.Data.Stream.Defs

/-!
# Fixed point

This module defines a generic `fix` operator for defining recursive
computations that are not necessarily well-founded or productive.
An instance is defined for `Part`.

## Main definition

* class `Fix`
* `Part.fix`
-/

@[expose] public section


universe u v

variable {α : Type*} {β : α -> Type*}

/--
Definition of `Fix` / `Fix` 的定义

English:
class Fix
  parameters: (α : Type*)
  axioms and operations (1):
    - fix : (α -> α) -> α

中文:
类 Fix
  参数: (α : 类型)
  公理与运算 (1 个):
    - fix : (α -> α) -> α
-/
class Fix (α : Type*) where
  /-- `fix f` represents the computation of a fixed point for `f`. -/
  fix : (α -> α) -> α

namespace Part

open Part Nat Nat.Upto

section Basic

variable (f : (forall a, Part (β a)) -> (forall a, Part (β a)))

/--
Definition of `Fix.approx` / `Fix.approx` 的定义

English:
definition Fix.approx
  signature: : Stream' (forall a, Part (β a))

中文:
定义 Fix.approx
  签名: : Stream' (对任意 a, Part (β a))
-/
def Fix.approx : Stream' (forall a, Part (β a))
  | 0 => ⊥
  | Nat.succ i => f (Fix.approx i)

/--
Definition of `fixAux` / `fixAux` 的定义

English:
definition fixAux
  signature: {p : Nat -> Prop} (i : Nat.Upto p) (g : forall j : Nat.Upto p, i < j -> forall a, Part (β a))
  body: f fun x : α => (assert ¬p i.val) fun h : ¬p i.val => g (i.succ h) (Nat.lt_succ_self _) x

中文:
定义 fixAux
  签名: {p : 自然数 -> 命题} (i : 自然数.Upto p) (g : 对任意 j : 自然数.Upto p, i < j -> 对任意 a, Part (β a))
  定义体: f fun x : α => (assert ¬p i.val) fun h : ¬p i.val => g (i.succ h) (Nat.lt_succ_self _) x

Depends on / 依赖: Nat.lt_succ_self, assert, i.succ, i.val, lt_succ_self
-/
def fixAux {p : Nat -> Prop} (i : Nat.Upto p) (g : forall j : Nat.Upto p, i < j -> forall a, Part (β a)) :
    forall a, Part (β a) :=
  f fun x : α => (assert ¬p i.val) fun h : ¬p i.val => g (i.succ h) (Nat.lt_succ_self _) x

/--
Definition of `fix` / `fix` 的定义

English:
definition fix
  signature: (x : α)
  body: (Part.assert (exists i, (Fix.approx f i x).Dom)) fun h =>
    WellFounded.fix.{1} (Nat.Upto.wf h) (fixAux f) Nat.Upto.zero x

中文:
定义 fix
  签名: (x : α)
  定义体: (Part.assert (exists i, (Fix.approx f i x).Dom)) fun h =>
    WellFounded.fix.{1} (Nat.Upto.wf h) (fixAux f) Nat.Upto.zero x
-/
protected def fix (x : α) : Part (β x) :=
  (Part.assert (exists i, (Fix.approx f i x).Dom)) fun h =>
    WellFounded.fix.{1} (Nat.Upto.wf h) (fixAux f) Nat.Upto.zero x

open scoped Classical in
/--
theorem `fix_def` / 定理 `fix_def`

English:
theorem fix_def
  given: {x : α} (h' : exists i, (Fix.approx f i x).Dom)
  proof: by
  let p := fun i : Nat => (Fix.approx f i x).Dom
  have : p (Nat.find h') := Nat.find_spec h'
  generalize hk : Nat.find h' = k
  replace hk : Nat.find h' = k + (@Upto.zero p).val := hk
  rw [hk] at this
  revert hk
  dsimp [Part.fix]; rw [assert_pos h']; revert this
  generalize Upto.zero = z; intro _this hk
  suffices forall x' hwf,
    WellFounded.fix hwf (fixAux f) z x' = Fix.approx f (succ k) x'
    from this _ _
  induction k generalizing z with
  | zero =>
    intro x' _
    rw [Fix.approx]; rw [WellFounded.fix_eq]; rw [fixAux]
    congr
    ext x : 1
    rw [assert_neg]
    · rfl
    · rw [Nat.zero_add] at _this
      simpa only [not_not, Coe]
  | succ n n_ih =>
    intro x' _
    rw [Fix.approx]; rw [WellFounded.fix_eq]; rw [fixAux]
    congr
    ext : 1
    have hh : ¬(Fix.approx f z.val x).Dom := by
      apply Nat.find_min h'
      lia
    rw [succ_add_eq_add_succ] at _this hk
    rw [assert_pos hh]; rw [n_ih (Upto.succ z hh) _this hk]

中文:
定理 fix_def
  条件: {x : α} (h' : 存在 i, (Fix.approx f i x).Dom)
  证明: by
  let p := fun i : Nat => (Fix.approx f i x).Dom
  have : p (Nat.find h') := Nat.find_spec h'
  generalize hk : Nat.find h' = k
  replace hk : Nat.find h' = k + (@Upto.zero p).val := hk
  rw [hk] at this
  revert hk
  dsimp [Part.fix]; rw [assert_pos h']; revert this
  generalize Upto.zero = z; intro _this hk
  suffices forall x' hwf,
    WellFounded.fix hwf (fixAux f) z x' = Fix.approx f (succ k) x'
    from this _ _
  induction k generalizing z with
  | zero =>
    intro x' _
    rw [Fix.approx]; rw [WellFounded.fix_eq]; rw [fixAux]
    congr
    ext x : 1
    rw [assert_neg]
    · rfl
    · rw [Nat.zero_add] at _this
      simpa only [not_not, Coe]
  | succ n n_ih =>
    intro x' _
    rw [Fix.approx]; rw [WellFounded.fix_eq]; rw [fixAux]
    congr
    ext : 1
    have hh : ¬(Fix.approx f z.val x).Dom := by
      apply Nat.find_min h'
      lia
    rw [succ_add_eq_add_succ] at _this hk
    rw [assert_pos hh]; rw [n_ih (Upto.succ z hh) _this hk]
-/
protected theorem fix_def {x : α} (h' : exists i, (Fix.approx f i x).Dom) :
    Part.fix f x = Fix.approx f (Nat.succ (Nat.find h')) x := by
  let p := fun i : Nat => (Fix.approx f i x).Dom
  have : p (Nat.find h') := Nat.find_spec h'
  generalize hk : Nat.find h' = k
  replace hk : Nat.find h' = k + (@Upto.zero p).val := hk
  rw [hk] at this
  revert hk
  dsimp [Part.fix]; rw [assert_pos h']; revert this
  generalize Upto.zero = z; intro _this hk
  suffices forall x' hwf,
    WellFounded.fix hwf (fixAux f) z x' = Fix.approx f (succ k) x'
    from this _ _
  induction k generalizing z with
  | zero =>
    intro x' _
    rw [Fix.approx]; rw [WellFounded.fix_eq]; rw [fixAux]
    congr
    ext x : 1
    rw [assert_neg]
    · rfl
    · rw [Nat.zero_add] at _this
      simpa only [not_not, Coe]
  | succ n n_ih =>
    intro x' _
    rw [Fix.approx]; rw [WellFounded.fix_eq]; rw [fixAux]
    congr
    ext : 1
    have hh : ¬(Fix.approx f z.val x).Dom := by
      apply Nat.find_min h'
      lia
    rw [succ_add_eq_add_succ] at _this hk
    rw [assert_pos hh]; rw [n_ih (Upto.succ z hh) _this hk]

/--
theorem `fix_def'` / 定理 `fix_def'`

English:
theorem fix_def'
  given: {x : α} (h' : ¬exists i, (Fix.approx f i x).Dom)
  statement: Part.fix f x = none
  proof: by
  dsimp [Part.fix]
  rw [assert_neg h']

中文:
定理 fix_def'
  条件: {x : α} (h' : ¬存在 i, (Fix.approx f i x).Dom)
  结论: Part.fix f x = none
  证明: by
  dsimp [Part.fix]
  rw [assert_neg h']

Depends on / 依赖: Part.fix, assert_neg
-/
theorem fix_def' {x : α} (h' : ¬exists i, (Fix.approx f i x).Dom) : Part.fix f x = none := by
  dsimp [Part.fix]
  rw [assert_neg h']

end Basic

end Part

namespace Part

/--
Instance `hasFix` / 实例 `hasFix`

English:
instance hasFix
  signature: : Fix (Part α)
  body: ⟨fun f => Part.fix (fun x u => f (x u)) ()⟩

中文:
实例 hasFix
  签名: : Fix (Part α)
  定义体: ⟨fun f => Part.fix (fun x u => f (x u)) ()⟩

Depends on / 依赖: Part.fix
-/
instance hasFix : Fix (Part α) :=
  ⟨fun f => Part.fix (fun x u => f (x u)) ()⟩

end Part

open Sigma

namespace Pi

/--
Instance `Part.hasFix` / 实例 `Part.hasFix`

English:
instance Part.hasFix
  signature: {β}
  body: ⟨Part.fix⟩

中文:
实例 Part.hasFix
  签名: {β}
  定义体: ⟨Part.fix⟩
-/
instance Part.hasFix {β} : Fix (α -> Part β) :=
  ⟨Part.fix⟩

end Pi
