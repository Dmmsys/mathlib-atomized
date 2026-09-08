/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.Analysis.Normed.Ring.TransferInstance
public import Mathlib.Topology.Algebra.Ring.Basic

/-!
# `WithAbs` type synonym

`WithAbs v` is a copy of the semiring `R` with the same underlying ring structure, but assigned
`v`-dependent instances (such as `NormedRing`) where `v` is an absolute value on `R`.

## Main definitions
- `WithAbs` : type synonym for a semiring which depends on an absolute value. This is
  a function that takes an absolute value on a semiring and returns the semiring. This can be used
  to assign and infer instances on a semiring that depend on absolute values.
- `WithAbs.equiv v` : The canonical ring equivalence between `WithAbs v` and `R`.
-/

@[expose] public section

open Topology

variable {R : Type*} {S : Type*} [Semiring S] [PartialOrder S]

/-- Type synonym for a semiring which depends on an absolute value. This is a function that takes
an absolute value on a semiring and returns the semiring. We use this to assign and infer instances
on a semiring that depend on absolute values.

This is also helpful when dealing with several absolute values on the same semiring. -/
/-
**WithAbs** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Semiring S] → [inst_1 : Pa
rtialOrder S] → [inst_2 : Semiring R] → AbsoluteValue R S → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for a semiring which depends on an absolute value. This is a functi
on that takes
an absolute value on a semiring and returns the semiring. We use this to assign 
and infer instances
on a semiring that depend on absolute values.

This is also helpful when dealing with several absolute values on the same semir
ing.
-/
structure WithAbs [Semiring R] (v : AbsoluteValue R S) where
  /-- Converts an element of `R` to an element of `WithAbs v`. -/
  toAbs (v) ::
  /-- Converts an element of `WithAbs v` to an element of `R`. -/
  ofAbs : R

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toAbs p x` being printed as `{ ofAbs := x }` by `delabStructureInstance`. -/
@[app_delab WithAbs.toAbs]
meta def WithAbs.delabToAbs : Delab := delabApp

end Notation

namespace WithAbs

section Semiring

variable [Semiring R] (v : AbsoluteValue R S)

/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semiring (WithAbs v) :=
  fast_instance% Equiv.semiring { toFun := ofAbs, invFun := toAbs v }
/-
**WithAbs.ofAbs_toAbs** 是 Mathlib 中的一个引理，位于命名空间 `WithAbs`。
形式化陈述：ofAbs_toAbs (x : R) : ofAbs (toAbs v x) = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofAbs_toAbs (x : R) : ofAbs (toAbs v x) = x := rfl
/-
**WithAbs.toAbs_ofAbs** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (x : WithAbs v), WithAbs.toA
bs v x.ofAbs = x
参数：v : AbsoluteValue R S；x : WithAbs v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAbs_ofAbs (x : WithAbs v) : toAbs v (ofAbs x) = x := rfl
/-
**WithAbs.ofAbs_surjective** 是 Mathlib 中的一个引理，位于命名空间 `WithAbs`。
形式化陈述：ofAbs_surjective : Function.Surjective (ofAbs (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用引理 `WithAbs.ofAbs_toAbs`：ofAbs_toAbs (x : R) : ofAbs (toAbs v x) = x
-/
lemma ofAbs_surjective : Function.Surjective (ofAbs (v := v)) :=
  Function.RightInverse.surjective <| ofAbs_toAbs _
/-
**WithAbs.toAbs_surjective** 是 Mathlib 中的一个引理，位于命名空间 `WithAbs`。
形式化陈述：toAbs_surjective : Function.Surjective (toAbs v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `WithAbs.toAbs_ofAbs`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S]
 [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (x : 
WithAbs v…
-/
lemma toAbs_surjective : Function.Surjective (toAbs v) :=
  Function.RightInverse.surjective <| toAbs_ofAbs _
/-
**WithAbs.ofAbs_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithAbs`。
形式化陈述：ofAbs_injective : Function.Injective (ofAbs (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `WithAbs.toAbs_ofAbs`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S]
 [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (x : 
WithAbs v…
-/
lemma ofAbs_injective : Function.Injective (ofAbs (v := v)) :=
  Function.LeftInverse.injective <| toAbs_ofAbs _
/-
**WithAbs.toAbs_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithAbs`。
形式化陈述：toAbs_injective : Function.Injective (toAbs v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用引理 `WithAbs.ofAbs_toAbs`：ofAbs_toAbs (x : R) : ofAbs (toAbs v x) = x
-/
lemma toAbs_injective : Function.Injective (toAbs v) :=
  Function.LeftInverse.injective <| ofAbs_toAbs _
/-
**WithAbs.ofAbs_bijective** 是 Mathlib 中的一个引理，位于命名空间 `WithAbs`。
形式化陈述：ofAbs_bijective : Function.Bijective (ofAbs (v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithAbs.ofAbs_injective`：ofAbs_injective : Function.Injective (ofAbs (v
· 使用引理 `WithAbs.ofAbs_surjective`：ofAbs_surjective : Function.Surjective (ofAbs 
(v
-/
lemma ofAbs_bijective : Function.Bijective (ofAbs (v := v)) :=
  ⟨ofAbs_injective v, ofAbs_surjective v⟩
/-
**WithAbs.toAbs_bijective** 是 Mathlib 中的一个引理，位于命名空间 `WithAbs`。
形式化陈述：toAbs_bijective : Function.Bijective (toAbs v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithAbs.toAbs_injective`：toAbs_injective : Function.Injective (toAbs v)
· 使用引理 `WithAbs.toAbs_surjective`：toAbs_surjective : Function.Surjective (toAbs 
v)
-/
lemma toAbs_bijective : Function.Bijective (toAbs v) :=
  ⟨toAbs_injective v, toAbs_surjective v⟩
/-
**WithAbs.toAbs_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S), WithAbs.toAbs v 0 = 0
参数：v : AbsoluteValue R S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAbs_zero : toAbs v (0 : R) = 0 := rfl
/-
**WithAbs.ofAbs_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S), WithAbs.ofAbs 0 = 0
参数：v : AbsoluteValue R S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAbs_zero : ofAbs (0 : WithAbs v) = 0 := rfl
/-
**WithAbs.toAbs_one** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S), WithAbs.toAbs v 1 = 1
参数：v : AbsoluteValue R S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAbs_one : toAbs v (1 : R) = 1 := rfl
/-
**WithAbs.ofAbs_one** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S), WithAbs.ofAbs 1 = 1
参数：v : AbsoluteValue R S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAbs_one : ofAbs (1 : WithAbs v) = 1 := rfl
/-
**WithAbs.toAbs_add** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (x y : R), WithAbs.toAbs v (
x + y) = WithAbs.toAbs v x + WithAbs.toAbs v y
参数：v : AbsoluteValue R S；x y : R；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAbs_add (x y : R) : toAbs v (x + y) = toAbs v x + toAbs v y := rfl
/-
**WithAbs.ofAbs_add** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (x y : WithAbs v), (x + y).o
fAbs = x.ofAbs + y.ofAbs
参数：v : AbsoluteValue R S；x y : WithAbs v；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAbs_add (x y : WithAbs v) : ofAbs (x + y) = ofAbs x + ofAbs y := rfl
/-
**WithAbs.toAbs_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (x y : R), WithAbs.toAbs v (
x * y) = WithAbs.toAbs v x * WithAbs.toAbs v y
参数：v : AbsoluteValue R S；x y : R；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAbs_mul (x y : R) : toAbs v (x * y) = toAbs v x * toAbs v y := rfl
/-
**WithAbs.ofAbs_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (x y : WithAbs v), (x * y).o
fAbs = x.ofAbs * y.ofAbs
参数：v : AbsoluteValue R S；x y : WithAbs v；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAbs_mul (x y : WithAbs v) : ofAbs (x * y) = ofAbs x * ofAbs y := rfl
/-
**WithAbs.toAbs_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) {x : R}, WithAbs.toAbs v x =
 0 ↔ x = 0
参数：v : AbsoluteValue R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithAbs.toAbs_injective`：toAbs_injective : Function.Injective (toAbs v)
-/
@[simp] lemma toAbs_eq_zero {x : R} : toAbs v x = 0 ↔ x = 0 := (toAbs_injective v).eq_iff
/-
**WithAbs.ofAbs_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) {x : WithAbs v}, x.ofAbs = 0
 ↔ x = 0
参数：v : AbsoluteValue R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithAbs.ofAbs_injective`：ofAbs_injective : Function.Injective (ofAbs (v
-/
@[simp] lemma ofAbs_eq_zero {x : WithAbs v} : ofAbs x = 0 ↔ x = 0 := (ofAbs_injective v).eq_iff
/-
**WithAbs.toAbs_pow** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (x : R) (n : ℕ), WithAbs.toA
bs v (x ^ n) = WithAbs.toAbs v x ^ n
参数：v : AbsoluteValue R S；x : R；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAbs_pow (x : R) (n : ℕ) : toAbs v (x ^ n) = toAbs v x ^ n := rfl
/-
**WithAbs.ofAbs_pow** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (x : WithAbs v) (n : ℕ), (x 
^ n).ofAbs = x.ofAbs ^ n
参数：v : AbsoluteValue R S；x : WithAbs v；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAbs_pow (x : WithAbs v) (n : ℕ) : ofAbs (x ^ n) = ofAbs x ^ n := rfl

/-- The canonical (semiring) equivalence between `WithAbs v` and `R`. -/
@[simps apply symm_apply]
/-
**WithAbs.equiv** 是 Mathlib 中的一个定义，位于命名空间 `WithAbs`。
形式化陈述：equiv : WithAbs v ≃+* R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical (semiring) equivalence between `WithAbs v` and `R`.
-/
def equiv : WithAbs v ≃+* R where
  toFun := ofAbs
  invFun := toAbs v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial (WithAbs v) := (equiv v).nontrivial
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique R] : Unique (WithAbs v) := (equiv v).unique
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (WithAbs v) := ⟨0⟩

variable {T U : Type*} [Semiring T] [Semiring U] (w : AbsoluteValue T S) (u : AbsoluteValue U S)
  (f : R →+* T) (g : T →+* U)

/-- Lift a ring hom to `WithAbs`. -/
/-
**WithAbs.map** 是 Mathlib 中的一个定义，位于命名空间 `WithAbs`。
形式化陈述：map : WithAbs v ->+* WithAbs w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a ring hom to `WithAbs`.
-/
def map : WithAbs v →+* WithAbs w := (equiv w).symm.toRingHom.comp (f.comp (equiv v).toRingHom)
/-
**WithAbs.map_id** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S), WithAbs.map v v (RingHom.id
 R) = RingHom.id (WithAbs v)
参数：v : AbsoluteValue R S；RingHom.id R；WithAbs v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_id : WithAbs.map v v (RingHom.id R) = RingHom.id (WithAbs v) := rfl
/-
**WithAbs.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：map_comp : map v u (g.comp f) = (map w u g).comp (map v w f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp : map v u (g.comp f) = (map w u g).comp (map v w f) := rfl
/-
**WithAbs.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) {T : Type u_3} [inst_3 : Sem
iring T] (w : AbsoluteValue T S) (f : R →+* T) (x : WithAbs v),   (WithAbs.map v
 w f) x = WithAbs.toAbs w (f x.ofAbs)
参数：v : AbsoluteValue R S；w : AbsoluteValue T S；f : R →+* T；x : WithAbs v；WithAbs
.map v w f；f x.ofAbs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_apply (x : WithAbs v) : map v w f x = toAbs w (f x.ofAbs) := rfl

variable (f : R ≃+* T) (g : T ≃+* U)

/-- Lift a `RingEquiv` to `WithAbs`. -/
/-
**WithAbs.congr** 是 Mathlib 中的一个定义，位于命名空间 `WithAbs`。
形式化陈述：congr : WithAbs v ≃+* WithAbs w where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a `RingEquiv` to `WithAbs`.
-/
def congr : WithAbs v ≃+* WithAbs w where
  __ := map v w f.toRingHom
  invFun := map w v f.symm.toRingHom
  left_inv x := by simp
  right_inv x := by simp

@[simp]
/-
**WithAbs.congr_refl** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：congr_refl : congr v v (RingEquiv.refl R) = RingEquiv.refl (WithAbs v)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_refl : congr v v (RingEquiv.refl R) = RingEquiv.refl (WithAbs v) := rfl
/-
**WithAbs.congr_trans** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：congr_trans : congr v u (f.trans g) = (congr v w f).trans (congr w u g)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_trans : congr v u (f.trans g) = (congr v w f).trans (congr w u g) := rfl
/-
**WithAbs.congr_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：congr_symm : (congr v w f).symm = congr w v f.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_symm : (congr v w f).symm = congr w v f.symm := rfl
/-
**WithAbs.congr_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) {T : Type u_3} [inst_3 : Sem
iring T] (w : AbsoluteValue T S) (f : R ≃+* T) (x : WithAbs v),   (WithAbs.congr
 v w f) x = WithAbs.toAbs w (f x.ofAbs)
参数：v : AbsoluteValue R S；w : AbsoluteValue T S；f : R ≃+* T；x : WithAbs v；WithAbs
.congr v w f；f x.ofAbs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem congr_apply (x : WithAbs v) : congr v w f x = toAbs w (f x.ofAbs) := rfl
/-
**WithAbs.congr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) {T : Type u_3} [inst_3 : Sem
iring T] (w : AbsoluteValue T S) (f : R ≃+* T) (x : WithAbs w),   (WithAbs.congr
 v w f).symm x = WithAbs.toAbs v (f.symm x.ofAbs)
参数：v : AbsoluteValue R S；w : AbsoluteValue T S；f : R ≃+* T；x : WithAbs w；WithAbs
.congr v w f；f.symm x.ofAbs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem congr_symm_apply (x : WithAbs w) :
    (congr v w f).symm x = toAbs v (f.symm x.ofAbs) := rfl

/-- The canonical (semiring) equivalence between `WithAbs v` and `WithAbs w`, for any two
absolute values `v` and `w` on `R`. -/
@[deprecated "Use `WithAbs.congr` instead." (since := "2026-03-02")]
/-
**WithAbs.equivWithAbs** 是 Mathlib 中的一个定义，位于命名空间 `WithAbs`。
形式化陈述：equivWithAbs (v w : AbsoluteValue R S) : WithAbs v ≃+* WithAbs w
参数：v w : AbsoluteValue R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical (semiring) equivalence between `WithAbs v` and `WithAbs w`, for an
y two
absolute values `v` and `w` on `R`.
-/
def equivWithAbs (v w : AbsoluteValue R S) : WithAbs v ≃+* WithAbs w :=
    congr v w (.refl R)

@[deprecated "Use `WithAbs.congr_symm` instead." (since := "2026-03-02")]
/-
**WithAbs.equivWithAbs_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：equivWithAbs_symm (v w : AbsoluteValue R S) : (congr v w (.refl R)).symm =
 (congr w v (RingEquiv.refl R).symm)
参数：v w : AbsoluteValue R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithAbs.congr_symm`：congr_symm : (congr v w f).symm = congr w v f.symm
-/
theorem equivWithAbs_symm (v w : AbsoluteValue R S) :
    (congr v w (.refl R)).symm = (congr w v (RingEquiv.refl R).symm) :=
  congr_symm _ _ _

@[deprecated "Use `simp`." (since := "2026-03-02")]
/-
**WithAbs.equiv_equivWithAbs_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：equiv_equivWithAbs_symm_apply {v w : AbsoluteValue R S} {x : WithAbs w} : 
equiv v ((congr v w (.refl R)).symm x) = equiv w x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithAbs.equiv_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S]
 [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) (self
 : WithAb…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_equivWithAbs_symm_apply {v w : AbsoluteValue R S} {x : WithAbs w} :
    equiv v ((congr v w (.refl R)).symm x) = equiv w x := by simp

@[deprecated "Use `simp`." (since := "2026-03-02")]
/-
**WithAbs.equivWithAbs_equiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：equivWithAbs_equiv_symm_apply {v w : AbsoluteValue R S} {x : R} : congr v 
w (.refl R) ((equiv v).symm x) = (equiv w).symm x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithAbs.equiv_symm_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng S] [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) 
(ofAbs : R), (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivWithAbs_equiv_symm_apply {v w : AbsoluteValue R S} {x : R} :
    congr v w (.refl R) ((equiv v).symm x) = (equiv w).symm x := by simp

@[deprecated "Use `simp`." (since := "2026-03-02")]
/-
**WithAbs.equivWithAbs_symm_equiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`
。
形式化陈述：equivWithAbs_symm_equiv_symm_apply {v w : AbsoluteValue R S} {x : R} : (co
ngr v w (.refl R)).symm ((equiv w).symm x) = (equiv v).symm x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithAbs.equiv_symm_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng S] [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) 
(ofAbs : R), (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivWithAbs_symm_equiv_symm_apply {v w : AbsoluteValue R S} {x : R} :
    (congr v w (.refl R)).symm ((equiv w).symm x) = (equiv v).symm x := by simp

end Semiring

section CommSemiring

variable [CommSemiring R] (v : AbsoluteValue R S)

/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemiring (WithAbs v) := fast_instance% (equiv v).commSemiring

end CommSemiring

section Ring

variable [Ring R]

/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (v : AbsoluteValue R S) : Ring (WithAbs v) := fast_instance% (equiv v).ring
/-
**WithAbs.normedRing** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
形式化陈述：normedRing (v : AbsoluteValue R Real) : NormedRing (WithAbs v)
参数：v : AbsoluteValue R Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance normedRing (v : AbsoluteValue R ℝ) : NormedRing (WithAbs v) :=
  letI := v.toNormedRing
  fast_instance% (equiv v).normedRing
/-
**WithAbs.norm_eq_apply_ofAbs** 是 Mathlib 中的一个引理，位于命名空间 `WithAbs`。
形式化陈述：norm_eq_apply_ofAbs (v : AbsoluteValue R Real) (x : WithAbs v) : ‖x‖ = v x
.ofAbs
参数：v : AbsoluteValue R Real；x : WithAbs v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_eq_apply_ofAbs (v : AbsoluteValue R ℝ) (x : WithAbs v) : ‖x‖ = v x.ofAbs := rfl
/-
**WithAbs.norm_toAbs_eq** 是 Mathlib 中的一个引理，位于命名空间 `WithAbs`。
形式化陈述：norm_toAbs_eq (v : AbsoluteValue R Real) (x : R) : ‖toAbs v x‖ = v x
参数：v : AbsoluteValue R Real；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_toAbs_eq (v : AbsoluteValue R ℝ) (x : R) : ‖toAbs v x‖ = v x := rfl

@[deprecated (since := "2026-03-02")] alias norm_eq_abv := norm_eq_apply_ofAbs
@[deprecated (since := "2026-03-02")] alias norm_eq_abv' := norm_toAbs_eq

variable (v : AbsoluteValue R S)
/-
**WithAbs.toAbs_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Ring R] (v : AbsoluteValue R S)   (x y : R), WithAbs.toAbs v (x - 
y) = WithAbs.toAbs v x - WithAbs.toAbs v y
参数：v : AbsoluteValue R S；x y : R；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAbs_sub (x y : R) : toAbs v (x - y) = toAbs v x - toAbs v y := rfl
/-
**WithAbs.ofAbs_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Ring R] (v : AbsoluteValue R S)   (x y : WithAbs v), (x - y).ofAbs
 = x.ofAbs - y.ofAbs
参数：v : AbsoluteValue R S；x y : WithAbs v；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAbs_sub (x y : WithAbs v) : ofAbs (x - y) = ofAbs x - ofAbs y := rfl
/-
**WithAbs.toAbs_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Ring R] (v : AbsoluteValue R S)   (x : R), WithAbs.toAbs v (-x) = 
-WithAbs.toAbs v x
参数：v : AbsoluteValue R S；x : R；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAbs_neg (x : R) : toAbs v (-x) = - toAbs v x := rfl
/-
**WithAbs.ofAbs_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Ring R] (v : AbsoluteValue R S)   (x : WithAbs v), (-x).ofAbs = -x
.ofAbs
参数：v : AbsoluteValue R S；x : WithAbs v；-x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAbs_neg (x : WithAbs v) : ofAbs (-x) = - ofAbs x := rfl

end Ring

section CommRing

variable [CommRing R] (v : AbsoluteValue R S)

/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (WithAbs v) := fast_instance% (equiv v).commRing

end CommRing

section Module

variable {R T : Type*} [Semiring R] (v : AbsoluteValue R S)

/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R T] : SMul (WithAbs v) T where
  smul x t := ofAbs x • t
/-
**WithAbs.smul_left_def** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：smul_left_def [SMul R T] (x : WithAbs v) (t : T) : x • t = ofAbs x • t
参数：x : WithAbs v；t : T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_left_def [SMul R T] (x : WithAbs v) (t : T) :
    x • t = ofAbs x • t := rfl
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R T] [FaithfulSMul R T] : FaithfulSMul (WithAbs v) T where
  eq_of_smul_eq_smul h := ofAbs_injective v <| FaithfulSMul.eq_of_smul_eq_smul h
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul T R] : SMul T (WithAbs v) := Equiv.smul T { toFun := ofAbs, invFun := toAbs v }
/-
**WithAbs.smul_right_def** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：smul_right_def [SMul T R] (t : T) (x : WithAbs v) : t • x = toAbs v (t • x
.ofAbs)
参数：t : T；x : WithAbs v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_right_def [SMul T R] (t : T) (x : WithAbs v) :
    t • x = toAbs v (t • x.ofAbs) := rfl
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul T R] [FaithfulSMul T R] : FaithfulSMul T (WithAbs v) where
  eq_of_smul_eq_smul h := by
    simp only [smul_right_def, toAbs.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun _ ↦ h (toAbs v _)
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : Type*} [SMul T P] [SMul R T] [SMul R P] [IsScalarTower R T P] :
    IsScalarTower (WithAbs v) T P where
  smul_assoc := by simp [smul_left_def]
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : Type*} [SMul P R] [SMul T R] [SMul P T]
    [IsScalarTower P T R] : IsScalarTower P T (WithAbs v) := (equiv v).isScalarTower P T
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : Type*} [SMul P R] [SMul P T] [SMul R T]
    [IsScalarTower P R T] : IsScalarTower P (WithAbs v) T where
  smul_assoc := by simp [smul_right_def, smul_left_def]
/-
**WithAbs.moduleLeft** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
形式化陈述：moduleLeft [AddCommMonoid T] [Module R T] : Module (WithAbs v) T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance moduleLeft [AddCommMonoid T] [Module R T] : Module (WithAbs v) T :=
  fast_instance% .compHom T (equiv v).toRingHom

@[deprecated (since := "2026-03-02")] alias instModule_left := moduleLeft
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring T] [Module T R] : Module T (WithAbs v) :=
  fast_instance% (equiv v).module T

@[deprecated (since := "2026-03-02")] alias instModule_right := instModule

variable [Semiring T] [Module R T] (v : AbsoluteValue T S)

variable (R) in
/-- The canonical `R`-linear isomorphism between `WithAbs v` and `T`, when
`v : AbsoluteValue T S`. -/
/-
**WithAbs.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithAbs`。
形式化陈述：linearEquiv : WithAbs v ≃ₗ[R] T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `R`-linear isomorphism between `WithAbs v` and `T`, when
`v : AbsoluteValue T S`.
-/
def linearEquiv : WithAbs v ≃ₗ[R] T := (equiv v).linearEquiv R

variable {v}
/-
**WithAbs.linearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder S] {R : Type u
_3} {T : Type u_4} [inst_2 : Semiring R]   [inst_3 : Semiring T] [inst_4 : _root
_.Module R T] {v : AbsoluteValue T S} (x : WithAbs v),   (WithAbs.linearEquiv R 
v) x = x.ofAbs
参数：x : WithAbs v；WithAbs.linearEquiv R v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem linearEquiv_apply (x : WithAbs v) : linearEquiv R v x = x.ofAbs := rfl
/-
**WithAbs.linearEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder S] {R : Type u
_3} {T : Type u_4} [inst_2 : Semiring R]   [inst_3 : Semiring T] [inst_4 : _root
_.Module R T] {v : AbsoluteValue T S} (x : T),   (WithAbs.linearEquiv R v).symm 
x = WithAbs.toAbs v x
参数：x : T；WithAbs.linearEquiv R v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem linearEquiv_symm_apply (x : T) : (linearEquiv R v).symm x = toAbs v x := rfl

end Module

section algebra

variable {R T : Type*} [CommSemiring R] [Semiring T] [Algebra R T]

variable (T) in
/-
**WithAbs.algebraLeft** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
形式化陈述：algebraLeft (v : AbsoluteValue R S) : Algebra (WithAbs v) T
参数：v : AbsoluteValue R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebraLeft (v : AbsoluteValue R S) : Algebra (WithAbs v) T :=
  fast_instance% .compHom T (equiv v).toRingHom
/-
**WithAbs.algebraMap_left_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：algebraMap_left_apply {v : AbsoluteValue R S} (x : WithAbs v) : algebraMap
 (WithAbs v) T x = algebraMap R T x.ofAbs
参数：x : WithAbs v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_left_apply {v : AbsoluteValue R S} (x : WithAbs v) :
    algebraMap (WithAbs v) T x = algebraMap R T x.ofAbs := rfl
/-
**WithAbs.algebraMap_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：algebraMap_left_injective (v : AbsoluteValue R S) (h : Function.Injective 
(algebraMap R T)) : Function.Injective (algebraMap (WithAbs v) T)
参数：v : AbsoluteValue R S；h : Function.Injective (algebraMap R T)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `WithAbs.ofAbs_injective`：ofAbs_injective : Function.Injective (ofAbs (v
-/
theorem algebraMap_left_injective (v : AbsoluteValue R S)
    (h : Function.Injective (algebraMap R T)) :
    Function.Injective (algebraMap (WithAbs v) T) :=
  h.comp (ofAbs_injective v)
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (v : AbsoluteValue T S) : Algebra R (WithAbs v) :=
  fast_instance% (equiv v).algebra R
/-
**WithAbs.algebraMap_right_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：algebraMap_right_apply {v : AbsoluteValue T S} (x : R) : algebraMap R (Wit
hAbs v) x = toAbs v (algebraMap R T x)
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_right_apply {v : AbsoluteValue T S} (x : R) :
    algebraMap R (WithAbs v) x = toAbs v (algebraMap R T x) := rfl
/-
**WithAbs.algebraMap_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：algebraMap_right_injective (v : AbsoluteValue T S) (h : Function.Injective
 (algebraMap R T)) : Function.Injective (algebraMap R (WithAbs v))
参数：v : AbsoluteValue T S；h : Function.Injective (algebraMap R T)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `WithAbs.toAbs_injective`：toAbs_injective : Function.Injective (toAbs v)
-/
theorem algebraMap_right_injective (v : AbsoluteValue T S)
    (h : Function.Injective (algebraMap R T)) : Function.Injective (algebraMap R (WithAbs v)) :=
  (toAbs_injective v).comp h
/-
**WithAbs.ofAbs_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：ofAbs_algebraMap (v : AbsoluteValue R S) (w : AbsoluteValue T S) (x : With
Abs v) : (algebraMap (WithAbs v) (WithAbs w) x).ofAbs = algebraMap R T x.ofAbs
参数：v : AbsoluteValue R S；w : AbsoluteValue T S；x : WithAbs v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAbs_algebraMap (v : AbsoluteValue R S) (w : AbsoluteValue T S) (x : WithAbs v) :
    (algebraMap (WithAbs v) (WithAbs w) x).ofAbs = algebraMap R T x.ofAbs := rfl

@[deprecated (since := "2026-03-02")] alias instAlgebra_left := algebraLeft
@[deprecated (since := "2026-03-02")] alias instAlgebra_right := instAlgebra

variable (R) in
/-- The canonical algebra isomorphism from an `R`-algebra `R'` with an absolute value `v`
to `R'`. -/
/-
**WithAbs.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithAbs`。
形式化陈述：algEquiv (v : AbsoluteValue T S) : (WithAbs v) ≃ₐ[R] T
参数：v : AbsoluteValue T S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical algebra isomorphism from an `R`-algebra `R'` with an absolute valu
e `v`
to `R'`.
-/
def algEquiv (v : AbsoluteValue T S) : (WithAbs v) ≃ₐ[R] T := (equiv v).algEquiv R
/-
**WithAbs.algEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder S] {R : Type u
_3} {T : Type u_4} [inst_2 : CommSemiring R]   [inst_3 : Semiring T] [inst_4 : A
lgebra R T] (v : AbsoluteValue T S) (x : WithAbs v),   (WithAbs.algEquiv R v) x 
= x.ofAbs
参数：v : AbsoluteValue T S；x : WithAbs v；WithAbs.algEquiv R v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem algEquiv_apply (v : AbsoluteValue T S) (x : WithAbs v) :
    algEquiv R v x = x.ofAbs := rfl
/-
**WithAbs.algEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder S] {R : Type u
_3} {T : Type u_4} [inst_2 : CommSemiring R]   [inst_3 : Semiring T] [inst_4 : A
lgebra R T] (v : AbsoluteValue T S) (x : T),   (WithAbs.algEquiv R v).symm x = W
ithAbs.toAbs v x
参数：v : AbsoluteValue T S；x : T；WithAbs.algEquiv R v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem algEquiv_symm_apply (v : AbsoluteValue T S) (x : T) :
    (algEquiv R v).symm x = toAbs v x := rfl

end algebra

end WithAbs

namespace AbsoluteValue

variable {K L S : Type*} [CommRing K] [IsSimpleRing K] [CommRing L] [Algebra K L] [PartialOrder S]
  [Nontrivial L] [Semiring S]

/-- An absolute value `w` of `L / K` lies over the absolute value `v` of `K` if `v` is the
restriction of `w` to `K`. -/
/-
**AbsoluteValue.LiesOver** 是 Mathlib 中的一个归纳类型，位于命名空间 `AbsoluteValue`。
形式化陈述：{K : Type u_3} →   {L : Type u_4} →     {S : Type u_5} →       [inst : Com
mRing K] →         [IsSimpleRing K] →           [inst_2 : CommRing L] →         
    [Algebra K L] →               [inst_4 : PartialOrder S] →                 [N
ontrivial L] → [inst_6 : Semiring S] → AbsoluteValue L S → AbsoluteValue K S → P
rop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An absolute value `w` of `L / K` lies over the absolute value `v` of `K` if `v` 
is the
restriction of `w` to `K`.
-/
class LiesOver (w : AbsoluteValue L S) (v : AbsoluteValue K S) : Prop where
  comp_eq (w) (v) : w.comp (algebraMap K L).injective = v

end AbsoluteValue

