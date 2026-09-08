/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Ring.Pi

/-!
# Pi instances for modules

This file defines instances for module and related structures on Pi Types
-/

public section


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

namespace Pi

/-
**Pi._root_.IsSMulRegular.pi** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsSMulRegular.pi {α : Type*} [∀ i, SMul α <| f i] {k : α}
    (hk : ∀ i, IsSMulRegular (f i) k) : IsSMulRegular (∀ i, f i) k := fun _ _ h =>
  funext fun i => hk i (congr_fun h i :)

variable (I f)
/-
**Pi.module** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：module (α) {r : Semiring α} {m : forall i, AddCommMonoid <| f i} [forall i
, Module α <| f i] : @Module α (forall i : I, f i) r (@Pi.addCommMonoid I f m)
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module (α) {r : Semiring α} {m : ∀ i, AddCommMonoid <| f i} [∀ i, Module α <| f i] :
    @Module α (∀ i : I, f i) r (@Pi.addCommMonoid I f m) :=
  { Pi.distribMulAction _ with
    add_smul := fun _ _ _ => funext fun _ => add_smul _ _ _
    zero_smul := fun _ => funext fun _ => zero_smul α _ }

/- Extra instance to short-circuit type class resolution.
For unknown reasons, this is necessary for certain inference problems. E.g., for this to succeed:
```lean
example (β X : Type*) [NormedAddCommGroup β] [NormedSpace ℝ β] : Module ℝ (X → β) := inferInstance
```
See: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/281296989
-/
/-- A special case of `Pi.module` for non-dependent types. Lean struggles to elaborate
definitions elsewhere in the library without this. -/
/-
**Pi.Function.module** 是 Mathlib 中的一个定义，位于命名空间 `Pi.Function`。
形式化陈述：(I : Type u) →   (α : Type u_1) →     (β : Type u_2) → [inst : Semiring α]
 → [inst_1 : AddCommMonoid β] → [_root_.Module α β] → _root_.Module α (I → β)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A special case of `Pi.module` for non-dependent types. Lean struggles to elabora
te
definitions elsewhere in the library without this.
-/
instance Function.module (α β : Type*) [Semiring α] [AddCommMonoid β] [Module α β] :
    Module α (I → β) :=
  Pi.module _ _ _

variable {I f}
/-
**Pi.module'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：module' {g : I -> Type*} {r : forall i, Semiring (f i)} {m : forall i, Add
CommMonoid (g i)} [forall i, Module (f i) (g i)] : Module (forall i, f i) (foral
l i, g i) where add_smul
参数：f i；g i；f i；g i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module' {g : I → Type*} {r : ∀ i, Semiring (f i)} {m : ∀ i, AddCommMonoid (g i)}
    [∀ i, Module (f i) (g i)] : Module (∀ i, f i) (∀ i, g i) where
  add_smul := by
    intros
    ext1
    apply add_smul
  zero_smul := by
    intros
    ext1
    rw [zero_smul]

end Pi

