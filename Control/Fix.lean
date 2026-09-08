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

variable {α : Type*} {β : α → Type*}

/-- `Fix α` provides a `fix` operator to define recursive computation
via the fixed point of function of type `α → α`. -/
/-
**Fix** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fix α` provides a `fix` operator to define recursive computation
via the fixed point of function of type `α → α`.
-/
class Fix (α : Type*) where
  /-- `fix f` represents the computation of a fixed point for `f`. -/
  fix : (α → α) → α

namespace Part

open Part Nat Nat.Upto

section Basic

variable (f : (∀ a, Part (β a)) → (∀ a, Part (β a)))

/-- A series of successive, finite approximation of the fixed point of `f`, defined by
`approx f n = f^[n] ⊥`. The limit of this chain is the fixed point of `f`. -/
/-
**Part.Fix.approx** 是 Mathlib 中的一个定义，位于命名空间 `Part.Fix`。
形式化陈述：{α : Type u_1} → {β : α → Type u_2} → (((a : α) → Part (β a)) → (a : α) → 
Part (β a)) → Stream' ((a : α) → Part (β a))
参数：((a : α) → Part (β a)) → (a : α) → Part (β a)；(a : α) → Part (β a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A series of successive, finite approximation of the fixed point of `f`, defined 
by
`approx f n = f^[n] ⊥`. The limit of this chain is the fixed point of `f`.
-/
def Fix.approx : Stream' (∀ a, Part (β a))
  | 0 => ⊥
  | Nat.succ i => f (Fix.approx i)

/-- loop body for finding the fixed point of `f` -/
/-
**Part.fixAux** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：fixAux {p : Nat -> Prop} (i : Nat.Upto p) (g : forall j : Nat.Upto p, i < 
j -> forall a, Part (β a)) : forall a, Part (β a)
参数：i : Nat.Upto p；g : forall j : Nat.Upto p, i < j -> forall a, Part (β a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
loop body for finding the fixed point of `f`
-/
def fixAux {p : ℕ → Prop} (i : Nat.Upto p) (g : ∀ j : Nat.Upto p, i < j → ∀ a, Part (β a)) :
    ∀ a, Part (β a) :=
  f fun x : α => (assert ¬p i.val) fun h : ¬p i.val => g (i.succ h) (Nat.lt_succ_self _) x

/-- The least fixed point of `f`.

If `f` is a continuous function (according to complete partial orders),
it satisfies the equations:

  1. `fix f = f (fix f)`          (is a fixed point)
  2. `∀ X, f X ≤ X → fix f ≤ X`   (least fixed point)
-/
/-
**Part.fix** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
形式化陈述：{α : Type u_1} → {β : α → Type u_2} → (((a : α) → Part (β a)) → (a : α) → 
Part (β a)) → (x : α) → Part (β x)
参数：((a : α) → Part (β a)) → (a : α) → Part (β a)；x : α；β x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The least fixed point of `f`.

If `f` is a continuous function (according to complete partial orders),
it satisfies the equations:

  1. `fix f = f (fix f)`          (is a fixed point)
  2. `∀ X, f X ≤ X → fix f ≤ X`   (least fixed point)
-/
protected def fix (x : α) : Part (β x) :=
  (Part.assert (∃ i, (Fix.approx f i x).Dom)) fun h =>
    WellFounded.fix.{1} (Nat.Upto.wf h) (fixAux f) Nat.Upto.zero x

open scoped Classical in
/-
**Part.fix_def** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：∀ {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → Part (β a)) → (a : α) 
→ Part (β a)) {x : α}   (h' : ∃ i, (Part.Fix.approx f i x).Dom), Part.fix f x = 
Part.Fix.approx f (Nat.find h').succ x
参数：f : ((a : α) → Part (β a)) → (a : α) → Part (β a)；h' : ∃ i, (Part.Fix.approx 
f i x).Dom；Nat.find h'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.assert_pos`：assert_pos {p : Prop} {f : p -> Part α} (h : p) : asser
t p f = f h
· 使用定理 `Part.Fix.approx.eq_2`：∀ {α : Type u_1} {β : α → Type u_2} (f : ((a : α) 
→ Part (β a)) → (a : α) → Part (β a)) (i : ℕ),   Part.Fix.approx f i.succ = f (P
art.Fix.ap…
· 使用定理 `WellFounded.fix_eq`：∀ {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (
hwf : WellFounded r) (F : (x : α) → ((y : α) → r y x → C y) → C x)   (x : α), hw
f.fix F …
· 使用定理 `Part.fixAux.eq_1`：∀ {α : Type u_1} {β : α → Type u_2} (f : ((a : α) → Pa
rt (β a)) → (a : α) → Part (β a)) {p : ℕ → Prop} (i : Nat.Upto p)   (g : (j : Na
t.Upto…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Part.assert_neg`：assert_neg {p : Prop} {f : p -> Part α} (h : ¬p) : asse
rt p f = none
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Nat.succ_add_eq_add_succ`：∀ (a b : ℕ), a.succ + b = a + b.succ
-/
protected theorem fix_def {x : α} (h' : ∃ i, (Fix.approx f i x).Dom) :
    Part.fix f x = Fix.approx f (Nat.succ (Nat.find h')) x := by
  let p := fun i : ℕ => (Fix.approx f i x).Dom
  have : p (Nat.find h') := Nat.find_spec h'
  generalize hk : Nat.find h' = k
  replace hk : Nat.find h' = k + (@Upto.zero p).val := hk
  rw [hk] at this
  revert hk
  dsimp [Part.fix]; rw [assert_pos h']; revert this
  generalize Upto.zero = z; intro _this hk
  suffices ∀ x' hwf,
    WellFounded.fix hwf (fixAux f) z x' = Fix.approx f (succ k) x'
    from this _ _
  induction k generalizing z with
  | zero =>
    intro x' _
    rw [Fix.approx, WellFounded.fix_eq, fixAux]
    congr
    ext x : 1
    rw [assert_neg]
    · rfl
    · rw [Nat.zero_add] at _this
      simpa only [not_not, Coe]
  | succ n n_ih =>
    intro x' _
    rw [Fix.approx, WellFounded.fix_eq, fixAux]
    congr
    ext : 1
    have hh : ¬(Fix.approx f z.val x).Dom := by
      apply Nat.find_min h'
      lia
    rw [succ_add_eq_add_succ] at _this hk
    rw [assert_pos hh, n_ih (Upto.succ z hh) _this hk]
/-
**Part.fix_def'** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：fix_def' {x : α} (h' : ¬exists i, (Fix.approx f i x).Dom) : Part.fix f x =
 none
参数：h' : ¬exists i, (Fix.approx f i x).Dom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.assert_neg`：assert_neg {p : Prop} {f : p -> Part α} (h : ¬p) : asse
rt p f = none
-/
theorem fix_def' {x : α} (h' : ¬∃ i, (Fix.approx f i x).Dom) : Part.fix f x = none := by
  dsimp [Part.fix]
  rw [assert_neg h']

end Basic

end Part

namespace Part

/-
**Part.hasFix** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
形式化陈述：hasFix : Fix (Part α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasFix : Fix (Part α) :=
  ⟨fun f => Part.fix (fun x u => f (x u)) ()⟩

end Part

open Sigma

namespace Pi

/-
**Pi.Part.hasFix** 是 Mathlib 中的一个定义，位于命名空间 `Pi.Part`。
形式化陈述：{α : Type u_1} → {β : Type u_3} → Fix (α → Part β)
参数：α → Part β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Part.hasFix {β} : Fix (α → Part β) :=
  ⟨Part.fix⟩

end Pi

