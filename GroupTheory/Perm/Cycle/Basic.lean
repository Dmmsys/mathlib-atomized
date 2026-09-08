/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Cycles of a permutation

This file starts the theory of cycles in permutations.

## Main definitions

In the following, `f : Equiv.Perm β`.

* `Equiv.Perm.SameCycle`: `f.SameCycle x y` when `x` and `y` are in the same cycle of `f`.
* `Equiv.Perm.IsCycle`: `f` is a cycle if any two nonfixed points of `f` are related by repeated
  applications of `f`, and `f` is not the identity.
* `Equiv.Perm.IsCycleOn`: `f` is a cycle on a set `s` when any two points of `s` are related by
  repeated applications of `f`.

## Notes

`Equiv.Perm.IsCycle` and `Equiv.Perm.IsCycleOn` are different in three ways:
* `IsCycle` is about the entire type while `IsCycleOn` is restricted to a set.
* `IsCycle` forbids the identity while `IsCycleOn` allows it (if `s` is a subsingleton).
* `IsCycleOn` forbids fixed points on `s` (if `s` is nontrivial), while `IsCycle` allows them.
-/

@[expose] public section


open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

/-! ### `SameCycle` -/

section SameCycle

variable {f g : Perm α} {p : α → Prop} {x y z : α}

/-- The equivalence relation indicating that two points are in the same cycle of a permutation. -/
/-
**Equiv.Perm.SameCycle** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：SameCycle (f : Perm α) (x y : α) : Prop
参数：f : Perm α；x y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence relation indicating that two points are in the same cycle of a p
ermutation.
-/
def SameCycle (f : Perm α) (x y : α) : Prop :=
  ∃ i : ℤ, (f ^ i) x = y

@[refl]
/-
**Equiv.Perm.SameCycle.refl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCycle`。
形式化陈述：∀ {α : Type u_2} (f : Equiv.Perm α) (x : α), f.SameCycle x x
参数：f : Equiv.Perm α；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SameCycle.refl (f : Perm α) (x : α) : SameCycle f x x :=
  ⟨0, rfl⟩
/-
**Equiv.Perm.SameCycle.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x : α}, f.SameCycle x x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.refl`：∀ {α : Type u_2} (f : Equiv.Perm α) (x : α), 
f.SameCycle x x
-/
theorem SameCycle.rfl : SameCycle f x x :=
  SameCycle.refl _ _
/-
**Equiv.Perm._root_.Eq.sameCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Eq.sameCycle (h : x = y) (f : Perm α) : f.SameCycle x y := by rw [h]

@[symm]
/-
**Equiv.Perm.SameCycle.symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}, f.SameCycle x y → f.SameCyc
le y x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SameCycle.symm : SameCycle f x y → SameCycle f y x := fun ⟨i, hi⟩ =>
  ⟨-i, by simp [zpow_neg, ← hi]⟩
/-
**Equiv.Perm.sameCycle_comm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_comm : SameCycle f x y ↔ SameCycle f y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.symm`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}
, f.SameCycle x y → f.SameCycle y x
-/
theorem sameCycle_comm : SameCycle f x y ↔ SameCycle f y x :=
  ⟨SameCycle.symm, SameCycle.symm⟩

@[trans]
/-
**Equiv.Perm.SameCycle.trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y z : α}, f.SameCycle x y → f.SameC
ycle y z → f.SameCycle x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
-/
theorem SameCycle.trans : SameCycle f x y → SameCycle f y z → SameCycle f x z :=
  fun ⟨i, hi⟩ ⟨j, hj⟩ => ⟨j + i, by rw [zpow_add, mul_apply, hi, hj]⟩

variable (f) in
/-
**Equiv.Perm.SameCycle.equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCyc
le`。
形式化陈述：∀ {α : Type u_2} (f : Equiv.Perm α), Equivalence f.SameCycle
参数：f : Equiv.Perm α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.refl`：∀ {α : Type u_2} (f : Equiv.Perm α) (x : α), 
f.SameCycle x x
· 使用定理 `Equiv.Perm.SameCycle.symm`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}
, f.SameCycle x y → f.SameCycle y x
· 使用定理 `Equiv.Perm.SameCycle.trans`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y z :
 α}, f.SameCycle x y → f.SameCycle y z → f.SameCycle x z
-/
theorem SameCycle.equivalence : Equivalence (SameCycle f) :=
  ⟨SameCycle.refl f, SameCycle.symm, SameCycle.trans⟩

/-- The setoid defined by the `SameCycle` relation. -/
@[instance_reducible]
/-
**Equiv.Perm.SameCycle.setoid** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.SameCycle`。
形式化陈述：{α : Type u_2} → Equiv.Perm α → Setoid α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.equivalence`：∀ {α : Type u_2} (f : Equiv.Perm α), E
quivalence f.SameCycle

--- 原说明 ---
The setoid defined by the `SameCycle` relation.
-/
def SameCycle.setoid (f : Perm α) : Setoid α where
  r := f.SameCycle
  iseqv := SameCycle.equivalence f

@[simp]
/-
**Equiv.Perm.sameCycle_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_one : SameCycle 1 x y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sameCycle_one : SameCycle 1 x y ↔ x = y := by simp [SameCycle]

@[simp]
/-
**Equiv.Perm.sameCycle_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_inv : SameCycle f⁻¹ x y ↔ SameCycle f x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `inv_zpow'`：inv_zpow' (a : α) (n : Int) : a⁻¹ ^ n = a ^ (-n)
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sameCycle_inv : SameCycle f⁻¹ x y ↔ SameCycle f x y :=
  (Equiv.neg _).exists_congr_left.trans <| by simp [SameCycle]

alias ⟨SameCycle.of_inv, SameCycle.inv⟩ := sameCycle_inv

@[simp]
/-
**Equiv.Perm.sameCycle_conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_conj : SameCycle (g * f * g⁻¹) x y ↔ SameCycle f (g⁻¹ x) (g⁻¹ y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `conj_zpow`：conj_zpow {i : Int} {a b : α} : (a * b * a⁻¹) ^ i = a * b ^ i
 * a⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sameCycle_conj : SameCycle (g * f * g⁻¹) x y ↔ SameCycle f (g⁻¹ x) (g⁻¹ y) :=
  exists_congr fun i => by simp [conj_zpow, eq_symm_apply]
/-
**Equiv.Perm.SameCycle.conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCycle`。
形式化陈述：∀ {α : Type u_2} {f g : Equiv.Perm α} {x y : α}, f.SameCycle x y → (g * f 
* g⁻¹).SameCycle (g x) (g y)
参数：g * f * g⁻¹；g x；g y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem SameCycle.conj : SameCycle f x y → SameCycle (g * f * g⁻¹) (g x) (g y) := by
  simp [sameCycle_conj]
/-
**Equiv.Perm.SameCycle.apply_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.S
ameCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}, f.SameCycle x y → (f x = x 
↔ f y = y)
参数：f x = x ↔ f y = y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用引理 `zpow_one_add`：zpow_one_add (a : G) (n : Int) : a ^ (1 + n) = a * a ^ n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem SameCycle.apply_eq_self_iff : SameCycle f x y → (f x = x ↔ f y = y) := fun ⟨i, hi⟩ => by
  rw [← hi, ← mul_apply, ← zpow_one_add, add_comm, zpow_add_one, mul_apply,
    (f ^ i).injective.eq_iff]
/-
**Equiv.Perm.SameCycle.eq_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCycl
e`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}, f.SameCycle x y → Function.
IsFixedPt (⇑f) x → x = y
参数：⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `Function.IsFixedPt.perm_zpow`：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α
}, Function.IsFixedPt (⇑e) x → ∀ (n : ℤ), Function.IsFixedPt (⇑(e ^ n)) x
-/
theorem SameCycle.eq_of_left (h : SameCycle f x y) (hx : IsFixedPt f x) : x = y :=
  let ⟨_, hn⟩ := h
  (hx.perm_zpow _).eq.symm.trans hn
/-
**Equiv.Perm.SameCycle.eq_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCyc
le`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}, f.SameCycle x y → Function.
IsFixedPt (⇑f) y → x = y
参数：⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.eq_of_left`：∀ {α : Type u_2} {f : Equiv.Perm α} {x 
y : α}, f.SameCycle x y → Function.IsFixedPt (⇑f) x → x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.SameCycle.apply_eq_self_iff`：∀ {α : Type u_2} {f : Equiv.Perm
 α} {x y : α}, f.SameCycle x y → (f x = x ↔ f y = y)
-/
theorem SameCycle.eq_of_right (h : SameCycle f x y) (hy : IsFixedPt f y) : x = y :=
  h.eq_of_left <| h.apply_eq_self_iff.2 hy

@[simp]
/-
**Equiv.Perm.sameCycle_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_apply_left : SameCycle f (f x) y ↔ SameCycle f x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.addRight_symm`：∀ {G : Type u_5} [inst : AddGroup G] (a : G), Equiv
.symm (Equiv.addRight a) = Equiv.addRight (-a)
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sameCycle_apply_left : SameCycle f (f x) y ↔ SameCycle f x y :=
  (Equiv.addRight 1).exists_congr_left.trans <| by
    simp [zpow_sub, SameCycle, Int.add_neg_one, Function.comp]

@[simp]
/-
**Equiv.Perm.sameCycle_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_apply_right : SameCycle f x (f y) ↔ SameCycle f x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sameCycle_comm`：sameCycle_comm : SameCycle f x y ↔ SameCycle 
f y x
· 使用定理 `Equiv.Perm.sameCycle_apply_left`：sameCycle_apply_left : SameCycle f (f x
) y ↔ SameCycle f x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sameCycle_apply_right : SameCycle f x (f y) ↔ SameCycle f x y := by
  rw [sameCycle_comm, sameCycle_apply_left, sameCycle_comm]

@[simp]
/-
**Equiv.Perm.sameCycle_symm_apply_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_symm_apply_left : SameCycle f (f.symm x) y ↔ SameCycle f x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sameCycle_apply_left`：sameCycle_apply_left : SameCycle f (f x
) y ↔ SameCycle f x y
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sameCycle_symm_apply_left : SameCycle f (f.symm x) y ↔ SameCycle f x y := by
  rw [← sameCycle_apply_left, apply_symm_apply]

@[simp]
/-
**Equiv.Perm.sameCycle_symm_apply_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_symm_apply_right : SameCycle f x (f.symm y) ↔ SameCycle f x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.sameCycle_apply_right`：sameCycle_apply_right : SameCycle f x 
(f y) ↔ SameCycle f x y
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sameCycle_symm_apply_right : SameCycle f x (f.symm y) ↔ SameCycle f x y := by
  rw [← sameCycle_apply_right, apply_symm_apply]

@[simp]
/-
**Equiv.Perm.sameCycle_zpow_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_zpow_left {n : Int} : SameCycle f ((f ^ n) x) y ↔ SameCycle f x 
y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.addRight_symm`：∀ {G : Type u_5} [inst : AddGroup G] (a : G), Equiv
.symm (Equiv.addRight a) = Equiv.addRight (-a)
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sameCycle_zpow_left {n : ℤ} : SameCycle f ((f ^ n) x) y ↔ SameCycle f x y :=
  (Equiv.addRight (n : ℤ)).exists_congr_left.trans <| by simp [SameCycle, zpow_add]

@[simp]
/-
**Equiv.Perm.sameCycle_zpow_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_zpow_right {n : Int} : SameCycle f x ((f ^ n) y) ↔ SameCycle f x
 y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.sameCycle_comm`：sameCycle_comm : SameCycle f x y ↔ SameCycle 
f y x
· 使用定理 `Equiv.Perm.sameCycle_zpow_left`：sameCycle_zpow_left {n : Int} : SameCycl
e f ((f ^ n) x) y ↔ SameCycle f x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sameCycle_zpow_right {n : ℤ} : SameCycle f x ((f ^ n) y) ↔ SameCycle f x y := by
  rw [sameCycle_comm, sameCycle_zpow_left, sameCycle_comm]

@[simp]
/-
**Equiv.Perm.sameCycle_pow_left** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_pow_left {n : Nat} : SameCycle f ((f ^ n) x) y ↔ SameCycle f x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Equiv.Perm.sameCycle_zpow_left`：sameCycle_zpow_left {n : Int} : SameCycl
e f ((f ^ n) x) y ↔ SameCycle f x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sameCycle_pow_left {n : ℕ} : SameCycle f ((f ^ n) x) y ↔ SameCycle f x y := by
  rw [← zpow_natCast, sameCycle_zpow_left]

@[simp]
/-
**Equiv.Perm.sameCycle_pow_right** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_pow_right {n : Nat} : SameCycle f x ((f ^ n) y) ↔ SameCycle f x 
y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Equiv.Perm.sameCycle_zpow_right`：sameCycle_zpow_right {n : Int} : SameCy
cle f x ((f ^ n) y) ↔ SameCycle f x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sameCycle_pow_right {n : ℕ} : SameCycle f x ((f ^ n) y) ↔ SameCycle f x y := by
  rw [← zpow_natCast, sameCycle_zpow_right]

alias ⟨SameCycle.of_apply_left, SameCycle.apply_left⟩ := sameCycle_apply_left

alias ⟨SameCycle.of_apply_right, SameCycle.apply_right⟩ := sameCycle_apply_right

alias ⟨SameCycle.of_symm_apply_left, SameCycle.symm_apply_left⟩ := sameCycle_symm_apply_left

alias ⟨SameCycle.of_symm_apply_right, SameCycle.symm_apply_right⟩ := sameCycle_symm_apply_right

alias ⟨SameCycle.of_pow_left, SameCycle.pow_left⟩ := sameCycle_pow_left

alias ⟨SameCycle.of_pow_right, SameCycle.pow_right⟩ := sameCycle_pow_right

alias ⟨SameCycle.of_zpow_left, SameCycle.zpow_left⟩ := sameCycle_zpow_left

alias ⟨SameCycle.of_zpow_right, SameCycle.zpow_right⟩ := sameCycle_zpow_right
/-
**Equiv.Perm.SameCycle.of_pow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α} {n : ℕ}, (f ^ n).SameCycle x
 y → f.SameCycle x y
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SameCycle.of_pow {n : ℕ} : SameCycle (f ^ n) x y → SameCycle f x y := fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩
/-
**Equiv.Perm.SameCycle.of_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.SameCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α} {n : ℤ}, (f ^ n).SameCycle x
 y → f.SameCycle x y
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SameCycle.of_zpow {n : ℤ} : SameCycle (f ^ n) x y → SameCycle f x y := fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩

@[simp]
/-
**Equiv.Perm.sameCycle_subtypePerm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_subtypePerm {h} {x y : { x // p x }} : (f.subtypePerm h).SameCyc
le x y ↔ f.SameCycle x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Algebra.Group.End.0.Equiv.Perm.zpow_aux`：∀ {α : Type u_
4} {p : α → Prop} {f : Equiv.Perm α}, (∀ (x : α), p (f x) ↔ p x) → ∀ {n : ℤ} (x 
: α), p ((f ^ n) x) ↔ p x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.Perm.subtypePerm_zpow`：subtypePerm_zpow (f : Perm α) (n : Int) (hf
) : (f.subtypePerm hf ^ n : Perm { x // p x }) = (f ^ n).subtypePerm (zpow_aux h
f)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sameCycle_subtypePerm {h} {x y : { x // p x }} :
    (f.subtypePerm h).SameCycle x y ↔ f.SameCycle x y :=
  exists_congr fun n => by simp [Subtype.ext_iff]

alias ⟨_, SameCycle.subtypePerm⟩ := sameCycle_subtypePerm

@[simp]
/-
**Equiv.Perm.sameCycle_extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：sameCycle_extendDomain {p : β -> Prop} [DecidablePred p] {f : α ≃ Subtype 
p} : SameCycle (g.extendDomain f) (f x) (f y) ↔ g.SameCycle x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Equiv.Perm.extendDomain_zpow`：extendDomain_zpow (n : Int) : (e ^ n).exte
ndDomain f = e.extendDomain f ^ n
· 使用定理 `Equiv.Perm.extendDomain_apply_image`：∀ {α' : Type u_9} {β' : Type u_10} 
(e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p
)   (a : α'), (e.extendDo…
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sameCycle_extendDomain {p : β → Prop} [DecidablePred p] {f : α ≃ Subtype p} :
    SameCycle (g.extendDomain f) (f x) (f y) ↔ g.SameCycle x y :=
  exists_congr fun n => by
    rw [← extendDomain_zpow, extendDomain_apply_image, Subtype.coe_inj, f.injective.eq_iff]

alias ⟨_, SameCycle.extendDomain⟩ := sameCycle_extendDomain
/-
**Equiv.Perm.SameCycle.exists_pow_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Same
Cycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α} [Finite α], f.SameCycle x y 
→ ∃ i < orderOf f, (f ^ i) x = y
参数：f ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用引理 `zpow_mod_orderOf`：zpow_mod_orderOf (x : G) (z : Int) : x ^ (z % (orderOf
 x : Int)) = x ^ z
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `Int.emod_lt_of_pos`：∀ (a : ℤ) {b : ℤ}, 0 < b → a % b < b
-/
theorem SameCycle.exists_pow_eq' [Finite α] : SameCycle f x y → ∃ i < orderOf f, (f ^ i) x = y := by
  rintro ⟨k, rfl⟩
  use (k % orderOf f).natAbs
  have h₀ := Int.natCast_pos.mpr (orderOf_pos f)
  have h₁ := Int.emod_nonneg k h₀.ne'
  rw [← zpow_natCast, Int.natAbs_of_nonneg h₁, zpow_mod_orderOf]
  refine ⟨?_, by rfl⟩
  rw [← Int.ofNat_lt, Int.natAbs_of_nonneg h₁]
  exact Int.emod_lt_of_pos _ h₀
/-
**Equiv.Perm.SameCycle.exists_pow_eq''** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Sam
eCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α} [Finite α], f.SameCycle x y 
→ ∃ i, 0 < i ∧ i ≤ orderOf f ∧ (f ^ i) x = y
参数：f ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.exists_pow_eq'`：∀ {α : Type u_2} {f : Equiv.Perm α}
 {x y : α} [Finite α], f.SameCycle x y → ∃ i < orderOf f, (f ^ i) x = y
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem SameCycle.exists_pow_eq'' [Finite α] (h : SameCycle f x y) :
    ∃ i : ℕ, 0 < i ∧ i ≤ orderOf f ∧ (f ^ i) x = y := by
  obtain ⟨_ | i, hi, rfl⟩ := h.exists_pow_eq'
  · refine ⟨orderOf f, orderOf_pos f, le_rfl, ?_⟩
    rw [pow_orderOf_eq_one, pow_zero]
  · exact ⟨i.succ, i.zero_lt_succ, hi.le, by rfl⟩
/-
**Equiv.Perm.SameCycle.exists_fin_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.S
ameCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α} [Finite α], f.SameCycle x y 
→ ∃ i, (f ^ ↑i) x = y
参数：f ^ ↑i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.exists_pow_eq'`：∀ {α : Type u_2} {f : Equiv.Perm α}
 {x y : α} [Finite α], f.SameCycle x y → ∃ i < orderOf f, (f ^ i) x = y
-/
theorem SameCycle.exists_fin_pow_eq [Finite α] (h : SameCycle f x y) :
    ∃ i : Fin (orderOf f), (f ^ (i : ℕ)) x = y := by
  obtain ⟨i, hi, hx⟩ := SameCycle.exists_pow_eq' h
  exact ⟨⟨i, hi⟩, hx⟩
/-
**Equiv.Perm.SameCycle.exists_nat_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.S
ameCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α} [Finite α], f.SameCycle x y 
→ ∃ i, (f ^ i) x = y
参数：f ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.exists_pow_eq'`：∀ {α : Type u_2} {f : Equiv.Perm α}
 {x y : α} [Finite α], f.SameCycle x y → ∃ i < orderOf f, (f ^ i) x = y
-/
theorem SameCycle.exists_nat_pow_eq [Finite α] (h : SameCycle f x y) :
    ∃ i : ℕ, (f ^ i) x = y := by
  obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
  exact ⟨i, hi⟩
/-
**Equiv.Perm.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : Perm α) [DecidableRel (SameCycle f)] :
    DecidableRel (SameCycle f⁻¹) := fun x y =>
  decidable_of_iff (f.SameCycle x y) sameCycle_inv.symm
/-
**Equiv.Perm.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [DecidableEq α] : DecidableRel (SameCycle (1 : Perm α)) := fun x y =>
  decidable_of_iff (x = y) sameCycle_one.symm

end SameCycle

/-!
### `IsCycle`
-/

section IsCycle

variable {f g : Perm α} {x y : α}

/-- A cycle is a non-identity permutation where any two nonfixed points of the permutation are
related by repeated application of the permutation. -/
/-
**Equiv.Perm.IsCycle** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：IsCycle (f : Perm α) : Prop
参数：f : Perm α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cycle is a non-identity permutation where any two nonfixed points of the permu
tation are
related by repeated application of the permutation.
-/
def IsCycle (f : Perm α) : Prop :=
  ∃ x, f x ≠ x ∧ ∀ ⦃y⦄, f y ≠ y → SameCycle f x y
/-
**Equiv.Perm.IsCycle.ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycle → f ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem IsCycle.ne_one (h : IsCycle f) : f ≠ 1 := fun hf => by simp [hf, IsCycle] at h

@[simp]
/-
**Equiv.Perm.not_isCycle_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：not_isCycle_one : ¬(1 : Perm α).IsCycle
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1
-/
theorem not_isCycle_one : ¬(1 : Perm α).IsCycle := fun H => H.ne_one rfl
/-
**Equiv.Perm.IsCycle.sameCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}, f.IsCycle → f x ≠ x → f y ≠
 y → f.SameCycle x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
protected theorem IsCycle.sameCycle (hf : IsCycle f) (hx : f x ≠ x) (hy : f y ≠ y) :
    SameCycle f x y :=
  let ⟨g, hg⟩ := hf
  let ⟨a, ha⟩ := hg.2 hx
  let ⟨b, hb⟩ := hg.2 hy
  ⟨b - a, by rw [← ha, ← mul_apply, ← zpow_add, sub_add_cancel, hb]⟩
/-
**Equiv.Perm.IsCycle.exists_zpow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycl
e`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}, f.IsCycle → f x ≠ x → f y ≠
 y → ∃ i, (f ^ i) x = y
参数：f ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycle.sameCycle`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y :
 α}, f.IsCycle → f x ≠ x → f y ≠ y → f.SameCycle x y
-/
theorem IsCycle.exists_zpow_eq : IsCycle f → f x ≠ x → f y ≠ y → ∃ i : ℤ, (f ^ i) x = y :=
  IsCycle.sameCycle
/-
**Equiv.Perm.IsCycle.inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycle → f⁻¹.IsCycle
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Equiv.Perm.inv_eq_iff_eq`：inv_eq_iff_eq {f : Perm α} {x y : α} : f⁻¹ x =
 y ↔ x = f y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Equiv.Perm.SameCycle.inv`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α},
 f.SameCycle x y → f⁻¹.SameCycle x y
-/
theorem IsCycle.inv (hf : IsCycle f) : IsCycle f⁻¹ :=
  hf.imp fun _ ⟨hx, h⟩ =>
    ⟨inv_eq_iff_eq.not.2 hx.symm, fun _ hy => (h <| inv_eq_iff_eq.not.2 hy.symm).inv⟩

@[simp]
/-
**Equiv.Perm.isCycle_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycle_inv : IsCycle f⁻¹ ↔ IsCycle f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycle.inv`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycle →
 f⁻¹.IsCycle
-/
theorem isCycle_inv : IsCycle f⁻¹ ↔ IsCycle f :=
  ⟨fun h => h.inv, IsCycle.inv⟩
/-
**Equiv.Perm.IsCycle.conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f g : Equiv.Perm α}, f.IsCycle → (g * f * g⁻¹).IsCycle
参数：g * f * g⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Equiv.Perm.SameCycle.conj`：∀ {α : Type u_2} {f g : Equiv.Perm α} {x y : 
α}, f.SameCycle x y → (g * f * g⁻¹).SameCycle (g x) (g y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Equiv.Perm.eq_inv_iff_eq`：eq_inv_iff_eq {f : Perm α} {x y : α} : x = f⁻¹
 y ↔ f x = y
-/
theorem IsCycle.conj : IsCycle f → IsCycle (g * f * g⁻¹) := by
  rintro ⟨x, hx, h⟩
  refine ⟨g x, by simp [coe_mul, hx], fun y hy => ?_⟩
  simpa using (h <| eq_inv_iff_eq.not.2 hy).conj (g := g)
/-
**Equiv.Perm.IsCycle.extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`
。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {g : Equiv.Perm α} {p : β → Prop} [inst : 
DecidablePred p] (f : α ≃ Subtype p),   g.IsCycle → (g.extendDomain f).IsCycle
参数：f : α ≃ Subtype p；g.extendDomain f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.extendDomain_apply_image`：∀ {α' : Type u_9} {β' : Type u_10} 
(e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Subtype p
)   (a : α'), (e.extendDo…
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Equiv.Perm.extendDomain_apply_not_subtype`：∀ {α' : Type u_9} {β' : Type 
u_10} (e : Equiv.Perm α') {p : β' → Prop} [inst : DecidablePred p] (f : α' ≃ Sub
type p)   {b : β'}, ¬p b → (e.e…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Equiv.Perm.SameCycle.extendDomain`：∀ {α : Type u_2} {β : Type u_3} {g : 
Equiv.Perm α} {x y : α} {p : β → Prop} [inst : DecidablePred p]   {f : α ≃ Subty
pe p}, g.SameCycle x y …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
-/
protected theorem IsCycle.extendDomain {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p) :
    IsCycle g → IsCycle (g.extendDomain f) := by
  rintro ⟨a, ha, ha'⟩
  refine ⟨f a, ?_, fun b hb => ?_⟩
  · rw [extendDomain_apply_image]
    exact Subtype.coe_injective.ne (f.injective.ne ha)
  have h : b = f (f.symm ⟨b, of_not_not <| hb ∘ extendDomain_apply_not_subtype _ _⟩) := by
    rw [apply_symm_apply, Subtype.coe_mk]
  rw [h] at hb ⊢
  simp only [extendDomain_apply_image, Subtype.coe_injective.ne_iff, f.injective.ne_iff] at hb
  exact (ha' hb).extendDomain
/-
**Equiv.Perm.isCycle_iff_sameCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycle_iff_sameCycle (hx : f x != x) : IsCycle f ↔ forall {y}, SameCycle 
f x y ↔ f y != y
参数：hx : f x != x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self`：∀ {α : Type u_1} {f : Eq
uiv.Perm α} {x : α}, f x = x → ∀ (n : ℤ), (f ^ n) x = x
· 使用定理 `Equiv.Perm.IsCycle.exists_zpow_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {
x y : α}, f.IsCycle → f x ≠ x → f y ≠ y → ∃ i, (f ^ i) x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem isCycle_iff_sameCycle (hx : f x ≠ x) : IsCycle f ↔ ∀ {y}, SameCycle f x y ↔ f y ≠ y :=
  ⟨fun hf y =>
    ⟨fun ⟨i, hi⟩ hy =>
      hx <| by
        rw [← zpow_apply_eq_self_of_apply_eq_self hy i, (f ^ i).injective.eq_iff] at hi
        rw [hi, hy],
      hf.exists_zpow_eq hx⟩,
    fun h => ⟨x, hx, fun _ hy => h.2 hy⟩⟩

section Finite

variable [Finite α]

/-
**Equiv.Perm.IsCycle.exists_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle
`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α} [Finite α], f.IsCycle → f x 
≠ x → f y ≠ y → ∃ i, (f ^ i) x = y
参数：f ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycle.exists_zpow_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {
x y : α}, f.IsCycle → f x ≠ x → f y ≠ y → ∃ i, (f ^ i) x = y
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用引理 `zpow_mod_orderOf`：zpow_mod_orderOf (x : G) (z : Int) : x ^ (z % (orderOf
 x : Int)) = x ^ z
-/
theorem IsCycle.exists_pow_eq (hf : IsCycle f) (hx : f x ≠ x) (hy : f y ≠ y) :
    ∃ i : ℕ, (f ^ i) x = y := by
  let ⟨n, hn⟩ := hf.exists_zpow_eq hx hy
  exact
      ⟨(n % orderOf f).toNat, by
        {have := n.emod_nonneg (Int.natCast_ne_zero.mpr (ne_of_gt (orderOf_pos f)))
         rwa [← zpow_natCast, Int.toNat_of_nonneg this, zpow_mod_orderOf]}⟩

end Finite

variable [DecidableEq α]

/-
**Equiv.Perm.isCycle_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycle_swap (hxy : x != y) : IsCycle (swap x y)
参数：hxy : x != y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `Equiv.swap_apply_def`：swap_apply_def (a b x : α) : swap a b x = if x = a
 then b else if x = b then a else x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem isCycle_swap (hxy : x ≠ y) : IsCycle (swap x y) :=
  ⟨y, by rwa [swap_apply_right], fun a (ha : ite (a = x) y (ite (a = y) x a) ≠ a) =>
    if hya : y = a then ⟨0, hya⟩
    else
      ⟨1, by
        rw [zpow_one, swap_apply_def]
        split_ifs at * <;> tauto⟩⟩
/-
**Equiv.Perm.IsSwap.isCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsSwap`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : DecidableEq α], f.IsSwap → f.I
sCycle
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.isCycle_swap`：isCycle_swap (hxy : x != y) : IsCycle (swap x y
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem IsSwap.isCycle : IsSwap f → IsCycle f := by
  rintro ⟨x, y, hxy, rfl⟩
  exact isCycle_swap hxy
/-
**Equiv.Perm.swap_isSwap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：swap_isSwap_iff {a b : α} : (swap a b).IsSwap ↔ a != b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1
· 使用定理 `Equiv.Perm.IsSwap.isCycle`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : D
ecidableEq α], f.IsSwap → f.IsCycle
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_self`：swap_self (a : α) : swap a a = Equiv.refl _
-/
theorem swap_isSwap_iff {a b : α} :
    (swap a b).IsSwap ↔ a ≠ b := by
  constructor
  · intro h hab
    apply h.isCycle.ne_one
    aesop
  · intro h; use a, b

variable [Fintype α]
/-
**Equiv.Perm.IsCycle.two_le_card_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.I
sCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Finty
pe α], f.IsCycle → 2 ≤ f.support.card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.two_le_card_support_of_ne_one`：two_le_card_support_of_ne_one 
{f : Perm α} (h : f != 1) : 2 <= #f.support
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1
-/
theorem IsCycle.two_le_card_support (h : IsCycle f) : 2 ≤ #f.support :=
  two_le_card_support_of_ne_one h.ne_one

set_option backward.isDefEq.respectTransparency false in
/-- The subgroup generated by a cycle is in bijection with its support -/
/-
**Equiv.Perm.IsCycle.zpowersEquivSupport** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.I
sCycle`。
形式化陈述：{α : Type u_2} →   [inst : DecidableEq α] → [inst_1 : Fintype α] → {σ : Eq
uiv.Perm α} → σ.IsCycle → ↥(Subgroup.zpowers σ) ≃ ↥σ.support
参数：Subgroup.zpowers σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup generated by a cycle is in bijection with its support
-/
noncomputable def IsCycle.zpowersEquivSupport {σ : Perm α} (hσ : IsCycle σ) :
    (Subgroup.zpowers σ) ≃ σ.support :=
  Equiv.ofBijective
    (fun (τ : ↥((Subgroup.zpowers σ) : Set (Perm α))) =>
      ⟨(τ : Perm α) (Classical.choose hσ), by
        obtain ⟨τ, n, rfl⟩ := τ
        rw [Subtype.coe_mk, zpow_apply_mem_support, mem_support]
        exact (Classical.choose_spec hσ).1⟩)
    (by
      constructor
      · rintro ⟨a, m, rfl⟩ ⟨b, n, rfl⟩ h
        ext y
        by_cases hy : σ y = y
        · simp_rw [zpow_apply_eq_self_of_apply_eq_self hy]
        · obtain ⟨i, rfl⟩ := (Classical.choose_spec hσ).2 hy
          rw [Subtype.coe_mk, Subtype.coe_mk, zpow_apply_comm σ m i, zpow_apply_comm σ n i]
          exact congr_arg _ (Subtype.ext_iff.mp h)
      · rintro ⟨y, hy⟩
        rw [mem_support] at hy
        obtain ⟨n, rfl⟩ := (Classical.choose_spec hσ).2 hy
        exact ⟨⟨σ ^ n, n, rfl⟩, rfl⟩)

@[simp]
/-
**Equiv.Perm.IsCycle.zpowersEquivSupport_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype α] {σ : Equiv.Pe
rm α} (hσ : σ.IsCycle) {n : ℕ},   hσ.zpowersEquivSupport ⟨σ ^ n, ⋯⟩ = ⟨(σ ^ n) (
Classical.choose hσ), ⋯⟩
参数：hσ : σ.IsCycle；σ ^ n；Classical.choose hσ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsCycle.zpowersEquivSupport_apply {σ : Perm α} (hσ : IsCycle σ) {n : ℕ} :
    hσ.zpowersEquivSupport ⟨σ ^ n, n, rfl⟩ =
      ⟨(σ ^ n) (Classical.choose hσ),
        pow_apply_mem_support.2 (mem_support.2 (Classical.choose_spec hσ).1)⟩ :=
  rfl

@[simp]
/-
**Equiv.Perm.IsCycle.zpowersEquivSupport_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `E
quiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype α] {σ : Equiv.Pe
rm α} (hσ : σ.IsCycle) (n : ℕ),   hσ.zpowersEquivSupport.symm ⟨(σ ^ n) (Classica
l.choose hσ), ⋯⟩ = ⟨σ ^ n, ⋯⟩
参数：hσ : σ.IsCycle；n : ℕ；σ ^ n；Classical.choose hσ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.Perm.pow_apply_mem_support`：pow_apply_mem_support {n : Nat} {x : α
} : (f ^ n) x in f.support ↔ x in f.support
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `Equiv.Perm.IsCycle.zpowersEquivSupport_apply`：∀ {α : Type u_2} [inst : D
ecidableEq α] [inst_1 : Fintype α] {σ : Equiv.Perm α} (hσ : σ.IsCycle) {n : ℕ}, 
  hσ.zpowersEquivSupport ⟨σ ^ n, ⋯…
-/
theorem IsCycle.zpowersEquivSupport_symm_apply {σ : Perm α} (hσ : IsCycle σ) (n : ℕ) :
    hσ.zpowersEquivSupport.symm
        ⟨(σ ^ n) (Classical.choose hσ),
          pow_apply_mem_support.2 (mem_support.2 (Classical.choose_spec hσ).1)⟩ =
      ⟨σ ^ n, n, rfl⟩ :=
  (Equiv.symm_apply_eq _).2 hσ.zpowersEquivSupport_apply
/-
**Equiv.Perm.IsCycle.orderOf** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Finty
pe α], f.IsCycle → orderOf f = f.support.card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_zpowers`：Fintype.card_zpowers : Fintype.card (zpowers x) = 
orderOf x
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
protected theorem IsCycle.orderOf (hf : IsCycle f) : orderOf f = #f.support := by
  rw [← Fintype.card_zpowers, ← Fintype.card_coe]
  convert! Fintype.card_congr (IsCycle.zpowersEquivSupport hf)
/-
**Equiv.Perm.isCycle_swap_mul_aux** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isCycle_swap_mul_aux₁ {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) {b x : α} {f : Perm α} (_ : (swap x (f x) * f) b ≠ b) (_ : (f ^ n) (f x) = b),
      ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b := by
  intro n
  induction n with
  | zero => exact fun _ h => ⟨0, h⟩
  | succ n hn =>
    intro b x f hb h
    obtain hfbx | hfbx := eq_or_ne (f x) b
    · exact ⟨0, hfbx⟩
    have : f b ≠ b ∧ b ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hb
    have hb' : (swap x (f x) * f) (f.symm b) ≠ f.symm b := by
      simpa [swap_apply_of_ne_of_ne this.2 hfbx.symm, eq_symm_apply, f.injective.eq_iff]
        using this.1
    obtain ⟨i, hi⟩ := hn hb' <| f.injective <| by simpa [pow_succ'] using h
    refine ⟨i + 1, ?_⟩
    rw [add_comm, zpow_add, mul_apply, hi, zpow_one, mul_apply, apply_symm_apply,
      swap_apply_of_ne_of_ne (ne_and_ne_of_swap_mul_apply_ne_self hb).2 hfbx.symm]
/-
**Equiv.Perm.isCycle_swap_mul_aux** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isCycle_swap_mul_aux₂ {α : Type*} [DecidableEq α] :
    ∀ (n : ℤ) {b x : α} {f : Perm α}, (swap x (f x) * f) b ≠ b → (f ^ n) (f x) = b →
      ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b
  | (n : ℕ), _, _, _, hb, h => isCycle_swap_mul_aux₁ n hb h
  | .negSucc n, b, x, f, hb, h => by
    obtain hfxb | hfxb := eq_or_ne (f x) b
    · exact ⟨0, hfxb⟩
    obtain ⟨hfb, hbx⟩ : f b ≠ b ∧ b ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hb
    replace hb : (swap x (f.symm x) * f⁻¹) (f.symm b) ≠ f.symm b := by
      rw [mul_apply, swap_apply_def]
      split_ifs <;> simp [symm_apply_eq, eq_symm_apply] at * <;> tauto
    obtain ⟨i, hi⟩ := isCycle_swap_mul_aux₁ n hb <| by
      rw [← mul_apply, ← pow_succ]; simpa [pow_succ', eq_symm_apply] using! h
    refine ⟨-i, (swap x (f⁻¹ x) * f⁻¹).injective ?_⟩
    convert! hi using 1
    · rw [zpow_neg, ← inv_zpow, ← mul_apply, mul_inv_rev, swap_inv, mul_swap_eq_swap_mul]
      simp [swap_comm _ x, ← mul_apply, -coe_mul, ← inv_def, -coe_inv, ← inv_def, mul_assoc _ f⁻¹,
        ← mul_zpow_mul, mul_assoc _ _ f]
      simp
    · exact swap_apply_of_ne_of_ne (by simpa [eq_comm, eq_symm_apply, symm_apply_eq] using! hfxb)
        (by simpa [eq_comm, eq_symm_apply, symm_apply_eq])
/-
**Equiv.Perm.IsCycle.eq_swap_of_apply_apply_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `E
quiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] {f : Equiv.Perm α},   f.IsCycle → 
∀ {x : α}, f x ≠ x → f (f x) = x → f = Equiv.swap x (f x)
参数：f x；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Equiv.Perm.zpow_apply_eq_of_apply_apply_eq_self`：∀ {α : Type u_1} {f : E
quiv.Perm α} {x : α}, f (f x) = x → ∀ (i : ℤ), (f ^ i) x = x ∨ (f ^ i) x = f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem IsCycle.eq_swap_of_apply_apply_eq_self {α : Type*} [DecidableEq α] {f : Perm α}
    (hf : IsCycle f) {x : α} (hfx : f x ≠ x) (hffx : f (f x) = x) : f = swap x (f x) :=
  Equiv.ext fun y =>
    let ⟨z, hz⟩ := hf
    let ⟨i, hi⟩ := hz.2 hfx
    if hyx : y = x then by simp [hyx]
    else
      if hfyx : y = f x then by simp [hfyx, hffx]
      else by
        rw [swap_apply_of_ne_of_ne hyx hfyx]
        refine by_contradiction fun hy => ?_
        obtain ⟨j, hj⟩ := hz.2 hy
        rw [← sub_add_cancel j i, zpow_add, mul_apply, hi] at hj
        rcases zpow_apply_eq_of_apply_apply_eq_self hffx (j - i) with hji | hji
        · rw [← hj, hji] at hyx
          tauto
        · rw [← hj, hji] at hfyx
          tauto
/-
**Equiv.Perm.IsCycle.swap_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_4} [inst : DecidableEq α] {f : Equiv.Perm α},   f.IsCycle → 
∀ {x : α}, f x ≠ x → f (f x) ≠ x → (Equiv.swap x (f x) * f).IsCycle
参数：f x；Equiv.swap x (f x) * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.Perm.IsCycle.exists_zpow_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {
x y : α}, f.IsCycle → f x ≠ x → f y ≠ y → ∃ i, (f ^ i) x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self`：ne_and_ne_of_swap_mul_ap
ply_ne_self {f : Perm α} {x y : α} (hy : (swap x (f x) * f) y != y) : f y != y ∧
 y != x
· 使用定理 `Equiv.Perm.isCycle_swap_mul_aux₂`：isCycle_swap_mul_aux₂ {α : Type*} [Dec
idableEq α] : forall (n : Int) {b x : α} {f : Perm α}, (swap x (f x) * f) b != b
 -> (f ^ n) (f x) = b …
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCycle.swap_mul {α : Type*} [DecidableEq α] {f : Perm α} (hf : IsCycle f) {x : α}
    (hx : f x ≠ x) (hffx : f (f x) ≠ x) : IsCycle (swap x (f x) * f) := by
  refine ⟨f x, ?_, fun y hy ↦ ?_⟩
  · simp [swap_apply_def, mul_apply, if_neg hffx, f.injective.eq_iff, hx]
  obtain ⟨i, rfl⟩ := hf.exists_zpow_eq hx (ne_and_ne_of_swap_mul_apply_ne_self hy).1
  exact isCycle_swap_mul_aux₂ (i - 1) hy (by simp [← mul_apply, -coe_mul, ← zpow_add_one])
/-
**Equiv.Perm.IsCycle.sign** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Fintype α] {f : Equiv.Pe
rm α},   f.IsCycle → Equiv.Perm.sign f = -(-1) ^ f.support.card
参数：-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycle.sign._unary`：∀ {α : Type u_2} [inst : DecidableEq α] 
[inst_1 : Fintype α] (_x : (f : Equiv.Perm α) ×' f.IsCycle),   Equiv.Perm.sign _
x.1 = -(-1) ^ _x.1.s…
-/
theorem IsCycle.sign {f : Perm α} (hf : IsCycle f) : sign f = -(-1) ^ #f.support :=
  let ⟨x, hx⟩ := hf
  calc
    Perm.sign f = Perm.sign (swap x (f x) * (swap x (f x) * f)) := by simp
    _ = -(-1) ^ #f.support :=
      if h1 : f (f x) = x then by
        have h : swap x (f x) * f = 1 := by
          simp only [mul_def, one_def]
          rw [hf.eq_swap_of_apply_apply_eq_self hx.1 h1, swap_apply_left, swap_swap]
        rw [sign_mul, sign_swap hx.1.symm, h, sign_one,
          hf.eq_swap_of_apply_apply_eq_self hx.1 h1, card_support_swap hx.1.symm]
        rfl
      else by
        have h : #(swap x (f x) * f).support + 1 = #f.support := by
          rw [← insert_erase (mem_support.2 hx.1), support_swap_mul_eq _ _ h1,
            card_insert_of_notMem (notMem_erase _ _), sdiff_singleton_eq_erase]
        rw [sign_mul, sign_swap hx.1.symm, (hf.swap_mul hx.1 h1).sign, ← h]
        simp only [mul_neg, neg_mul, one_mul, neg_neg, pow_add, pow_one, mul_one]
termination_by #f.support
/-
**Equiv.Perm.IsCycle.of_pow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Finty
pe α] {n : ℕ},   (f ^ n).IsCycle → f.support ⊆ (f ^ n).support → f.IsCycle
参数：f ^ n；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Equiv.Perm.support_pow_le`：support_pow_le (σ : Perm α) (n : Nat) : (σ ^ 
n).support <= σ.support
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
-/
theorem IsCycle.of_pow {n : ℕ} (h1 : IsCycle (f ^ n)) (h2 : f.support ⊆ (f ^ n).support) :
    IsCycle f := by
  have key : ∀ x : α, (f ^ n) x ≠ x ↔ f x ≠ x := by
    simp_rw [← mem_support, ← Finset.ext_iff]
    exact (support_pow_le _ n).antisymm h2
  obtain ⟨x, hx1, hx2⟩ := h1
  refine ⟨x, (key x).mp hx1, fun y hy => ?_⟩
  obtain ⟨i, _⟩ := hx2 ((key y).mpr hy)
  exact ⟨n * i, by rwa [zpow_mul]⟩

-- The lemma `support_zpow_le` is relevant. It means that `h2` is equivalent to
-- `σ.support = (σ ^ n).support`, as well as to `#σ.support ≤ #(σ ^ n).support`.
/-
**Equiv.Perm.IsCycle.of_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Finty
pe α] {n : ℤ},   (f ^ n).IsCycle → f.support ⊆ (f ^ n).support → f.IsCycle
参数：f ^ n；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycle.of_pow`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : D
ecidableEq α] [inst_1 : Fintype α] {n : ℕ},   (f ^ n).IsCycle → f.support ⊆ (f ^
 n).support → f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.IsCycle.inv`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycle →
 f⁻¹.IsCycle
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.Perm.support_inv`：support_inv (σ : Perm α) : support σ⁻¹ = σ.suppo
rt
-/
theorem IsCycle.of_zpow {n : ℤ} (h1 : IsCycle (f ^ n)) (h2 : f.support ⊆ (f ^ n).support) :
    IsCycle f := by
  cases n
  · exact h1.of_pow h2
  · simp only [zpow_negSucc, Perm.support_inv] at h1 h2
    exact (inv_inv (f ^ _) ▸ h1.inv).of_pow h2
/-
**Equiv.Perm.nodup_of_pairwise_disjoint_cycles** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Perm`。
形式化陈述：nodup_of_pairwise_disjoint_cycles {l : List (Perm β)} (h1 : forall f in l,
 IsCycle f) (h2 : l.Pairwise Disjoint) : l.Nodup
参数：Perm β；h1 : forall f in l, IsCycle f；h2 : l.Pairwise Disjoint。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.nodup_of_pairwise_disjoint`：nodup_of_pairwise_disjoint {l : L
ist (Perm α)} (h1 : (1 : Perm α) ∉ l) (h2 : l.Pairwise Disjoint) : l.Nodup
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1
-/
theorem nodup_of_pairwise_disjoint_cycles {l : List (Perm β)} (h1 : ∀ f ∈ l, IsCycle f)
    (h2 : l.Pairwise Disjoint) : l.Nodup :=
  nodup_of_pairwise_disjoint (fun h => (h1 1 h).ne_one rfl) h2

/-- Unlike `support_congr`, which assumes that `∀ (x ∈ g.support), f x = g x)`, here
we have the weaker assumption that `∀ (x ∈ f.support), f x = g x`. -/
/-
**Equiv.Perm.IsCycle.support_congr** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle
`。
形式化陈述：∀ {α : Type u_2} {f g : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Fin
type α],   f.IsCycle → g.IsCycle → f.support ⊆ g.support → (∀ x ∈ f.support, f x
 = g x) → f = g
参数：∀ x ∈ f.support, f x = g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.IsCycle.exists_pow_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x
 y : α} [Finite α], f.IsCycle → f x ≠ x → f y ≠ y → ∃ i, (f ^ i) x = y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_of_mem_inter_left`：mem_of_mem_inter_left {a : α} {s₁ s₂ : Fin
set α} (h : a in s₁ inter s₂) : a in s₁
· 使用定理 `Equiv.Perm.pow_eq_on_of_mem_support`：pow_eq_on_of_mem_support (h : foral
l x in f.support inter g.support, f x = g x) (k : Nat) : forall x in f.support i
nter g.support, (f ^ k) x…
· 使用定理 `Finset.mem_inter_of_mem`：mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a
 in s₁ -> a in s₂ -> a in s₁ inter s₂
· 使用定理 `Equiv.Perm.pow_apply_mem_support`：pow_apply_mem_support {n : Nat} {x : α
} : (f ^ n) x in f.support ↔ x in f.support
· 使用定理 `Equiv.Perm.support_congr`：support_congr (h : f.support subseteq g.suppor
t) (h' : forall x in g.support, f x = g x) : f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Unlike `support_congr`, which assumes that `∀ (x ∈ g.support), f x = g x)`, here
we have the weaker assumption that `∀ (x ∈ f.support), f x = g x`.
-/
theorem IsCycle.support_congr (hf : IsCycle f) (hg : IsCycle g) (h : f.support ⊆ g.support)
    (h' : ∀ x ∈ f.support, f x = g x) : f = g := by
  have : f.support = g.support := by
    refine le_antisymm h ?_
    intro z hz
    obtain ⟨x, hx, _⟩ := id hf
    have hx' : g x ≠ x := by rwa [← h' x (mem_support.mpr hx)]
    obtain ⟨m, hm⟩ := hg.exists_pow_eq hx' (mem_support.mp hz)
    have h'' : ∀ x ∈ f.support ∩ g.support, f x = g x := by
      intro x hx
      exact h' x (mem_of_mem_inter_left hx)
    rwa [← hm, ←
      pow_eq_on_of_mem_support h'' _ x
        (mem_inter_of_mem (mem_support.mpr hx) (mem_support.mpr hx')),
      pow_apply_mem_support, mem_support]
  refine Equiv.Perm.support_congr h ?_
  simpa [← this] using h'

/-- If two cyclic permutations agree on all terms in their intersection,
and that intersection is not empty, then the two cyclic permutations must be equal. -/
/-
**Equiv.Perm.IsCycle.eq_on_support_inter_nonempty_congr** 是 Mathlib 中的一个定理，位于命名空
间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f g : Equiv.Perm α} {x : α} [inst : DecidableEq α] [inst
_1 : Fintype α],   f.IsCycle → g.IsCycle → (∀ x ∈ f.support ∩ g.support, f x = g
 x) → f x = g x → x ∈ f.support → f = g
参数：∀ x ∈ f.support ∩ g.support, f x = g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.IsCycle.exists_pow_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x
 y : α} [Finite α], f.IsCycle → f x ≠ x → f y ≠ y → ∃ i, (f ^ i) x = y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.pow_eq_on_of_mem_support`：pow_eq_on_of_mem_support (h : foral
l x in f.support inter g.support, f x = g x) (k : Nat) : forall x in f.support i
nter g.support, (f ^ k) x…
· 使用定理 `Finset.mem_inter_of_mem`：mem_inter_of_mem {a : α} {s₁ s₂ : Finset α} : a
 in s₁ -> a in s₂ -> a in s₁ inter s₂
· 使用定理 `Equiv.Perm.pow_apply_mem_support`：pow_apply_mem_support {n : Nat} {x : α
} : (f ^ n) x in f.support ↔ x in f.support
· 使用定理 `Equiv.Perm.IsCycle.support_congr`：∀ {α : Type u_2} {f g : Equiv.Perm α} 
[inst : DecidableEq α] [inst_1 : Fintype α],   f.IsCycle → g.IsCycle → f.support
 ⊆ g.support → (∀ x ∈ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.inter_eq_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fin
set α}, s ∩ t = s ↔ s ⊆ t

--- 原说明 ---
If two cyclic permutations agree on all terms in their intersection,
and that intersection is not empty, then the two cyclic permutations must be equ
al.
-/
theorem IsCycle.eq_on_support_inter_nonempty_congr (hf : IsCycle f) (hg : IsCycle g)
    (h : ∀ x ∈ f.support ∩ g.support, f x = g x)
    (hx : f x = g x) (hx' : x ∈ f.support) : f = g := by
  have hx'' : x ∈ g.support := by rwa [mem_support, ← hx, ← mem_support]
  have : f.support ⊆ g.support := by
    intro y hy
    obtain ⟨k, rfl⟩ := hf.exists_pow_eq (mem_support.mp hx') (mem_support.mp hy)
    rwa [pow_eq_on_of_mem_support h _ _ (mem_inter_of_mem hx' hx''), pow_apply_mem_support]
  rw [inter_eq_left.mpr this] at h
  exact hf.support_congr hg this h
/-
**Equiv.Perm.IsCycle.support_pow_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Is
Cycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Finty
pe α],   f.IsCycle → ∀ {n : ℕ}, (f ^ n).support = f.support ↔ ¬orderOf f ∣ n
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.support_eq_empty_iff`：support_eq_empty_iff {σ : Perm α} : σ.s
upport = ∅ ↔ σ = 1
· 使用定理 `Equiv.Perm.support_one`：support_one : (1 : Perm α).support = ∅
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Equiv.Perm.support_pow_le`：support_pow_le (σ : Perm α) (n : Nat) : (σ ^ 
n).support <= σ.support
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.Perm.pow_apply_eq_self_of_apply_eq_self`：∀ {α : Type u_1} {f : Equ
iv.Perm α} {x : α}, f x = x → ∀ (n : ℕ), (f ^ n) x = x
· 使用定理 `Equiv.Perm.one_apply`：one_apply (x) : (1 : Perm α) x = x
· 使用定理 `Equiv.Perm.IsCycle.exists_pow_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x
 y : α} [Finite α], f.IsCycle → f x ≠ x → f y ≠ y → ∃ i, (f ^ i) x = y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.pow_pow_self`：pow_pow_self (a : M) (m n : Nat) : Commute (a ^ m)
 (a ^ n)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem IsCycle.support_pow_eq_iff (hf : IsCycle f) {n : ℕ} :
    support (f ^ n) = support f ↔ ¬orderOf f ∣ n := by
  rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h H
    refine hf.ne_one ?_
    rw [← support_eq_empty_iff, ← h, H, support_one]
  · intro H
    apply le_antisymm (support_pow_le _ n) _
    intro x hx
    contrapose H
    ext z
    by_cases hz : f z = z
    · rw [pow_apply_eq_self_of_apply_eq_self hz, one_apply]
    · obtain ⟨k, rfl⟩ := hf.exists_pow_eq hz (mem_support.mp hx)
      apply (f ^ k).injective
      rw [← mul_apply, (Commute.pow_pow_self _ _ _).eq, mul_apply]
      simpa using H
/-
**Equiv.Perm.IsCycle.support_pow_of_pos_of_lt_orderOf** 是 Mathlib 中的一个定理，位于命名空间 
`Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : DecidableEq α] [inst_1 : Finty
pe α],   f.IsCycle → ∀ {n : ℕ}, 0 < n → n < orderOf f → (f ^ n).support = f.supp
ort
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.IsCycle.support_pow_eq_iff`：∀ {α : Type u_2} {f : Equiv.Perm 
α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.IsCycle → ∀ {n : ℕ}, (f ^ n)
.support = f.support ↔ ¬ord…
· 使用定理 `Nat.not_dvd_of_pos_of_lt`：∀ {n m : ℕ}, 0 < n → n < m → ¬m ∣ n
-/
theorem IsCycle.support_pow_of_pos_of_lt_orderOf (hf : IsCycle f) {n : ℕ} (npos : 0 < n)
    (hn : n < orderOf f) : (f ^ n).support = f.support :=
  hf.support_pow_eq_iff.2 <| Nat.not_dvd_of_pos_of_lt npos hn
/-
**Equiv.Perm.IsCycle.pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {β : Type u_3} [Finite β] {f : Equiv.Perm β}, f.IsCycle → ∀ {n : ℕ}, (f 
^ n).IsCycle ↔ n.Coprime (orderOf f)
参数：f ^ n；orderOf f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.IsCycle.support_pow_eq_iff`：∀ {α : Type u_2} {f : Equiv.Perm 
α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.IsCycle → ∀ {n : ℕ}, (f ^ n)
.support = f.support ↔ ¬ord…
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `Nat.div_eq_self`：∀ {m n : ℕ}, m / n = m ↔ m = 0 ∨ n = 1
· 使用定理 `orderOf_pow`：orderOf_pow (x : G) : orderOf (x ^ n) = orderOf x / Nat.gcd
 (orderOf x) n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `orderOf_pos`：orderOf_pos (x : G) : 0 < orderOf x
· 使用定理 `Nat.coprime_iff_gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n ↔ m.gcd n = 1
· 使用定理 `Nat.gcd_comm`：∀ (m n : ℕ), m.gcd n = n.gcd m
· 使用定理 `exists_pow_eq_self_of_coprime`：exists_pow_eq_self_of_coprime (h : n.Copr
ime (orderOf x)) : exists m : Nat, (x ^ n) ^ m = x
· 使用定理 `Equiv.Perm.IsCycle.of_pow`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : D
ecidableEq α] [inst_1 : Fintype α] {n : ℕ},   (f ^ n).IsCycle → f.support ⊆ (f ^
 n).support → f…
· 使用定理 `Equiv.Perm.support_pow_le`：support_pow_le (σ : Perm α) (n : Nat) : (σ ^ 
n).support <= σ.support
-/
theorem IsCycle.pow_iff [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} :
    IsCycle (f ^ n) ↔ n.Coprime (orderOf f) := by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      have hr : support (f ^ n) = support f := by
        rw [hf.support_pow_eq_iff]
        rintro ⟨k, rfl⟩
        refine h.ne_one ?_
        simp [pow_mul, pow_orderOf_eq_one]
      have : orderOf (f ^ n) = orderOf f := by rw [h.orderOf, hr, hf.orderOf]
      rw [orderOf_pow, Nat.div_eq_self] at this
      rcases this with h | _
      · exact absurd h (orderOf_pos _).ne'
      · rwa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    · intro h
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
      have hf' : IsCycle ((f ^ n) ^ m) := by rwa [hm]
      refine hf'.of_pow fun x hx => ?_
      rw [hm]
      exact support_pow_le _ n hx

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
/-
**Equiv.Perm.IsCycle.pow_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycl
e`。
形式化陈述：∀ {β : Type u_3} [Finite β] {f : Equiv.Perm β}, f.IsCycle → ∀ {n : ℕ}, f ^
 n = 1 ↔ ∃ x, f x ≠ x ∧ (f ^ n) x = x
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Equiv.Perm.IsCycle.support_pow_eq_iff`：∀ {α : Type u_2} {f : Equiv.Perm 
α} [inst : DecidableEq α] [inst_1 : Fintype α],   f.IsCycle → ∀ {n : ℕ}, (f ^ n)
.support = f.support ↔ ¬ord…
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem IsCycle.pow_eq_one_iff [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} :
    f ^ n = 1 ↔ ∃ x, f x ≠ x ∧ (f ^ n) x = x := by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := id hf
      exact ⟨x, hx, by simp [h]⟩
    · rintro ⟨x, hx, hx'⟩
      by_cases h : support (f ^ n) = support f
      · rw [← mem_support, ← h, mem_support] at hx
        contradiction
      · rw [hf.support_pow_eq_iff, Classical.not_not] at h
        obtain ⟨k, rfl⟩ := h
        rw [pow_mul, pow_orderOf_eq_one, one_pow]

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
/-
**Equiv.Perm.IsCycle.pow_eq_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCyc
le`。
形式化陈述：∀ {β : Type u_3} [Finite β] {f : Equiv.Perm β}, f.IsCycle → ∀ {n : ℕ} {x :
 β}, f x ≠ x → (f ^ n = 1 ↔ (f ^ n) x = x)
参数：f ^ n = 1 ↔ (f ^ n) x = x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.IsCycle.pow_eq_one_iff`：∀ {β : Type u_3} [Finite β] {f : Equi
v.Perm β}, f.IsCycle → ∀ {n : ℕ}, f ^ n = 1 ↔ ∃ x, f x ≠ x ∧ (f ^ n) x = x
-/
theorem IsCycle.pow_eq_one_iff' [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} {x : β}
    (hx : f x ≠ x) : f ^ n = 1 ↔ (f ^ n) x = x :=
  ⟨fun h => DFunLike.congr_fun h x, fun h => hf.pow_eq_one_iff.2 ⟨x, hx, h⟩⟩

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
/-
**Equiv.Perm.IsCycle.pow_eq_one_iff''** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCy
cle`。
形式化陈述：∀ {β : Type u_3} [Finite β] {f : Equiv.Perm β}, f.IsCycle → ∀ {n : ℕ}, f ^
 n = 1 ↔ ∀ (x : β), f x ≠ x → (f ^ n) x = x
参数：x : β；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.IsCycle.pow_eq_one_iff'`：∀ {β : Type u_3} [Finite β] {f : Equ
iv.Perm β}, f.IsCycle → ∀ {n : ℕ} {x : β}, f x ≠ x → (f ^ n = 1 ↔ (f ^ n) x = x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsCycle.pow_eq_one_iff'' [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} :
    f ^ n = 1 ↔ ∀ x, f x ≠ x → (f ^ n) x = x :=
  ⟨fun h _ hx => (hf.pow_eq_one_iff' hx).1 h, fun h =>
    let ⟨_, hx, _⟩ := id hf
    (hf.pow_eq_one_iff' hx).2 (h _ hx)⟩

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
/-
**Equiv.Perm.IsCycle.pow_eq_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycl
e`。
形式化陈述：∀ {β : Type u_3} [Finite β] {f : Equiv.Perm β},   f.IsCycle → ∀ {a b : ℕ},
 f ^ a = f ^ b ↔ ∃ x, f x ≠ x ∧ (f ^ a) x = (f ^ b) x
参数：f ^ a；f ^ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Equiv.Perm.IsCycle.pow_eq_one_iff`：∀ {β : Type u_3} [Finite β] {f : Equi
v.Perm β}, f.IsCycle → ∀ {n : ℕ}, f ^ n = 1 ↔ ∃ x, f x ≠ x ∧ (f ^ n) x = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用引理 `pow_sub`：pow_sub (a : G) {m n : Nat} (h : n <= m) : a ^ (m - n) = a ^ m 
* (a ^ n)⁻¹
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.zpow_apply_comm`：zpow_apply_comm {α : Type*} (σ : Perm α) (m 
n : Int) {x : α} : (σ ^ m) ((σ ^ n) x) = (σ ^ n) ((σ ^ m) x)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem IsCycle.pow_eq_pow_iff [Finite β] {f : Perm β} (hf : IsCycle f) {a b : ℕ} :
    f ^ a = f ^ b ↔ ∃ x, f x ≠ x ∧ (f ^ a) x = (f ^ b) x := by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := id hf
      exact ⟨x, hx, by simp [h]⟩
    · rintro ⟨x, hx, hx'⟩
      wlog hab : a ≤ b generalizing a b
      · exact (this hx'.symm (le_of_not_ge hab)).symm
      suffices f ^ (b - a) = 1 by
        rw [pow_sub _ hab, mul_inv_eq_one] at this
        rw [this]
      rw [hf.pow_eq_one_iff]
      by_cases hfa : (f ^ a) x ∈ f.support
      · refine ⟨(f ^ a) x, mem_support.mp hfa, ?_⟩
        simp [pow_sub _ hab, ← hx']
      · have h := @Equiv.Perm.zpow_apply_comm _ f 1 a x
        simp only [zpow_one, zpow_natCast] at h
        rw [notMem_support, h, Function.Injective.eq_iff (f ^ a).injective] at hfa
        contradiction
/-
**Equiv.Perm.IsCycle.isCycle_pow_pos_of_lt_prime_order** 是 Mathlib 中的一个定理，位于命名空间
 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {β : Type u_3} [Finite β] {f : Equiv.Perm β},   f.IsCycle → Nat.Prime (o
rderOf f) → ∀ (n : ℕ), 0 < n → n < orderOf f → (f ^ n).IsCycle
参数：orderOf f；n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Nat.not_dvd_of_pos_of_lt`：∀ {n m : ℕ}, 0 < n → n < m → ¬m ∣ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.IsCycle.pow_iff`：∀ {β : Type u_3} [Finite β] {f : Equiv.Perm 
β}, f.IsCycle → ∀ {n : ℕ}, (f ^ n).IsCycle ↔ n.Coprime (orderOf f)
-/
theorem IsCycle.isCycle_pow_pos_of_lt_prime_order [Finite β] {f : Perm β} (hf : IsCycle f)
    (hf' : (orderOf f).Prime) (n : ℕ) (hn : 0 < n) (hn' : n < orderOf f) : IsCycle (f ^ n) := by
  cases nonempty_fintype β
  have : n.Coprime (orderOf f) := by
    refine Nat.Coprime.symm ?_
    rw [Nat.Prime.coprime_iff_not_dvd hf']
    exact Nat.not_dvd_of_pos_of_lt hn hn'
  exact (pow_iff hf).mpr this

end IsCycle

open Equiv

/-
**Equiv.Perm._root_.Int.addLeft_one_isCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Int.addLeft_one_isCycle : (Equiv.addLeft 1 : Perm ℤ).IsCycle :=
  ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩
/-
**Equiv.Perm._root_.Int.addRight_one_isCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Pe
rm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Int.addRight_one_isCycle : (Equiv.addRight 1 : Perm ℤ).IsCycle :=
  ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩

section Conjugation

variable [Fintype α] [DecidableEq α] {σ τ : Perm α}

/-
**Equiv.Perm.IsCycle.isConj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α] {σ τ : Equiv.
Perm α},   σ.IsCycle → τ.IsCycle → σ.support.card = τ.support.card → IsConj σ τ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.isConj_of_support_equiv`：isConj_of_support_equiv (f : { x // 
x in (σ.support : Set α) } ≃ { x // x in (τ.support : Set α) }) (hf : forall (x 
: α) (hx : x in (σ.suppo…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.apply_mem_support`：apply_mem_support {x : α} : f x in f.suppo
rt ↔ x in f.support
· 使用定理 `Equiv.Perm.IsCycle.exists_pow_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {x
 y : α} [Finite α], f.IsCycle → f x ≠ x → f y ≠ y → ∃ i, (f ^ i) x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.Perm.pow_apply_mem_support`：pow_apply_mem_support {n : Nat} {x : α
} : (f ^ n) x in f.support ↔ x in f.support
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Equiv.Perm.IsCycle.zpowersEquivSupport_symm_apply`：∀ {α : Type u_2} [ins
t : DecidableEq α] [inst_1 : Fintype α] {σ : Equiv.Perm α} (hσ : σ.IsCycle) (n :
 ℕ),   hσ.zpowersEquivSupport.symm ⟨(σ …
· 使用定理 `zpowersEquivZPowers_apply`：zpowersEquivZPowers_apply (h : orderOf x = or
derOf y) (n : Nat) : zpowersEquivZPowers h ⟨x ^ n, n, zpow_natCast x n⟩ = ⟨y ^ n
, n, zpow_natCa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsCycle.isConj (hσ : IsCycle σ) (hτ : IsCycle τ) (h : #σ.support = #τ.support) :
    IsConj σ τ := by
  refine
    isConj_of_support_equiv
      (hσ.zpowersEquivSupport.symm.trans <|
        (zpowersEquivZPowers <| by rw [hσ.orderOf, h, hτ.orderOf]).trans hτ.zpowersEquivSupport)
      ?_
  intro x hx
  simp only [Equiv.trans_apply]
  obtain ⟨n, rfl⟩ := hσ.exists_pow_eq (Classical.choose_spec hσ).1 (mem_support.1 hx)
  simp [← Perm.mul_apply, ← pow_succ']
/-
**Equiv.Perm.IsCycle.isConj_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α] {σ τ : Equiv.
Perm α},   σ.IsCycle → τ.IsCycle → (IsConj σ τ ↔ σ.support.card = τ.support.card
)
参数：IsConj σ τ ↔ σ.support.card = τ.support.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.card_support_conj`：card_support_conj : #(σ * τ * σ⁻¹).support
 = #τ.support
· 使用定理 `Equiv.Perm.IsCycle.isConj`：∀ {α : Type u_2} [inst : Fintype α] [inst_1 :
 DecidableEq α] {σ τ : Equiv.Perm α},   σ.IsCycle → τ.IsCycle → σ.support.card =
 τ.support.card…
-/
theorem IsCycle.isConj_iff (hσ : IsCycle σ) (hτ : IsCycle τ) :
    IsConj σ τ ↔ #σ.support = #τ.support where
  mp h := by
    obtain ⟨π, rfl⟩ := (_root_.isConj_iff).1 h
    exact card_support_conj.symm
  mpr := hσ.isConj hτ

end Conjugation

/-! ### `IsCycleOn` -/

section IsCycleOn

variable {f g : Perm α} {s t : Set α} {a b x y : α}

/-- A permutation is a cycle on `s` when any two points of `s` are related by repeated application
of the permutation. Note that this means the identity is a cycle of subsingleton sets. -/
/-
**Equiv.Perm.IsCycleOn** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：IsCycleOn (f : Perm α) (s : Set α) : Prop
参数：f : Perm α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A permutation is a cycle on `s` when any two points of `s` are related by repeat
ed application
of the permutation. Note that this means the identity is a cycle of subsingleton
 sets.
-/
def IsCycleOn (f : Perm α) (s : Set α) : Prop :=
  Set.BijOn f s s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → f.SameCycle x y

@[simp]
/-
**Equiv.Perm.isCycleOn_empty** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycleOn_empty : f.IsCycleOn ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isCycleOn_empty : f.IsCycleOn ∅ := by simp [IsCycleOn]

@[simp]
/-
**Equiv.Perm.isCycleOn_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycleOn_one : (1 : Perm α).IsCycleOn s ↔ s.Subsingleton
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCycleOn_one : (1 : Perm α).IsCycleOn s ↔ s.Subsingleton := by
  simp [IsCycleOn, Set.bijOn_id, Set.Subsingleton]

alias ⟨IsCycleOn.subsingleton, _root_.Set.Subsingleton.isCycleOn_one⟩ := isCycleOn_one

@[simp]
/-
**Equiv.Perm.isCycleOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycleOn_singleton : f.IsCycleOn {a} ↔ f a = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCycleOn_singleton : f.IsCycleOn {a} ↔ f a = a := by simp [IsCycleOn, SameCycle.rfl]
/-
**Equiv.Perm.isCycleOn_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycleOn_of_subsingleton [Subsingleton α] (f : Perm α) (s : Set α) : f.Is
CycleOn s
参数：f : Perm α；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.bijOn_of_subsingleton`：bijOn_of_subsingleton [Subsingleton α] (f : α
 -> α) (s : Set α) : BijOn f s s
· 使用定理 `Eq.sameCycle`：∀ {α : Type u_2} {x y : α}, x = y → ∀ (f : Equiv.Perm α), 
f.SameCycle x y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem isCycleOn_of_subsingleton [Subsingleton α] (f : Perm α) (s : Set α) : f.IsCycleOn s :=
  ⟨s.bijOn_of_subsingleton _, fun x _ y _ => (Subsingleton.elim x y).sameCycle _⟩

@[simp]
/-
**Equiv.Perm.isCycleOn_inv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycleOn_inv : f⁻¹.IsCycleOn s ↔ f.IsCycleOn s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.BijOn.perm_inv`：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Set
.BijOn (⇑f) s s → Set.BijOn (⇑f⁻¹) s s
-/
theorem isCycleOn_inv : f⁻¹.IsCycleOn s ↔ f.IsCycleOn s := by
  simp only [IsCycleOn, sameCycle_inv, and_congr_left_iff]
  exact fun _ ↦ ⟨fun h ↦ Set.BijOn.perm_inv h, fun h ↦ Set.BijOn.perm_inv h⟩

alias ⟨IsCycleOn.of_inv, IsCycleOn.inv⟩ := isCycleOn_inv
/-
**Equiv.Perm.IsCycleOn.conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycleOn`。
形式化陈述：∀ {α : Type u_2} {f g : Equiv.Perm α} {s : Set α}, f.IsCycleOn s → (g * f 
* g⁻¹).IsCycleOn (⇑g '' s)
参数：g * f * g⁻¹；⇑g '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set 
α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.BijOn g t p → Set.BijO
n f …
· 使用引理 `Equiv.bijOn_image`：bijOn_image : BijOn e s (e '' s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Equiv.bijOn_symm_image`：bijOn_symm_image : BijOn e.symm (e '' s) s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.SameCycle.conj`：∀ {α : Type u_2} {f g : Equiv.Perm α} {x y : 
α}, f.SameCycle x y → (g * f * g⁻¹).SameCycle (g x) (g y)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem IsCycleOn.conj (h : f.IsCycleOn s) : (g * f * g⁻¹).IsCycleOn ((g : Perm α) '' s) :=
  ⟨(g.bijOn_image.comp h.1).comp g.bijOn_symm_image, fun x hx y hy => by
    rw [Equiv.image_eq_preimage_symm] at hx hy
    convert! Equiv.Perm.SameCycle.conj (h.2 hx hy) (g := g) <;> simp⟩
/-
**Equiv.Perm.isCycleOn_swap** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：isCycleOn_swap [DecidableEq α] (hab : a != b) : (swap a b).IsCycleOn {a, b
}
参数：hab : a != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.bijOn_swap`：bijOn_swap (ha : a in s) (hb : b in s) : BijOn (swap a
 b) s s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `Equiv.Perm.coe_one`：∀ {α : Type u_4}, ⇑1 = id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
-/
theorem isCycleOn_swap [DecidableEq α] (hab : a ≠ b) : (swap a b).IsCycleOn {a, b} :=
  ⟨bijOn_swap (by simp) (by simp), fun x hx y hy => by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    obtain rfl | rfl := hx <;> obtain rfl | rfl := hy
    · exact ⟨0, by rw [zpow_zero, coe_one, id]⟩
    · exact ⟨1, by rw [zpow_one, swap_apply_left]⟩
    · exact ⟨1, by rw [zpow_one, swap_apply_right]⟩
    · exact ⟨0, by rw [zpow_zero, coe_one, id]⟩⟩
/-
**Equiv.Perm.IsCycleOn.apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycleOn`
。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α} {a : α}, f.IsCycleOn s → s
.Nontrivial → a ∈ s → f a ≠ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nontrivial.exists_ne`：∀ {α : Type u} {s : Set α}, s.Nontrivial → ∀ (
z : α), ∃ x ∈ s, x ≠ z
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Function.IsFixedPt.perm_zpow`：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α
}, Function.IsFixedPt (⇑e) x → ∀ (n : ℤ), Function.IsFixedPt (⇑(e ^ n)) x
-/
protected theorem IsCycleOn.apply_ne (hf : f.IsCycleOn s) (hs : s.Nontrivial) (ha : a ∈ s) :
    f a ≠ a := by
  obtain ⟨b, hb, hba⟩ := hs.exists_ne a
  obtain ⟨n, rfl⟩ := hf.2 ha hb
  exact fun h => hba (IsFixedPt.perm_zpow h n)
/-
**Equiv.Perm.IsCycle.isCycleOn** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycle → f.IsCycleOn {x | f x ≠ x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijOn`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) {s : Set α} {t 
: Set β}, (∀ (a : α), e a ∈ t ↔ a ∈ s) → Set.BijOn (⇑e) s t
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `Equiv.Perm.IsCycle.sameCycle`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y :
 α}, f.IsCycle → f x ≠ x → f y ≠ y → f.SameCycle x y
-/
protected theorem IsCycle.isCycleOn (hf : f.IsCycle) : f.IsCycleOn { x | f x ≠ x } :=
  ⟨f.bijOn fun _ => f.apply_eq_iff_eq.not, fun _ ha _ => hf.sameCycle ha⟩

/-- This lemma demonstrates the relation between `Equiv.Perm.IsCycle` and `Equiv.Perm.IsCycleOn`
in non-degenerate cases. -/
/-
**Equiv.Perm.isCycle_iff_exists_isCycleOn** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：isCycle_iff_exists_isCycleOn : f.IsCycle ↔ exists s : Set α, s.Nontrivial 
∧ f.IsCycleOn s ∧ forall ⦃x⦄, ¬IsFixedPt f x -> x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.Perm.IsCycle.isCycleOn`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsC
ycle → f.IsCycleOn {x | f x ≠ x}
· 使用定理 `Set.Nontrivial.nonempty`：∀ {α : Type u} {s : Set α}, s.Nontrivial → s.No
nempty
· 使用定理 `Equiv.Perm.IsCycleOn.apply_ne`：∀ {α : Type u_2} {f : Equiv.Perm α} {s : 
Set α} {a : α}, f.IsCycleOn s → s.Nontrivial → a ∈ s → f a ≠ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
This lemma demonstrates the relation between `Equiv.Perm.IsCycle` and `Equiv.Per
m.IsCycleOn`
in non-degenerate cases.
-/
theorem isCycle_iff_exists_isCycleOn :
    f.IsCycle ↔ ∃ s : Set α, s.Nontrivial ∧ f.IsCycleOn s ∧ ∀ ⦃x⦄, ¬IsFixedPt f x → x ∈ s := by
  refine ⟨fun hf => ⟨{ x | f x ≠ x }, ?_, hf.isCycleOn, fun _ => id⟩, ?_⟩
  · obtain ⟨a, ha⟩ := hf
    exact ⟨f a, f.injective.ne ha.1, a, ha.1, ha.1⟩
  · rintro ⟨s, hs, hf, hsf⟩
    obtain ⟨a, ha⟩ := hs.nonempty
    exact ⟨a, hf.apply_ne hs ha, fun b hb => hf.2 ha <| hsf hb⟩
/-
**Equiv.Perm.IsCycleOn.apply_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCyc
leOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α} {x : α}, f.IsCycleOn s → (
f x ∈ s ↔ x ∈ s)
参数：f x ∈ s ↔ x ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.BijOn.perm_inv`：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Set
.BijOn (⇑f) s s → Set.BijOn (⇑f⁻¹) s s
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
-/
theorem IsCycleOn.apply_mem_iff (hf : f.IsCycleOn s) : f x ∈ s ↔ x ∈ s :=
  ⟨fun hx => by simpa using hf.1.perm_inv.1 hx, fun hx => hf.1.mapsTo hx⟩

/-- Note that the identity satisfies `IsCycleOn` for any subsingleton set, but not `IsCycle`. -/
/-
**Equiv.Perm.IsCycleOn.isCycle_subtypePerm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
.IsCycleOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α} (hf : f.IsCycleOn s), s.No
ntrivial → (f.subtypePerm ⋯).IsCycle
参数：hf : f.IsCycleOn s；f.subtypePerm ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycleOn.apply_mem_iff`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{s : Set α} {x : α}, f.IsCycleOn s → (f x ∈ s ↔ x ∈ s)
· 使用定理 `Set.Nontrivial.nonempty`：∀ {α : Type u} {s : Set α}, s.Nontrivial → s.No
nempty
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Equiv.Perm.IsCycleOn.apply_ne`：∀ {α : Type u_2} {f : Equiv.Perm α} {s : 
Set α} {a : α}, f.IsCycleOn s → s.Nontrivial → a ∈ s → f a ≠ a
· 使用定理 `Equiv.Perm.SameCycle.subtypePerm`：∀ {α : Type u_2} {f : Equiv.Perm α} {p
 : α → Prop} {h : ∀ (x : α), p (f x) ↔ p x} {x y : { x // p x }},   f.SameCycle 
↑x ↑y → (f.subtypePerm…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Note that the identity satisfies `IsCycleOn` for any subsingleton set, but not `
IsCycle`.
-/
theorem IsCycleOn.isCycle_subtypePerm (hf : f.IsCycleOn s) (hs : s.Nontrivial) :
    (f.subtypePerm fun _ => hf.apply_mem_iff : Perm s).IsCycle := by
  obtain ⟨a, ha⟩ := hs.nonempty
  exact
    ⟨⟨a, ha⟩, ne_of_apply_ne ((↑) : s → α) (hf.apply_ne hs ha), fun b _ =>
      (hf.2 (⟨a, ha⟩ : s).2 b.2).subtypePerm⟩

/-- Note that the identity is a cycle on any subsingleton set, but not a cycle. -/
/-
**Equiv.Perm.IsCycleOn.subtypePerm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle
On`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α} (hf : f.IsCycleOn s), (f.s
ubtypePerm ⋯).IsCycleOn Set.univ
参数：hf : f.IsCycleOn s；f.subtypePerm ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycleOn.apply_mem_iff`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{s : Set α} {x : α}, f.IsCycleOn s → (f x ∈ s ↔ x ∈ s)
· 使用定理 `Set.subsingleton_or_nontrivial`：∀ {α : Type u} (s : Set α), s.Subsinglet
on ∨ s.Nontrivial
· 使用定理 `Set.Subsingleton.coe_sort`：∀ {α : Type u} {s : Set α}, s.Subsingleton → 
Subsingleton ↑s
· 使用定理 `Equiv.Perm.isCycleOn_of_subsingleton`：isCycleOn_of_subsingleton [Subsing
leton α] (f : Perm α) (s : Set α) : f.IsCycleOn s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Equiv.Perm.IsCycleOn.apply_ne`：∀ {α : Type u_2} {f : Equiv.Perm α} {s : 
Set α} {a : α}, f.IsCycleOn s → s.Nontrivial → a ∈ s → f a ≠ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.Perm.IsCycle.isCycleOn`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsC
ycle → f.IsCycleOn {x | f x ≠ x}
· 使用定理 `Equiv.Perm.IsCycleOn.isCycle_subtypePerm`：∀ {α : Type u_2} {f : Equiv.Pe
rm α} {s : Set α} (hf : f.IsCycleOn s), s.Nontrivial → (f.subtypePerm ⋯).IsCycle

--- 原说明 ---
Note that the identity is a cycle on any subsingleton set, but not a cycle.
-/
protected theorem IsCycleOn.subtypePerm (hf : f.IsCycleOn s) :
    (f.subtypePerm fun _ => hf.apply_mem_iff : Perm s).IsCycleOn _root_.Set.univ := by
  obtain hs | hs := s.subsingleton_or_nontrivial
  · have := hs.coe_sort
    exact isCycleOn_of_subsingleton _ _
  convert! (hf.isCycle_subtypePerm hs).isCycleOn
  rw [eq_comm, Set.eq_univ_iff_forall]
  exact fun x => ne_of_apply_ne ((↑) : s → α) (hf.apply_ne hs x.2)

-- TODO: Theory of order of an element under an action
/-
**Equiv.Perm.IsCycleOn.pow_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycl
eOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {a : α} {s : Finset α},   f.IsCycleOn 
↑s → a ∈ s → ∀ {n : ℕ}, (f ^ n) a = a ↔ s.card ∣ n
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_singleton_or_nontrivial`：eq_singleton_or_nontrivial (ha : a in
 s) : s = {a} ∨ s.Nontrivial
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Function.IsFixedPt.iterate`：∀ {α : Type u_1} {f : α → α} {x : α}, Functi
on.IsFixedPt f x → ∀ (n : ℕ), Function.IsFixedPt f^[n] x
· 使用定理 `Equiv.Perm.isCycleOn_singleton`：isCycleOn_singleton : f.IsCycleOn {a} ↔ 
f a = a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.IsCycleOn.apply_ne`：∀ {α : Type u_2} {f : Equiv.Perm α} {s : 
Set α} {a : α}, f.IsCycleOn s → s.Nontrivial → a ∈ s → f a ≠ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.Perm.IsCycleOn.apply_mem_iff`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{s : Set α} {x : α}, f.IsCycleOn s → (f x ∈ s ↔ x ∈ s)
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `Equiv.Perm.IsCycleOn.isCycle_subtypePerm`：∀ {α : Type u_2} {f : Equiv.Pe
rm α} {s : Set α} (hf : f.IsCycleOn s), s.Nontrivial → (f.subtypePerm ⋯).IsCycle
· 使用定理 `Equiv.Perm.support_subtypePerm`：support_subtypePerm [DecidableEq α] {s :
 Finset α} (f : Perm α) (h) : (f.subtypePerm h : Perm s).support = ({x | f x != 
x} : Finset s)
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `Equiv.Perm.IsCycle.pow_eq_one_iff'`：∀ {β : Type u_3} [Finite β] {f : Equ
iv.Perm β}, f.IsCycle → ∀ {n : ℕ} {x : β}, f x ≠ x → (f ^ n = 1 ↔ (f ^ n) x = x)
（共 37 条，此处仅展示前 30 条）
-/
theorem IsCycleOn.pow_apply_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) {n : ℕ} :
    (f ^ n) a = a ↔ #s ∣ n := by
  obtain rfl | hs := Finset.eq_singleton_or_nontrivial ha
  · rw [coe_singleton, isCycleOn_singleton] at hf
    simpa using! IsFixedPt.iterate hf n
  classical
    have h (x : s) : ¬f x = x := hf.apply_ne hs x.2
    have := (hf.isCycle_subtypePerm hs).orderOf
    simp only [coe_sort_coe, support_subtypePerm, ne_eq, h, not_false_eq_true, univ_eq_attach,
      mem_attach, imp_self, implies_true, filter_true_of_mem, card_attach] at this
    rw [← this, orderOf_dvd_iff_pow_eq_one,
      (hf.isCycle_subtypePerm hs).pow_eq_one_iff'
        (ne_of_apply_ne ((↑) : s → α) <| hf.apply_ne hs (⟨a, ha⟩ : s).2)]
    simp [-SetLike.coe_sort_coe]
/-
**Equiv.Perm.IsCycleOn.zpow_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCyc
leOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {a : α} {s : Finset α},   f.IsCycleOn 
↑s → a ∈ s → ∀ {n : ℤ}, (f ^ n) a = a ↔ ↑s.card ∣ n
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.Perm.IsCycleOn.pow_apply_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {
a : α} {s : Finset α},   f.IsCycleOn ↑s → a ∈ s → ∀ {n : ℕ}, (f ^ n) a = a ↔ s.c
ard ∣ n
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Equiv.Perm.IsCycleOn.inv`：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α
}, f.IsCycleOn s → f⁻¹.IsCycleOn s
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b
-/
theorem IsCycleOn.zpow_apply_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) :
    ∀ {n : ℤ}, (f ^ n) a = a ↔ (#s : ℤ) ∣ n
  | Int.ofNat _ => (hf.pow_apply_eq ha).trans Int.natCast_dvd_natCast.symm
  | Int.negSucc n => by
    rw [zpow_negSucc, ← inv_pow]
    exact (hf.inv.pow_apply_eq ha).trans (dvd_neg.trans Int.natCast_dvd_natCast).symm
/-
**Equiv.Perm.IsCycleOn.pow_apply_eq_pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.P
erm.IsCycleOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {a : α} {s : Finset α},   f.IsCycleOn 
↑s → a ∈ s → ∀ {m n : ℕ}, (f ^ m) a = (f ^ n) a ↔ m ≡ n [MOD s.card]
参数：f ^ m；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [MOD n] ↔ (n : Int) ∣ b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.IsCycleOn.zpow_apply_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{a : α} {s : Finset α},   f.IsCycleOn ↑s → a ∈ s → ∀ {n : ℤ}, (f ^ n) a = a ↔ ↑s
.card ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsCycleOn.pow_apply_eq_pow_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s)
    {m n : ℕ} : (f ^ m) a = (f ^ n) a ↔ m ≡ n [MOD #s] := by
  rw [Nat.modEq_iff_dvd, ← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_symm_apply, eq_comm]
/-
**Equiv.Perm.IsCycleOn.zpow_apply_eq_zpow_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv
.Perm.IsCycleOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {a : α} {s : Finset α},   f.IsCycleOn 
↑s → a ∈ s → ∀ {m n : ℤ}, (f ^ m) a = (f ^ n) a ↔ m ≡ n [ZMOD ↑s.card]
参数：f ^ m；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.modEq_iff_dvd`：modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.IsCycleOn.zpow_apply_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{a : α} {s : Finset α},   f.IsCycleOn ↑s → a ∈ s → ∀ {n : ℤ}, (f ^ n) a = a ↔ ↑s
.card ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsCycleOn.zpow_apply_eq_zpow_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s)
    {m n : ℤ} : (f ^ m) a = (f ^ n) a ↔ m ≡ n [ZMOD #s] := by
  rw [Int.modEq_iff_dvd, ← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_symm_apply, eq_comm]
/-
**Equiv.Perm.IsCycleOn.pow_card_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCy
cleOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {a : α} {s : Finset α}, f.IsCycleOn ↑s
 → a ∈ s → (f ^ s.card) a = a
参数：f ^ s.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.IsCycleOn.pow_apply_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} {
a : α} {s : Finset α},   f.IsCycleOn ↑s → a ∈ s → ∀ {n : ℕ}, (f ^ n) a = a ↔ s.c
ard ∣ n
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem IsCycleOn.pow_card_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) :
    (f ^ #s) a = a :=
  (hf.pow_apply_eq ha).2 dvd_rfl
/-
**Equiv.Perm.IsCycleOn.exists_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCyc
leOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {a b : α} {s : Finset α},   f.IsCycleO
n ↑s → a ∈ s → b ∈ s → ∃ n < s.card, (f ^ n) a = b
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Int.ModEq.dvd`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → n ∣ b - a
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
· 使用定理 `Int.mod_modEq`：mod_modEq (a n) : a % n ≡ a [ZMOD n]
· 使用引理 `Int.natMod_lt`：natMod_lt {n : Nat} (hn : n != 0) : m.natMod n < n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.natMod.eq_1`：∀ (m n : ℤ), m.natMod n = (m % n).toNat
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Function.IsFixedPt.perm_zpow`：∀ {α : Type u_1} {x : α} {e : Equiv.Perm α
}, Function.IsFixedPt (⇑e) x → ∀ (n : ℤ), Function.IsFixedPt (⇑(e ^ n)) x
· 使用定理 `Equiv.Perm.IsCycleOn.pow_card_apply`：∀ {α : Type u_2} {f : Equiv.Perm α}
 {a : α} {s : Finset α}, f.IsCycleOn ↑s → a ∈ s → (f ^ s.card) a = a
-/
theorem IsCycleOn.exists_pow_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) (hb : b ∈ s) :
    ∃ n < #s, (f ^ n) a = b := by
  obtain ⟨n, rfl⟩ := hf.2 ha hb
  obtain ⟨k, hk⟩ := (Int.mod_modEq n #s).symm.dvd
  refine ⟨n.natMod #s, Int.natMod_lt (Nonempty.card_pos ⟨a, ha⟩).ne', ?_⟩
  rw [← zpow_natCast, Int.natMod,
    Int.toNat_of_nonneg (Int.emod_nonneg _ <| Nat.cast_ne_zero.2
      (Nonempty.card_pos ⟨a, ha⟩).ne'), sub_eq_iff_eq_add'.1 hk, zpow_add, zpow_mul]
  simp only [zpow_natCast, coe_mul, comp_apply, EmbeddingLike.apply_eq_iff_eq]
  exact IsFixedPt.perm_zpow (hf.pow_card_apply ha) _
/-
**Equiv.Perm.IsCycleOn.exists_pow_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCy
cleOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α} {a b : α}, s.Finite → f.Is
CycleOn s → a ∈ s → b ∈ s → ∃ n, (f ^ n) a = b
参数：f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Equiv.Perm.IsCycleOn.exists_pow_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{a b : α} {s : Finset α},   f.IsCycleOn ↑s → a ∈ s → b ∈ s → ∃ n < s.card, (f ^ 
n) a = b
-/
theorem IsCycleOn.exists_pow_eq' (hs : s.Finite) (hf : f.IsCycleOn s) (ha : a ∈ s) (hb : b ∈ s) :
    ∃ n : ℕ, (f ^ n) a = b := by
  lift s to Finset α using hs
  obtain ⟨n, -, hn⟩ := hf.exists_pow_eq ha hb
  exact ⟨n, hn⟩
/-
**Equiv.Perm.IsCycleOn.range_pow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycleOn
`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α} {a : α},   s.Finite → f.Is
CycleOn s → a ∈ s → (Set.range fun n => (f ^ n) a) = s
参数：Set.range fun n => (f ^ n) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Set.MapsTo.perm_pow`：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Se
t.MapsTo (⇑f) s s → ∀ (n : ℕ), Set.MapsTo (⇑(f ^ n)) s s
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.Perm.IsCycleOn.exists_pow_eq'`：∀ {α : Type u_2} {f : Equiv.Perm α}
 {s : Set α} {a b : α}, s.Finite → f.IsCycleOn s → a ∈ s → b ∈ s → ∃ n, (f ^ n) 
a = b
-/
theorem IsCycleOn.range_pow (hs : s.Finite) (h : f.IsCycleOn s) (ha : a ∈ s) :
    Set.range (fun n => (f ^ n) a : ℕ → α) = s :=
  Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => h.1.mapsTo.perm_pow _ ha) fun _ =>
    h.exists_pow_eq' hs ha
/-
**Equiv.Perm.IsCycleOn.range_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycleO
n`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α} {a : α}, f.IsCycleOn s → a
 ∈ s → (Set.range fun n => (f ^ n) a) = s
参数：Set.range fun n => (f ^ n) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.BijOn.perm_zpow`：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Se
t.BijOn (⇑f) s s → ∀ (n : ℤ), Set.BijOn (⇑(f ^ n)) s s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsCycleOn.range_zpow (h : f.IsCycleOn s) (ha : a ∈ s) :
    Set.range (fun n => (f ^ n) a : ℤ → α) = s :=
  Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => (h.1.perm_zpow _).mapsTo ha) <| h.2 ha
/-
**Equiv.Perm.IsCycleOn.of_pow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycleOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α} {n : ℕ}, (f ^ n).IsCycleOn
 s → Set.BijOn (⇑f) s s → f.IsCycleOn s
参数：f ^ n；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.of_pow`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : 
α} {n : ℕ}, (f ^ n).SameCycle x y → f.SameCycle x y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsCycleOn.of_pow {n : ℕ} (hf : (f ^ n).IsCycleOn s) (h : Set.BijOn f s s) : f.IsCycleOn s :=
  ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_pow⟩
/-
**Equiv.Perm.IsCycleOn.of_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycleOn`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α} {n : ℤ}, (f ^ n).IsCycleOn
 s → Set.BijOn (⇑f) s s → f.IsCycleOn s
参数：f ^ n；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.of_zpow`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y :
 α} {n : ℤ}, (f ^ n).SameCycle x y → f.SameCycle x y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsCycleOn.of_zpow {n : ℤ} (hf : (f ^ n).IsCycleOn s) (h : Set.BijOn f s s) :
    f.IsCycleOn s :=
  ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_zpow⟩
/-
**Equiv.Perm.IsCycleOn.extendDomain** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycl
eOn`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {g : Equiv.Perm α} {s : Set α} {p : β → Pr
op} [inst : DecidablePred p]   (f : α ≃ Subtype p), g.IsCycleOn s → (g.extendDom
ain f).IsCycleOn (Subtype.val ∘ ⇑f '' s)
参数：f : α ≃ Subtype p；g.extendDomain f；Subtype.val ∘ ⇑f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.extendDomain`：∀ {α : Type u_1} {β : Type u_2} {p : β → Prop} [
inst : DecidablePred p] {f : α ≃ Subtype p} {g : Equiv.Perm α}   {s t : Set α}, 
Set.BijOn (⇑…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Equiv.Perm.SameCycle.extendDomain`：∀ {α : Type u_2} {β : Type u_3} {g : 
Equiv.Perm α} {x y : α} {p : β → Prop} [inst : DecidablePred p]   {f : α ≃ Subty
pe p}, g.SameCycle x y …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsCycleOn.extendDomain {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)
    (h : g.IsCycleOn s) : (g.extendDomain f).IsCycleOn ((↑) ∘ f '' s) :=
  ⟨h.1.extendDomain, by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (h.2 ha hb).extendDomain⟩
/-
**Equiv.Perm.IsCycleOn.countable** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycleOn
`。
形式化陈述：∀ {α : Type u_2} {f : Equiv.Perm α} {s : Set α}, f.IsCycleOn s → s.Countab
le
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.countable_empty`：∀ {α : Type u}, ∅.Countable
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableInt`：Countable ℤ
-/
protected theorem IsCycleOn.countable (hs : f.IsCycleOn s) : s.Countable := by
  obtain rfl | ⟨a, ha⟩ := s.eq_empty_or_nonempty
  · exact Set.countable_empty
  · exact (Set.countable_range fun n : ℤ => (⇑(f ^ n) : α → α) a).mono (hs.2 ha)


end IsCycleOn

end Equiv.Perm

namespace List

section

variable [DecidableEq α] {l : List α}

/-
**List.Nodup.isCycleOn_formPerm** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] {l : List α}, l.Nodup → l.formPerm
.IsCycleOn {a | a ∈ l}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijOn`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β) {s : Set α} {t 
: Set β}, (∀ (a : α), e a ∈ t ↔ a ∈ s) → Set.BijOn (⇑e) s t
· 使用定理 `List.formPerm_mem_iff_mem`：formPerm_mem_iff_mem : l.formPerm x in l ↔ x 
in l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.idxOf_lt_length_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] 
{l : List α} {a : α}, List.idxOf a l < l.length ↔ a ∈ l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `List.getElem_idxOf`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {x : α
} {xs : List α} (h : List.idxOf x xs < xs.length),   xs[List.idxOf x xs] = x
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `List.formPerm_pow_apply_getElem`：formPerm_pow_apply_getElem (l : List α)
 (w : Nodup l) (n : Nat) (i : Nat) (h : i < l.length) : (formPerm l ^ n) l[i] = 
l[(i + n) % l.length]…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem Nodup.isCycleOn_formPerm (h : l.Nodup) :
    l.formPerm.IsCycleOn { a | a ∈ l } := by
  refine ⟨l.formPerm.bijOn fun _ => List.formPerm_mem_iff_mem, fun a ha b hb => ?_⟩
  rw [Set.mem_ofPred, ← List.idxOf_lt_length_iff] at ha hb
  rw [← List.getElem_idxOf ha, ← List.getElem_idxOf hb]
  refine ⟨l.idxOf b - l.idxOf a, ?_⟩
  simp only [sub_eq_neg_add, zpow_add, zpow_neg, Equiv.Perm.inv_eq_iff_eq, zpow_natCast,
    Equiv.Perm.coe_mul, List.formPerm_pow_apply_getElem _ h, Function.comp]
  rw [add_comm]

end

end List

namespace Finset

variable [DecidableEq α] [Fintype α]

/-
**Finset.exists_cycleOn** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_cycleOn (s : Finset α) : exists f : Perm α, f.IsCycleOn s ∧ f.suppo
rt subseteq s
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.Nodup.isCycleOn_formPerm`：∀ {α : Type u_2} [inst : DecidableEq α] {
l : List α}, l.Nodup → l.formPerm.IsCycleOn {a | a ∈ l}
· 使用定理 `Finset.nodup_toList`：nodup_toList (s : Finset α) : s.toList.Nodup
· 使用定理 `List.mem_of_formPerm_apply_ne`：mem_of_formPerm_apply_ne (h : l.formPerm 
x != x) : x in l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
-/
theorem exists_cycleOn (s : Finset α) :
    ∃ f : Perm α, f.IsCycleOn s ∧ f.support ⊆ s := by
  refine ⟨s.toList.formPerm, ?_, fun x hx => by
    simpa using List.mem_of_formPerm_apply_ne (Perm.mem_support.1 hx)⟩
  convert! s.nodup_toList.isCycleOn_formPerm
  simp

end Finset

namespace Set

variable {f : Perm α} {s : Set α}

/-
**Set.Countable.exists_cycleOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.Countable`。
形式化陈述：∀ {α : Type u_2} {s : Set α}, s.Countable → ∃ f, f.IsCycleOn s ∧ {x | f x 
≠ x} ⊆ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_or_infinite`：∀ {α : Type u} (s : Set α), s.Finite ∨ s.Infinit
e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.Nodup.isCycleOn_formPerm`：∀ {α : Type u_2} [inst : DecidableEq α] {
l : List α}, l.Nodup → l.formPerm.IsCycleOn {a | a ∈ l}
· 使用定理 `Finset.nodup_toList`：nodup_toList (s : Finset α) : s.toList.Nodup
· 使用定理 `List.mem_of_formPerm_apply_ne`：mem_of_formPerm_apply_ne (h : l.formPerm 
x != x) : x in l
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Equiv.Perm.IsCycleOn.extendDomain`：∀ {α : Type u_2} {β : Type u_3} {g : 
Equiv.Perm α} {s : Set α} {p : β → Prop} [inst : DecidablePred p]   (f : α ≃ Sub
type p), g.IsCycleOn s …
· 使用定理 `Equiv.Perm.IsCycle.isCycleOn`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsC
ycle → f.IsCycleOn {x | f x ≠ x}
· 使用定理 `Int.addRight_one_isCycle`：(Equiv.addRight 1).IsCycle
（共 32 条，此处仅展示前 30 条）
-/
theorem Countable.exists_cycleOn (hs : s.Countable) :
    ∃ f : Perm α, f.IsCycleOn s ∧ { x | f x ≠ x } ⊆ s := by
  classical
  obtain hs' | hs' := s.finite_or_infinite
  · refine ⟨hs'.toFinset.toList.formPerm, ?_, fun x hx => by
      simpa using List.mem_of_formPerm_apply_ne hx⟩
    convert! hs'.toFinset.nodup_toList.isCycleOn_formPerm
    simp
  · have := hs.to_subtype
    have := hs'.to_subtype
    obtain ⟨f⟩ : Nonempty (ℤ ≃ s) := inferInstance
    refine ⟨(Equiv.addRight 1).extendDomain f, ?_, fun x hx =>
      of_not_not fun h => hx <| Perm.extendDomain_apply_not_subtype _ _ h⟩
    convert! Int.addRight_one_isCycle.isCycleOn.extendDomain f
    rw [Set.image_comp, Equiv.image_eq_preimage_symm]
    ext
    simp
/-
**Set.prod_self_eq_iUnion_perm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：prod_self_eq_iUnion_perm (hf : f.IsCycleOn s) : s ×ˢ s = ⋃ n : Int, (fun a
 => (a, (f ^ n) a)) '' s
参数：hf : f.IsCycleOn s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.BijOn.perm_zpow`：∀ {α : Type u_1} {f : Equiv.Perm α} {s : Set α}, Se
t.BijOn (⇑f) s s → ∀ (n : ℤ), Set.BijOn (⇑(f ^ n)) s s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem prod_self_eq_iUnion_perm (hf : f.IsCycleOn s) :
    s ×ˢ s = ⋃ n : ℤ, (fun a => (a, (f ^ n) a)) '' s := by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_image]
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := hf.2 hx.1 hx.2
    exact ⟨_, _, hx.1, rfl⟩
  · rintro ⟨n, a, ha, ⟨⟩⟩
    exact ⟨ha, (hf.1.perm_zpow _).mapsTo ha⟩

end Set

namespace Finset

variable {f : Perm α} {s : Finset α}

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.product_self_eq_disjiUnion_perm_aux** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_self_eq_disjiUnion_perm_aux (hf : f.IsCycleOn s) : (range #s : Set
 Nat).PairwiseDisjoint fun k => s.map ⟨fun i => (i, (f ^ k) i), fun _ _ => congr
_arg Prod.fst⟩
参数：hf : f.IsCycleOn s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.subsingleton_or_nontrivial`：∀ {α : Type u} (s : Set α), s.Subsinglet
on ∨ s.Nontrivial
· 使用定理 `Set.Subsingleton.pairwise`：∀ {α : Type u_1} {s : Set α}, s.Subsingleton 
→ ∀ (r : α → α → Prop), s.Pairwise r
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Nat.ModEq.eq_of_lt_of_lt`：eq_of_lt_of_lt (h : a ≡ b [MOD m]) (ha : a < m
) (hb : b < m) : a = b
· 使用定理 `Equiv.Perm.IsCycleOn.pow_apply_eq_pow_apply`：∀ {α : Type u_2} {f : Equiv
.Perm α} {a : α} {s : Finset α},   f.IsCycleOn ↑s → a ∈ s → ∀ {m n : ℕ}, (f ^ m)
 a = (f ^ n) a ↔ m ≡ n [MOD s.car…
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
-/
theorem product_self_eq_disjiUnion_perm_aux (hf : f.IsCycleOn s) :
    (range #s : Set ℕ).PairwiseDisjoint fun k =>
      s.map ⟨fun i => (i, (f ^ k) i), fun _ _ => congr_arg Prod.fst⟩ := by
  obtain hs | _ := (s : Set α).subsingleton_or_nontrivial
  · refine Set.Subsingleton.pairwise ?_ _
    simp_rw [Set.Subsingleton, mem_coe, ← card_le_one] at hs ⊢
    rwa [card_range]
  classical
    rintro m hm n hn hmn
    simp only [disjoint_left, Function.onFun, mem_map, Function.Embedding.coeFn_mk,
      not_exists, not_and, forall_exists_index, and_imp, Prod.forall, Prod.mk_inj]
    rintro _ _ _ - rfl rfl a ha rfl h
    rw [hf.pow_apply_eq_pow_apply ha] at h
    rw [mem_coe, mem_range] at hm hn
    exact hmn.symm (h.eq_of_lt_of_lt hn hm)

/-- We can partition the square `s ×ˢ s` into shifted diagonals as such:
```
01234
40123
34012
23401
12340
```

The diagonals are given by the cycle `f`.
-/
/-
**Finset.product_self_eq_disjiUnion_perm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：product_self_eq_disjiUnion_perm (hf : f.IsCycleOn s) : s ×ˢ s = (range #s)
.disjiUnion (fun k => s.map ⟨fun i => (i, (f ^ k) i), fun _ _ => congr_arg Prod.
fst⟩) (product_self_eq_disjiUnion_perm_aux hf)
参数：hf : f.IsCycleOn s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.product_self_eq_disjiUnion_perm_aux`：product_self_eq_disjiUnion_p
erm_aux (hf : f.IsCycleOn s) : (range #s : Set Nat).PairwiseDisjoint fun k => s.
map ⟨fun i => (i, (f ^ k) i), fu…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.Perm.IsCycleOn.exists_pow_eq`：∀ {α : Type u_2} {f : Equiv.Perm α} 
{a b : α} {s : Finset α},   f.IsCycleOn ↑s → a ∈ s → b ∈ s → ∃ n < s.card, (f ^ 
n) a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Equiv.Perm.iterate_eq_pow`：iterate_eq_pow (f : Perm α) (n : Nat) : f^[n]
 = ⇑(f ^ n)
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t
· 使用定理 `Set.BijOn.iterate`：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.BijOn f
 s s → ∀ (n : ℕ), Set.BijOn f^[n] s s

--- 原说明 ---
We can partition the square `s ×ˢ s` into shifted diagonals as such:
```
01234
40123
34012
23401
12340
```

The diagonals are given by the cycle `f`.
-/
theorem product_self_eq_disjiUnion_perm (hf : f.IsCycleOn s) :
    s ×ˢ s =
      (range #s).disjiUnion
        (fun k => s.map ⟨fun i => (i, (f ^ k) i), fun _ _ => congr_arg Prod.fst⟩)
        (product_self_eq_disjiUnion_perm_aux hf) := by
  ext ⟨a, b⟩
  simp only [mem_product, Equiv.Perm.coe_pow, mem_disjiUnion, mem_range, mem_map,
    Function.Embedding.coeFn_mk, Prod.mk_inj]
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨n, hn, rfl⟩ := hf.exists_pow_eq hx.1 hx.2
    exact ⟨n, hn, a, hx.1, rfl, by rw [f.iterate_eq_pow]⟩
  · rintro ⟨n, -, a, ha, rfl, rfl⟩
    exact ⟨ha, (hf.1.iterate _).mapsTo ha⟩

end Finset

namespace Finset

variable [Semiring α] [AddCommMonoid β] [Module α β] {s : Finset ι} {σ : Perm ι}

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.sum_smul_sum_eq_sum_perm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_smul_sum_eq_sum_perm (hσ : σ.IsCycleOn s) (f : ι -> α) (g : ι -> β) : 
(∑ i in s, f i) • ∑ i in s, g i = ∑ k in range #s, ∑ i in s, f i • g ((σ ^ k) i)
参数：hσ : σ.IsCycleOn s；f : ι -> α；g : ι -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sum_smul_sum`：Finset.sum_smul_sum (s : Finset α) (t : Finset β) {
f : α -> R} {g : β -> M} : (∑ i in s, f i) • ∑ j in t, g j = ∑ i in s, ∑ j in t,
 f i • g …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_product'`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [ins
t : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ → α → β),   ∑ x ∈ s ×ˢ
 t, f x.1…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.product_self_eq_disjiUnion_perm_aux`：product_self_eq_disjiUnion_p
erm_aux (hf : f.IsCycleOn s) : (range #s : Set Nat).PairwiseDisjoint fun k => s.
map ⟨fun i => (i, (f ^ k) i), fu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.product_self_eq_disjiUnion_perm`：product_self_eq_disjiUnion_perm 
(hf : f.IsCycleOn s) : s ×ˢ s = (range #s).disjiUnion (fun k => s.map ⟨fun i => 
(i, (f ^ k) i), fun _ _ => c…
· 使用定理 `Finset.sum_disjiUnion`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [i
nst : AddCommMonoid M] {f : ι → M} (s : Finset κ) (t : κ → Finset ι)   (h : (↑s)
.PairwiseDi…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_smul_sum_eq_sum_perm (hσ : σ.IsCycleOn s) (f : ι → α) (g : ι → β) :
    (∑ i ∈ s, f i) • ∑ i ∈ s, g i = ∑ k ∈ range #s, ∑ i ∈ s, f i • g ((σ ^ k) i) := by
  rw [sum_smul_sum, ← sum_product']
  simp_rw [product_self_eq_disjiUnion_perm hσ, sum_disjiUnion, sum_map, Embedding.coeFn_mk]
/-
**Finset.sum_mul_sum_eq_sum_perm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_mul_sum_eq_sum_perm (hσ : σ.IsCycleOn s) (f g : ι -> α) : ((∑ i in s, 
f i) * ∑ i in s, g i) = ∑ k in range #s, ∑ i in s, f i * g ((σ ^ k) i)
参数：hσ : σ.IsCycleOn s；f g : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_smul_sum_eq_sum_perm`：sum_smul_sum_eq_sum_perm (hσ : σ.IsCycl
eOn s) (f : ι -> α) (g : ι -> β) : (∑ i in s, f i) • ∑ i in s, g i = ∑ k in rang
e #s, ∑ i in s, f i •…
-/
theorem sum_mul_sum_eq_sum_perm (hσ : σ.IsCycleOn s) (f g : ι → α) :
    ((∑ i ∈ s, f i) * ∑ i ∈ s, g i) = ∑ k ∈ range #s, ∑ i ∈ s, f i * g ((σ ^ k) i) :=
  sum_smul_sum_eq_sum_perm hσ f g

end Finset

namespace Equiv.Perm

/-
**Equiv.Perm.subtypePerm_apply_pow_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：subtypePerm_apply_pow_of_mem {g : Perm α} {s : Finset α} (hs : forall x : 
α, g x in s ↔ x in s) {n : Nat} {x : α} (hx : x in s) : ((g.subtypePerm hs ^ n) 
(⟨x, hx⟩ : s) : α) = (g ^ n) x
参数：hs : forall x : α, g x in s ↔ x in s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Algebra.Group.End.0.Equiv.Perm.pow_aux`：∀ {α : Type u_4
} {p : α → Prop} {f : Equiv.Perm α}, (∀ (x : α), p (f x) ↔ p x) → ∀ {n : ℕ} (x :
 α), p ((f ^ n) x) ↔ p x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.Perm.subtypePerm_pow`：subtypePerm_pow (f : Perm α) (n : Nat) (hf) 
: (f.subtypePerm hf : Perm { x // p x }) ^ n = (f ^ n).subtypePerm (pow_aux hf)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subtypePerm_apply_pow_of_mem {g : Perm α} {s : Finset α}
    (hs : ∀ x : α, g x ∈ s ↔ x ∈ s) {n : ℕ} {x : α} (hx : x ∈ s) :
    ((g.subtypePerm hs ^ n) (⟨x, hx⟩ : s) : α) = (g ^ n) x := by
  simp only [subtypePerm_pow, subtypePerm_apply]
/-
**Equiv.Perm.subtypePerm_apply_zpow_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：subtypePerm_apply_zpow_of_mem {g : Perm α} {s : Finset α} (hs : forall x :
 α, g x in s ↔ x in s) {i : Int} {x : α} (hx : x in s) : ((g.subtypePerm hs ^ i)
 (⟨x, hx⟩ : s) : α) = (g ^ i) x
参数：hs : forall x : α, g x in s ↔ x in s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Algebra.Group.End.0.Equiv.Perm.zpow_aux`：∀ {α : Type u_
4} {p : α → Prop} {f : Equiv.Perm α}, (∀ (x : α), p (f x) ↔ p x) → ∀ {n : ℤ} (x 
: α), p ((f ^ n) x) ↔ p x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.Perm.subtypePerm_zpow`：subtypePerm_zpow (f : Perm α) (n : Int) (hf
) : (f.subtypePerm hf ^ n : Perm { x // p x }) = (f ^ n).subtypePerm (zpow_aux h
f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subtypePerm_apply_zpow_of_mem {g : Perm α} {s : Finset α}
    (hs : ∀ x : α, g x ∈ s ↔ x ∈ s) {i : ℤ} {x : α} (hx : x ∈ s) :
    ((g.subtypePerm hs ^ i) (⟨x, hx⟩ : s) : α) = (g ^ i) x := by
  simp only [subtypePerm_zpow, subtypePerm_apply]

variable [Fintype α] [DecidableEq α]

/-- Restrict a permutation to its support -/
/-
**Equiv.Perm.subtypePermOfSupport** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePermOfSupport (c : Perm α) : Perm c.support
参数：c : Perm α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.apply_mem_support`：apply_mem_support {x : α} : f x in f.suppo
rt ↔ x in f.support

--- 原说明 ---
Restrict a permutation to its support
-/
def subtypePermOfSupport (c : Perm α) : Perm c.support :=
  subtypePerm c fun _ : α => apply_mem_support

/-- Restrict a permutation to a Finset containing its support -/
/-
**Equiv.Perm.subtypePerm_of_support_le** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm`。
形式化陈述：subtypePerm_of_support_le (c : Perm α) {s : Finset α} (hcs : c.support sub
seteq s) : Equiv.Perm s
参数：c : Perm α；hcs : c.support subseteq s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.isInvariant_of_support_le`：isInvariant_of_support_le {c : Per
m α} {s : Finset α} (hcs : c.support <= s) (x : α) : c x in s ↔ x in s

--- 原说明 ---
Restrict a permutation to a Finset containing its support
-/
def subtypePerm_of_support_le (c : Perm α) {s : Finset α}
    (hcs : c.support ⊆ s) : Equiv.Perm s :=
  subtypePerm c (isInvariant_of_support_le hcs)

/-- Support of a cycle is nonempty -/
/-
**Equiv.Perm.IsCycle.nonempty_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCy
cle`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α] {g : Equiv.Pe
rm α}, g.IsCycle → g.support.Nonempty
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Equiv.Perm.support_eq_empty_iff`：support_eq_empty_iff {σ : Perm α} : σ.s
upport = ∅ ↔ σ = 1
· 使用定理 `Equiv.Perm.IsCycle.ne_one`：∀ {α : Type u_2} {f : Equiv.Perm α}, f.IsCycl
e → f ≠ 1

--- 原说明 ---
Support of a cycle is nonempty
-/
theorem IsCycle.nonempty_support {g : Perm α} (hg : g.IsCycle) :
    g.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty_iff]
  exact IsCycle.ne_one hg

/-- Centralizer of a cycle is a power of that cycle on the cycle -/
/-
**Equiv.Perm.IsCycle.commute_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`
。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α] {g c : Equiv.
Perm α},   c.IsCycle →     (Commute g c ↔       ∃ (hc' : ∀ (x : α), g x ∈ c.supp
ort ↔ x ∈ c.support), g.subtypePerm hc' ∈ Subgroup.zpowers c.subtypePermOfSuppor
t)
参数：Commute g c ↔       ∃ (hc' : ∀ (x : α), g x ∈ c.support ↔ x ∈ c.support), g.s
ubtypePerm hc' ∈ Subgroup.zpowers c.subtypePermOfSupport。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.mem_support_iff_of_commute`：mem_support_iff_of_commute {g c :
 Perm α} (hgc : Commute g c) (x : α) : g x in c.support ↔ x in c.support
· 使用定理 `Equiv.Perm.IsCycle.nonempty_support`：∀ {α : Type u_2} [inst : Fintype α]
 [inst_1 : DecidableEq α] {g : Equiv.Perm α}, g.IsCycle → g.support.Nonempty
· 使用定理 `Equiv.Perm.IsCycle.sameCycle`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y :
 α}, f.IsCycle → f x ≠ x → f y ≠ y → f.SameCycle x y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Equiv.Perm.apply_mem_support`：apply_mem_support {x : α} : f x in f.suppo
rt ↔ x in f.support
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.subtypePerm_apply_zpow_of_mem`：subtypePerm_apply_zpow_of_mem 
{g : Perm α} {s : Finset α} (hs : forall x : α, g x in s ↔ x in s) {i : Int} {x 
: α} (hx : x in s) : ((g.subty…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用引理 `Commute.zpow_right`：zpow_right (h : Commute a b) (m : Int) : Commute a (
b ^ m)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Equiv.Perm.congr_fun`：∀ {α : Sort u} {f g : Equiv.Perm α}, f = g → ∀ (x 
: α), f x = g x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)

--- 原说明 ---
Centralizer of a cycle is a power of that cycle on the cycle
-/
theorem IsCycle.commute_iff' {g c : Perm α} (hc : c.IsCycle) :
    Commute g c ↔
      ∃ hc' : ∀ x : α, g x ∈ c.support ↔ x ∈ c.support,
        subtypePerm g hc' ∈ Subgroup.zpowers c.subtypePermOfSupport := by
  constructor
  · intro hgc
    have hgc' := mem_support_iff_of_commute hgc
    use hgc'
    obtain ⟨a, ha⟩ := IsCycle.nonempty_support hc
    obtain ⟨i, hi⟩ := hc.sameCycle (mem_support.mp ha) (mem_support.mp ((hgc' a).mpr ha))
    use i
    ext ⟨x, hx⟩
    simp only [subtypePermOfSupport, Subtype.coe_mk, subtypePerm_apply]
    rw [subtypePerm_apply_zpow_of_mem]
    obtain ⟨j, rfl⟩ := hc.sameCycle (mem_support.mp ha) (mem_support.mp hx)
    simp only [← mul_apply, Commute.eq (Commute.zpow_right hgc j)]
    rw [← zpow_add, add_comm i j, zpow_add]
    simp only [mul_apply, EmbeddingLike.apply_eq_iff_eq]
    exact hi
  · rintro ⟨hc', ⟨i, hi⟩⟩
    ext x
    simp only [coe_mul, Function.comp_apply]
    by_cases hx : x ∈ c.support
    · suffices hi' : ∀ x ∈ c.support, g x = (c ^ i) x by
        rw [hi' x hx, hi' (c x) (apply_mem_support.mpr hx)]
        simp only [← mul_apply, ← zpow_add_one, ← zpow_one_add, add_comm]
      intro x hx
      have hix := Perm.congr_fun hi ⟨x, hx⟩
      simp only [← Subtype.coe_inj, subtypePermOfSupport, subtypePerm_apply,
        subtypePerm_apply_zpow_of_mem] at hix
      exact hix.symm
    · rw [notMem_support.mp hx, eq_comm, ← notMem_support]
      contrapose hx
      exact (hc' x).mp hx

/-- A permutation `g` commutes with a cycle `c` if and only if
  `c.support` is invariant under `g`, and `g` acts on it as a power of `c`. -/
/-
**Equiv.Perm.IsCycle.commute_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.IsCycle`。
形式化陈述：∀ {α : Type u_2} [inst : Fintype α] [inst_1 : DecidableEq α] {g c : Equiv.
Perm α},   c.IsCycle →     (Commute g c ↔       ∃ (hc' : ∀ (x : α), g x ∈ c.supp
ort ↔ x ∈ c.support),         Equiv.Perm.ofSubtype (g.subtypePerm hc') ∈ Subgrou
p.zpowers c)
参数：Commute g c ↔       ∃ (hc' : ∀ (x : α), g x ∈ c.support ↔ x ∈ c.support),    
     Equiv.Perm.ofSubtype (g.subtypePerm hc') ∈ Subgroup.zpowers c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.IsCycle.commute_iff'`：∀ {α : Type u_2} [inst : Fintype α] [in
st_1 : DecidableEq α] {g c : Equiv.Perm α},   c.IsCycle →     (Commute g c ↔    
   ∃ (hc' : ∀ (x : α)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Equiv.Perm.apply_mem_support`：apply_mem_support {x : α} : f x in f.suppo
rt ↔ x in f.support
· 使用定理 `Equiv.Perm.subtypePermOfSupport.eq_1`：∀ {α : Type u_2} [inst : Fintype α
] [inst_1 : DecidableEq α] (c : Equiv.Perm α),   c.subtypePermOfSupport = c.subt
ypePerm ⋯
· 使用定理 `_private.Mathlib.Algebra.Group.End.0.Equiv.Perm.zpow_aux`：∀ {α : Type u_
4} {p : α → Prop} {f : Equiv.Perm α}, (∀ (x : α), p (f x) ↔ p x) → ∀ {n : ℤ} (x 
: α), p ((f ^ n) x) ↔ p x
· 使用定理 `Equiv.Perm.subtypePerm_zpow`：subtypePerm_zpow (f : Perm α) (n : Int) (hf
) : (f.subtypePerm hf ^ n : Perm { x // p x }) = (f ^ n).subtypePerm (zpow_aux h
f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `imp_iff_right`：∀ {b a : Prop}, a → (a → b ↔ b)
· 使用定理 `Equiv.Perm.ofSubtype_subtypePerm_of_mem`：ofSubtype_subtypePerm_of_mem {p
 : α -> Prop} [DecidablePred p] {g : Perm α} (hg : forall (x : α), p (g x) ↔ p x
) {a : α} (ha : p a) : (ofSub…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `iff_true_left`：∀ {a b : Prop}, a → ((a ↔ b) ↔ b)
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `Finset.notMem_mono`：notMem_mono {s t : Finset α} (h : s subseteq t) {a :
 α} : a ∉ t -> a ∉ s
· 使用定理 `Equiv.Perm.support_zpow_le`：support_zpow_le (σ : Perm α) (n : Int) : (σ 
^ n).support <= σ.support

--- 原说明 ---
A permutation `g` commutes with a cycle `c` if and only if
  `c.support` is invariant under `g`, and `g` acts on it as a power of `c`.
-/
theorem IsCycle.commute_iff {g c : Perm α} (hc : c.IsCycle) :
    Commute g c ↔
      ∃ hc' : ∀ x : α, g x ∈ c.support ↔ x ∈ c.support,
        ofSubtype (subtypePerm g hc') ∈ Subgroup.zpowers c := by
  simp_rw [hc.commute_iff', Subgroup.mem_zpowers_iff]
  refine exists_congr fun hc' => exists_congr fun k => ?_
  rw [subtypePermOfSupport, subtypePerm_zpow c k]
  simp only [Perm.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  apply forall_congr'
  intro a
  by_cases ha : a ∈ c.support
  · rw [imp_iff_right ha, ofSubtype_subtypePerm_of_mem hc' ha]
  · rw [iff_true_left (fun b ↦ (ha b).elim), ofSubtype_apply_of_not_mem, ← notMem_support]
    · exact Finset.notMem_mono (support_zpow_le c k) ha
    · exact ha
/-
**Equiv.Perm.zpow_eq_ofSubtype_subtypePerm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Perm`。
形式化陈述：zpow_eq_ofSubtype_subtypePerm_iff {g c : Equiv.Perm α} {s : Finset α} (hg 
: forall x, g x in s ↔ x in s) (hc : c.support subseteq s) (n : Int) : c ^ n = o
fSubtype (g.subtypePerm hg) ↔ c.subtypePerm (isInvariant_of_support_le hc) ^ n =
 g.subtypePerm hg
参数：hg : forall x, g x in s ↔ x in s；hc : c.support subseteq s；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.isInvariant_of_support_le`：isInvariant_of_support_le {c : Per
m α} {s : Finset α} (hcs : c.support <= s) (x : α) : c x in s ↔ x in s
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Algebra.Group.End.0.Equiv.Perm.zpow_aux`：∀ {α : Type u_
4} {p : α → Prop} {f : Equiv.Perm α}, (∀ (x : α), p (f x) ↔ p x) → ∀ {n : ℤ} (x 
: α), p ((f ^ n) x) ↔ p x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.Perm.congr_fun`：∀ {α : Sort u} {f g : Equiv.Perm α}, f = g → ∀ (x 
: α), f x = g x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.Perm.subtypePerm_zpow`：subtypePerm_zpow (f : Perm α) (n : Int) (hf
) : (f.subtypePerm hf ^ n : Perm { x // p x }) = (f ^ n).subtypePerm (zpow_aux h
f)
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Equiv.Perm.ofSubtype_subtypePerm_of_mem`：ofSubtype_subtypePerm_of_mem {p
 : α -> Prop} [DecidablePred p] {g : Perm α} (hg : forall (x : α), p (g x) ↔ p x
) {a : α} (ha : p a) : (ofSub…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_mem`：ofSubtype_apply_of_mem (f : Perm (Sub
type p)) (ha : p a) : ofSubtype f a = f ⟨a, ha⟩
· 使用定理 `Equiv.Perm.subtypePerm_apply`：subtypePerm_apply (f : Perm α) (h : forall
 x, p (f x) ↔ p x) (x : { x // p x }) : subtypePerm f h x = ⟨f x, (h _).2 x.2⟩
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `Equiv.Perm.support_zpow_le`：support_zpow_le (σ : Perm α) (n : Int) : (σ 
^ n).support <= σ.support
-/
theorem zpow_eq_ofSubtype_subtypePerm_iff
    {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, g x ∈ s ↔ x ∈ s) (hc : c.support ⊆ s) (n : ℤ) :
    c ^ n = ofSubtype (g.subtypePerm hg) ↔
      c.subtypePerm (isInvariant_of_support_le hc) ^ n = g.subtypePerm hg := by
  constructor
  · intro h
    ext ⟨x, hx⟩
    simpa [Perm.congr_fun h _] using ofSubtype_subtypePerm_of_mem _ hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x ∈ s
    · rw [ofSubtype_apply_of_mem (subtypePerm c _ ^ n) hx,
        subtypePerm_zpow, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (subtypePerm c _ ^ n) hx,
        ← notMem_support]
      exact fun hx' ↦ hx (hc (support_zpow_le _ _ hx'))
/-
**Equiv.Perm.cycle_zpow_mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycle_zpow_mem_support_iff {g : Perm α} (hg : g.IsCycle) {n : Int} {x : α}
 (hx : g x != x) : (g ^ n) x = x ↔ n % #g.support = 0
参数：hg : g.IsCycle；hx : g x != x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ediv_emod_unique`：∀ {a b r q : ℤ}, 0 < b → (a / b = q ∧ a % b = r ↔ 
r + b * q = a ∧ 0 ≤ r ∧ r < b)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Equiv.Perm.IsCycle.two_le_card_support`：∀ {α : Type u_2} {f : Equiv.Perm
 α} [inst : DecidableEq α] [inst_1 : Fintype α], f.IsCycle → 2 ≤ f.support.card
· 使用定理 `Int.eq_ofNat_of_zero_le`：∀ {a : ℤ}, 0 ≤ a → ∃ n, a = ↑n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `zpow_mul`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (m n : ℤ), 
a ^ (m * n) = (a ^ m) ^ n
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用定理 `Equiv.Perm.IsCycle.pow_eq_one_iff`：∀ {β : Type u_3} [Finite β] {f : Equi
v.Perm β}, f.IsCycle → ∀ {n : ℕ}, f ^ n = 1 ↔ ∃ x, f x ≠ x ∧ (f ^ n) x = x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
（共 31 条，此处仅展示前 30 条）
-/
theorem cycle_zpow_mem_support_iff {g : Perm α}
    (hg : g.IsCycle) {n : ℤ} {x : α} (hx : g x ≠ x) :
    (g ^ n) x = x ↔ n % #g.support = 0 := by
  set q := n / #g.support
  set r := n % #g.support
  have div_euc : r + #g.support * q = n ∧ 0 ≤ r ∧ r < #g.support := by
    rw [← Int.ediv_emod_unique _]
    · exact ⟨rfl, rfl⟩
    simp only [Int.natCast_pos]
    apply lt_of_lt_of_le _ (IsCycle.two_le_card_support hg); simp
  simp only [← hg.orderOf] at div_euc
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le div_euc.2.1
  simp only [hm, Nat.cast_nonneg, Nat.cast_lt, true_and] at div_euc
  rw [← div_euc.1, zpow_add g]
  simp only [hm, Nat.cast_eq_zero, zpow_natCast, coe_mul, comp_apply, zpow_mul,
    pow_orderOf_eq_one, one_zpow, coe_one, id_eq]
  have : (g ^ m) x = x ↔ g ^ m = 1 := by
    constructor
    · intro hgm
      simp only [IsCycle.pow_eq_one_iff hg]
      use x
    · intro hgm
      simp only [hgm, coe_one, id_eq]
  rw [this]
  by_cases hm0 : m = 0
  · simp only [hm0, pow_zero]
  · simp only [hm0, iff_false]
    exact pow_ne_one_of_lt_orderOf hm0 div_euc.2

end Perm

end Equiv

