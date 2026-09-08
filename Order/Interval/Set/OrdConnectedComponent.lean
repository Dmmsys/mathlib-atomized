/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Data.Set.Lattice.Image

/-!
# Order connected components of a set

In this file we define `Set.ordConnectedComponent s x` to be the set of `y` such that
`Set.uIcc x y ⊆ s` and prove some basic facts about this definition. At the moment of writing,
this construction is used only to prove that any linear order with order topology is a T₅ space,
so we only add API needed for this lemma.
-/

@[expose] public section


open Interval Function OrderDual

namespace Set

variable {α : Type*} [LinearOrder α] {s t : Set α} {x y z : α}

/-- Order-connected component of a point `x` in a set `s`. It is defined as the set of `y` such that
`Set.uIcc x y ⊆ s`. Note that it is empty if and only if `x ∉ s`. -/
/-
**Set.ordConnectedComponent** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：ordConnectedComponent (s : Set α) (x : α) : Set α
参数：s : Set α；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order-connected component of a point `x` in a set `s`. It is defined as the set 
of `y` such that
`Set.uIcc x y ⊆ s`. Note that it is empty if and only if `x ∉ s`.
-/
def ordConnectedComponent (s : Set α) (x : α) : Set α :=
  { y | [[x, y]] ⊆ s }
/-
**Set.mem_ordConnectedComponent** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_ordConnectedComponent : y in ordConnectedComponent s x ↔ [[x, y]] subs
eteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ordConnectedComponent : y ∈ ordConnectedComponent s x ↔ [[x, y]] ⊆ s :=
  Iff.rfl
/-
**Set.dual_ordConnectedComponent** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：dual_ordConnectedComponent : ordConnectedComponent (ofDual ⁻¹' s) (toDual 
x) = ofDual ⁻¹' ordConnectedComponent s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Set.uIcc_toDual`：uIcc_toDual (a b : α) : [[toDual a, toDual b]] = ofDual
 ⁻¹' [[a, b]]
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dual_ordConnectedComponent :
    ordConnectedComponent (ofDual ⁻¹' s) (toDual x) = ofDual ⁻¹' ordConnectedComponent s x :=
  ext <| (Surjective.forall toDual.surjective).2 fun x => by simp [mem_ordConnectedComponent]
/-
**Set.ordConnectedComponent_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnectedComponent_subset : ordConnectedComponent s x subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.right_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, b ∈ S
et.uIcc a b
-/
theorem ordConnectedComponent_subset : ordConnectedComponent s x ⊆ s := fun _ hy =>
  hy right_mem_uIcc
/-
**Set.subset_ordConnectedComponent** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_ordConnectedComponent {t} [h : OrdConnected s] (hs : x in s) (ht : 
s subseteq t) : s subseteq ordConnectedComponent t x
参数：hs : x in s；ht : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.OrdConnected.uIcc_subset`：∀ {α : Type u_1} [inst : LinearOrder α] {s
 : Set α},   s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.uIcc x y
 ⊆ s
-/
theorem subset_ordConnectedComponent {t} [h : OrdConnected s] (hs : x ∈ s) (ht : s ⊆ t) :
    s ⊆ ordConnectedComponent t x := fun _ hy => (h.uIcc_subset hs hy).trans ht

@[simp]
/-
**Set.self_mem_ordConnectedComponent** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：self_mem_ordConnectedComponent : x in ordConnectedComponent s x ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ordConnectedComponent`：mem_ordConnectedComponent : y in ordConne
ctedComponent s x ↔ [[x, y]] subseteq s
· 使用引理 `Set.uIcc_self`：uIcc_self : [[a, a]] = {a}
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem self_mem_ordConnectedComponent : x ∈ ordConnectedComponent s x ↔ x ∈ s := by
  rw [mem_ordConnectedComponent, uIcc_self, singleton_subset_iff]

@[simp]
/-
**Set.nonempty_ordConnectedComponent** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_ordConnectedComponent : (ordConnectedComponent s x).Nonempty ↔ x 
in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.left_mem_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, a ∈ Se
t.uIcc a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.self_mem_ordConnectedComponent`：self_mem_ordConnectedComponent : x i
n ordConnectedComponent s x ↔ x in s
-/
theorem nonempty_ordConnectedComponent : (ordConnectedComponent s x).Nonempty ↔ x ∈ s :=
  ⟨fun ⟨_, hy⟩ => hy <| left_mem_uIcc, fun h => ⟨x, self_mem_ordConnectedComponent.2 h⟩⟩

@[simp]
/-
**Set.ordConnectedComponent_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnectedComponent_eq_empty : ordConnectedComponent s x = ∅ ↔ x ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Set.nonempty_ordConnectedComponent`：nonempty_ordConnectedComponent : (or
dConnectedComponent s x).Nonempty ↔ x in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ordConnectedComponent_eq_empty : ordConnectedComponent s x = ∅ ↔ x ∉ s := by
  rw [← not_nonempty_iff_eq_empty, nonempty_ordConnectedComponent]

@[simp]
/-
**Set.ordConnectedComponent_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnectedComponent_empty : ordConnectedComponent ∅ x = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ordConnectedComponent_eq_empty`：ordConnectedComponent_eq_empty : ord
ConnectedComponent s x = ∅ ↔ x ∉ s
· 使用定理 `Set.notMem_empty`：notMem_empty (x : α) : x ∉ (∅ : Set α)
-/
theorem ordConnectedComponent_empty : ordConnectedComponent ∅ x = ∅ :=
  ordConnectedComponent_eq_empty.2 (notMem_empty x)

@[simp]
/-
**Set.ordConnectedComponent_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnectedComponent_univ : ordConnectedComponent univ x = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordConnectedComponent_univ : ordConnectedComponent univ x = univ := by
  simp [ordConnectedComponent]
/-
**Set.ordConnectedComponent_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnectedComponent_inter (s t : Set α) (x : α) : ordConnectedComponent 
(s inter t) x = ordConnectedComponent s x inter ordConnectedComponent t x
参数：s t : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordConnectedComponent_inter (s t : Set α) (x : α) :
    ordConnectedComponent (s ∩ t) x = ordConnectedComponent s x ∩ ordConnectedComponent t x := by
  simp [ordConnectedComponent, ofPred_and]
/-
**Set.mem_ordConnectedComponent_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_ordConnectedComponent_comm : y in ordConnectedComponent s x ↔ x in ord
ConnectedComponent s y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ordConnectedComponent`：mem_ordConnectedComponent : y in ordConne
ctedComponent s x ↔ [[x, y]] subseteq s
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ordConnectedComponent_comm :
    y ∈ ordConnectedComponent s x ↔ x ∈ ordConnectedComponent s y := by
  rw [mem_ordConnectedComponent, mem_ordConnectedComponent, uIcc_comm]
/-
**Set.mem_ordConnectedComponent_trans** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_ordConnectedComponent_trans (hxy : y in ordConnectedComponent s x) (hy
z : z in ordConnectedComponent s y) : z in ordConnectedComponent s x
参数：hxy : y in ordConnectedComponent s x；hyz : z in ordConnectedComponent s y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.uIcc_subset_uIcc_union_uIcc`：uIcc_subset_uIcc_union_uIcc : [[a, c]] 
subseteq [[a, b]] union [[b, c]]
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
-/
theorem mem_ordConnectedComponent_trans (hxy : y ∈ ordConnectedComponent s x)
    (hyz : z ∈ ordConnectedComponent s y) : z ∈ ordConnectedComponent s x :=
  calc
    [[x, z]] ⊆ [[x, y]] ∪ [[y, z]] := uIcc_subset_uIcc_union_uIcc
    _ ⊆ s := union_subset hxy hyz
/-
**Set.ordConnectedComponent_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnectedComponent_eq (h : [[x, y]] subseteq s) : ordConnectedComponent
 s x = ordConnectedComponent s y
参数：h : [[x, y]] subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_ordConnectedComponent_trans`：mem_ordConnectedComponent_trans (hx
y : y in ordConnectedComponent s x) (hyz : z in ordConnectedComponent s y) : z i
n ordConnectedComponent s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ordConnectedComponent_comm`：mem_ordConnectedComponent_comm : y i
n ordConnectedComponent s x ↔ x in ordConnectedComponent s y
-/
theorem ordConnectedComponent_eq (h : [[x, y]] ⊆ s) :
    ordConnectedComponent s x = ordConnectedComponent s y :=
  ext fun _ =>
    ⟨mem_ordConnectedComponent_trans (mem_ordConnectedComponent_comm.2 h),
      mem_ordConnectedComponent_trans h⟩
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrdConnected (ordConnectedComponent s x) :=
  ordConnected_of_uIcc_subset_left fun _ hy _ hz => (uIcc_subset_uIcc_left hz).trans hy

/-- Projection from `s : Set α` to `α` sending each order connected component of `s` to a single
point of this component. -/
/-
**Set.ordConnectedProj** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：ordConnectedProj (s : Set α) : s -> α
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Projection from `s : Set α` to `α` sending each order connected component of `s`
 to a single
point of this component.
-/
noncomputable def ordConnectedProj (s : Set α) : s → α := fun x : s =>
  (nonempty_ordConnectedComponent.2 x.2).some
/-
**Set.ordConnectedProj_mem_ordConnectedComponent** 是 Mathlib 中的一个定理，位于命名空间 `Set`
。
形式化陈述：ordConnectedProj_mem_ordConnectedComponent (s : Set α) (x : s) : ordConnec
tedProj s x in ordConnectedComponent s x
参数：s : Set α；x : s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
-/
theorem ordConnectedProj_mem_ordConnectedComponent (s : Set α) (x : s) :
    ordConnectedProj s x ∈ ordConnectedComponent s x :=
  Nonempty.some_mem _
/-
**Set.mem_ordConnectedComponent_ordConnectedProj** 是 Mathlib 中的一个定理，位于命名空间 `Set`
。
形式化陈述：mem_ordConnectedComponent_ordConnectedProj (s : Set α) (x : s) : ↑x in ord
ConnectedComponent s (ordConnectedProj s x)
参数：s : Set α；x : s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ordConnectedComponent_comm`：mem_ordConnectedComponent_comm : y i
n ordConnectedComponent s x ↔ x in ordConnectedComponent s y
· 使用定理 `Set.ordConnectedProj_mem_ordConnectedComponent`：ordConnectedProj_mem_ord
ConnectedComponent (s : Set α) (x : s) : ordConnectedProj s x in ordConnectedCom
ponent s x
-/
theorem mem_ordConnectedComponent_ordConnectedProj (s : Set α) (x : s) :
    ↑x ∈ ordConnectedComponent s (ordConnectedProj s x) :=
  mem_ordConnectedComponent_comm.2 <| ordConnectedProj_mem_ordConnectedComponent s x

@[simp]
/-
**Set.ordConnectedComponent_ordConnectedProj** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnectedComponent_ordConnectedProj (s : Set α) (x : s) : ordConnectedC
omponent s (ordConnectedProj s x) = ordConnectedComponent s x
参数：s : Set α；x : s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ordConnectedComponent_eq`：ordConnectedComponent_eq (h : [[x, y]] sub
seteq s) : ordConnectedComponent s x = ordConnectedComponent s y
· 使用定理 `Set.mem_ordConnectedComponent_ordConnectedProj`：mem_ordConnectedComponen
t_ordConnectedProj (s : Set α) (x : s) : ↑x in ordConnectedComponent s (ordConne
ctedProj s x)
-/
theorem ordConnectedComponent_ordConnectedProj (s : Set α) (x : s) :
    ordConnectedComponent s (ordConnectedProj s x) = ordConnectedComponent s x :=
  ordConnectedComponent_eq <| mem_ordConnectedComponent_ordConnectedProj _ _

@[simp]
/-
**Set.ordConnectedProj_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnectedProj_eq {x y : s} : ordConnectedProj s x = ordConnectedProj s 
y ↔ [[(x : α), y]] subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_ordConnectedComponent`：mem_ordConnectedComponent : y in ordConne
ctedComponent s x ↔ [[x, y]] subseteq s
· 使用定理 `Set.ordConnectedComponent_ordConnectedProj`：ordConnectedComponent_ordCon
nectedProj (s : Set α) (x : s) : ordConnectedComponent s (ordConnectedProj s x) 
= ordConnectedComponent s x
· 使用定理 `Set.self_mem_ordConnectedComponent`：self_mem_ordConnectedComponent : x i
n ordConnectedComponent s x ↔ x in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ordConnectedComponent_eq`：ordConnectedComponent_eq (h : [[x, y]] sub
seteq s) : ordConnectedComponent s x = ordConnectedComponent s y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Nonempty.some.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s = 
s_1) (h : s.Nonempty), h.some = ⋯.some
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ordConnectedProj_eq {x y : s} :
    ordConnectedProj s x = ordConnectedProj s y ↔ [[(x : α), y]] ⊆ s := by
  constructor <;> intro h
  · rw [← mem_ordConnectedComponent, ← ordConnectedComponent_ordConnectedProj, h,
      ordConnectedComponent_ordConnectedProj, self_mem_ordConnectedComponent]
    exact y.2
  · simp only [ordConnectedProj, ordConnectedComponent_eq h]

/-- A set that intersects each order connected component of a set by a single point. Defined as the
range of `Set.ordConnectedProj s`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Set.ordConnectedSection** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：ordConnectedSection (s : Set α) : Set α
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def ordConnectedSection (s : Set α) : Set α :=
  range <| ordConnectedProj s
/-
**Set.dual_ordConnectedSection** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：dual_ordConnectedSection (s : Set α) : ordConnectedSection (ofDual ⁻¹' s) 
= ofDual ⁻¹' ordConnectedSection s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.dual_ordConnectedComponent`：dual_ordConnectedComponent : ordConnecte
dComponent (ofDual ⁻¹' s) (toDual x) = ofDual ⁻¹' ordConnectedComponent s x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Nonempty.some.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s = 
s_1) (h : s.Nonempty), h.some = ⋯.some
-/
theorem dual_ordConnectedSection (s : Set α) :
    ordConnectedSection (ofDual ⁻¹' s) = ofDual ⁻¹' ordConnectedSection s := by
  simp only [ordConnectedSection]
  simp +unfoldPartialApp only [ordConnectedProj]
  ext x
  simp only [mem_range, Subtype.exists, mem_preimage, OrderDual.exists, dual_ordConnectedComponent,
    ofDual_toDual]
  tauto
/-
**Set.ordConnectedSection_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordConnectedSection_subset : ordConnectedSection s subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Set.ordConnectedComponent_subset`：ordConnectedComponent_subset : ordConn
ectedComponent s x subseteq s
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
-/
theorem ordConnectedSection_subset : ordConnectedSection s ⊆ s :=
  range_subset_iff.2 fun _ => ordConnectedComponent_subset <| Nonempty.some_mem _
/-
**Set.eq_of_mem_ordConnectedSection_of_uIcc_subset** 是 Mathlib 中的一个定理，位于命名空间 `Se
t`。
形式化陈述：eq_of_mem_ordConnectedSection_of_uIcc_subset (hx : x in ordConnectedSectio
n s) (hy : y in ordConnectedSection s) (h : [[x, y]] subseteq s) : x = y
参数：hx : x in ordConnectedSection s；hy : y in ordConnectedSection s；h : [[x, y]] 
subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ordConnectedProj_eq`：ordConnectedProj_eq {x y : s} : ordConnectedPro
j s x = ordConnectedProj s y ↔ [[(x : α), y]] subseteq s
· 使用定理 `Set.mem_ordConnectedComponent_trans`：mem_ordConnectedComponent_trans (hx
y : y in ordConnectedComponent s x) (hyz : z in ordConnectedComponent s y) : z i
n ordConnectedComponent s…
· 使用定理 `Set.ordConnectedProj_mem_ordConnectedComponent`：ordConnectedProj_mem_ord
ConnectedComponent (s : Set α) (x : s) : ordConnectedProj s x in ordConnectedCom
ponent s x
· 使用定理 `Set.mem_ordConnectedComponent_ordConnectedProj`：mem_ordConnectedComponen
t_ordConnectedProj (s : Set α) (x : s) : ↑x in ordConnectedComponent s (ordConne
ctedProj s x)
-/
theorem eq_of_mem_ordConnectedSection_of_uIcc_subset (hx : x ∈ ordConnectedSection s)
    (hy : y ∈ ordConnectedSection s) (h : [[x, y]] ⊆ s) : x = y := by
  rcases hx with ⟨x, rfl⟩; rcases hy with ⟨y, rfl⟩
  exact
    ordConnectedProj_eq.2
      (mem_ordConnectedComponent_trans
        (mem_ordConnectedComponent_trans (ordConnectedProj_mem_ordConnectedComponent _ _) h)
        (mem_ordConnectedComponent_ordConnectedProj _ _))

/-- Given two sets `s t : Set α`, the set `Set.orderSeparatingSet s t` is the set of points that
belong both to some `Set.ordConnectedComponent tᶜ x`, `x ∈ s`, and to some
`Set.ordConnectedComponent sᶜ x`, `x ∈ t`. In the case of two disjoint closed sets, this is the
union of all open intervals $(a, b)$ such that their endpoints belong to different sets. -/
/-
**Set.ordSeparatingSet** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：ordSeparatingSet (s t : Set α) : Set α
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two sets `s t : Set α`, the set `Set.orderSeparatingSet s t` is the set of
 points that
belong both to some `Set.ordConnectedComponent tᶜ x`, `x ∈ s`, and to some
`Set.ordConnectedComponent sᶜ x`, `x ∈ t`. In the case of two disjoint closed se
ts, this is the
union of all open intervals $(a, b)$ such that their endpoints belong to differe
nt sets.
-/
def ordSeparatingSet (s t : Set α) : Set α :=
  (⋃ x ∈ s, ordConnectedComponent tᶜ x) ∩ ⋃ x ∈ t, ordConnectedComponent sᶜ x
/-
**Set.ordSeparatingSet_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：ordSeparatingSet_comm (s t : Set α) : ordSeparatingSet s t = ordSeparating
Set t s
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem ordSeparatingSet_comm (s t : Set α) : ordSeparatingSet s t = ordSeparatingSet t s :=
  inter_comm _ _
/-
**Set.disjoint_left_ordSeparatingSet** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_left_ordSeparatingSet : Disjoint s (ordSeparatingSet s t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.inter_right'`：inter_right' (u : Set α) (h : Disjoint s t) : Dis
joint s (u inter t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iUnion₂_right`：disjoint_iUnion₂_right {s : Set α} {t : fora
ll i, κ i -> Set α} : Disjoint s (⋃ (i) (j), t i j) ↔ forall i j, Disjoint s (t 
i j)
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Set.ordConnectedComponent_subset`：ordConnectedComponent_subset : ordConn
ectedComponent s x subseteq s
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
-/
theorem disjoint_left_ordSeparatingSet : Disjoint s (ordSeparatingSet s t) :=
  Disjoint.inter_right' _ <|
    disjoint_iUnion₂_right.2 fun _ _ =>
      disjoint_compl_right.mono_right <| ordConnectedComponent_subset
/-
**Set.disjoint_right_ordSeparatingSet** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_right_ordSeparatingSet : Disjoint t (ordSeparatingSet s t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.disjoint_left_ordSeparatingSet`：disjoint_left_ordSeparatingSet : Dis
joint s (ordSeparatingSet s t)
· 使用定理 `Set.ordSeparatingSet_comm`：ordSeparatingSet_comm (s t : Set α) : ordSepa
ratingSet s t = ordSeparatingSet t s
-/
theorem disjoint_right_ordSeparatingSet : Disjoint t (ordSeparatingSet s t) :=
  ordSeparatingSet_comm t s ▸ disjoint_left_ordSeparatingSet
/-
**Set.dual_ordSeparatingSet** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：dual_ordSeparatingSet : ordSeparatingSet (ofDual ⁻¹' s) (ofDual ⁻¹' t) = o
fDual ⁻¹' ordSeparatingSet s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.iUnion_comp`：iUnion_comp {f : ι -> ι₂} (hf : Surject
ive f) (g : ι₂ -> Set α) : ⋃ x, g (f x) = ⋃ y, g y
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Set.dual_ordConnectedComponent`：dual_ordConnectedComponent : ordConnecte
dComponent (ofDual ⁻¹' s) (toDual x) = ofDual ⁻¹' ordConnectedComponent s x
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dual_ordSeparatingSet :
    ordSeparatingSet (ofDual ⁻¹' s) (ofDual ⁻¹' t) = ofDual ⁻¹' ordSeparatingSet s t := by
  simp only [ordSeparatingSet, mem_preimage, ← toDual.surjective.iUnion_comp, ofDual_toDual,
    dual_ordConnectedComponent, ← preimage_compl, preimage_inter, preimage_iUnion]

/-- An auxiliary neighborhood that will be used in the proof of
`OrderTopology.CompletelyNormalSpace`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Set.ordT5Nhd** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：ordT5Nhd (s t : Set α) : Set α
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def ordT5Nhd (s t : Set α) : Set α :=
  ⋃ x ∈ s, ordConnectedComponent (tᶜ ∩ (ordConnectedSection <| ordSeparatingSet s t)ᶜ) x
/-
**Set.disjoint_ordT5Nhd** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：disjoint_ordT5Nhd : Disjoint (ordT5Nhd s t) (ordT5Nhd t s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `Set.uIcc_subset_uIcc_union_uIcc`：uIcc_subset_uIcc_union_uIcc : [[a, c]] 
subseteq [[a, b]] union [[b, c]]
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
· 使用定理 `Set.ordSeparatingSet_comm`：ordSeparatingSet_comm (s t : Set α) : ordSepa
ratingSet s t = ordSeparatingSet t s
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用引理 `Set.Icc_subset_uIcc'`：Icc_subset_uIcc' : Icc b a subseteq [[a, b]]
· 使用引理 `Set.Icc_subset_uIcc`：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Set.disjoint_left_ordSeparatingSet`：disjoint_left_ordSeparatingSet : Dis
joint s (ordSeparatingSet s t)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.disjoint_right_ordSeparatingSet`：disjoint_right_ordSeparatingSet : D
isjoint t (ordSeparatingSet s t)
· 使用定理 `Set.ordConnectedProj_mem_ordConnectedComponent`：ordConnectedProj_mem_ord
ConnectedComponent (s : Set α) (x : s) : ordConnectedProj s x in ordConnectedCom
ponent s x
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.subset_inter_iff`：subset_inter_iff {s t r : Set α} : r subseteq s in
ter t ↔ r subseteq s ∧ r subseteq t
· 使用定理 `Set.mem_ordConnectedComponent`：mem_ordConnectedComponent : y in ordConne
ctedComponent s x ↔ [[x, y]] subseteq s
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem disjoint_ordT5Nhd : Disjoint (ordT5Nhd s t) (ordT5Nhd t s) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hx₁, hx₂⟩
  rcases mem_iUnion₂.1 hx₁ with ⟨a, has, ha⟩
  clear hx₁
  rcases mem_iUnion₂.1 hx₂ with ⟨b, hbt, hb⟩
  clear hx₂
  rw [mem_ordConnectedComponent, subset_inter_iff] at ha hb
  wlog hab : a ≤ b with H
  · exact H b hbt hb a has ha (le_of_not_ge hab)
  obtain ⟨ha, ha'⟩ := ha
  obtain ⟨hb, hb'⟩ := hb
  have hsub : [[a, b]] ⊆ (ordSeparatingSet s t).ordConnectedSectionᶜ := by
    rw [ordSeparatingSet_comm, uIcc_comm] at hb'
    calc
      [[a, b]] ⊆ [[a, x]] ∪ [[x, b]] := uIcc_subset_uIcc_union_uIcc
      _ ⊆ (ordSeparatingSet s t).ordConnectedSectionᶜ := union_subset ha' hb'
  clear ha' hb'
  rcases le_total x a with hxa | hax
  · exact hb (Icc_subset_uIcc' ⟨hxa, hab⟩) has
  rcases le_total b x with hbx | hxb
  · exact ha (Icc_subset_uIcc ⟨hab, hbx⟩) hbt
  have h' : x ∈ ordSeparatingSet s t := ⟨mem_iUnion₂.2 ⟨a, has, ha⟩, mem_iUnion₂.2 ⟨b, hbt, hb⟩⟩
  lift x to ordSeparatingSet s t using h'
  suffices ordConnectedComponent (ordSeparatingSet s t) x ⊆ [[a, b]] from
    hsub (this <| ordConnectedProj_mem_ordConnectedComponent _ x) (mem_range_self _)
  rintro y hy
  rw [uIcc_of_le hab, mem_Icc, ← not_lt, ← not_lt]
  have sol1 := fun (hya : y < a) =>
      (disjoint_left (t := ordSeparatingSet s t)).1 disjoint_left_ordSeparatingSet has
        (hy <| Icc_subset_uIcc' ⟨hya.le, hax⟩)
  have sol2 := fun (hby : b < y) =>
      (disjoint_left (t := ordSeparatingSet s t)).1 disjoint_right_ordSeparatingSet hbt
        (hy <| Icc_subset_uIcc ⟨hxb, hby.le⟩)
  exact ⟨sol1, sol2⟩

end Set

