/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Coset.Basic

/-!
# Double cosets

This file defines double cosets for two subgroups `H K` of a group `G` and the quotient of `G` by
the double coset relation, i.e. `H \ G / K`. We also prove that `G` can be written as a disjoint
union of the double cosets and that if one of `H` or `K` is the trivial group (i.e. `⊥` ) then
this is the usual left or right quotient of a group by a subgroup.

## Main definitions

* `setoid`: The double coset relation defined by two subgroups `H K` of `G`.
* `DoubleCoset.quotient`: The quotient of `G` by the double coset relation, i.e, `H \ G / K`.
-/

@[expose] public section

assert_not_exists MonoidWithZero

variable {G : Type*} [Group G] {α : Type*} [Mul α]

open MulOpposite
open scoped Pointwise

namespace DoubleCoset

/-- The double coset as an element of `Set α` corresponding to `s a t` -/
/-
**DoubleCoset.doubleCoset** 是 Mathlib 中的一个定义，位于命名空间 `DoubleCoset`。
形式化陈述：doubleCoset (a : α) (s t : Set α) : Set α
参数：a : α；s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The double coset as an element of `Set α` corresponding to `s a t`
-/
def doubleCoset (a : α) (s t : Set α) : Set α :=
  s * {a} * t
/-
**DoubleCoset.doubleCoset_eq_image2** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：doubleCoset_eq_image2 (a : α) (s t : Set α) : doubleCoset a s t = Set.imag
e2 (· * a * ·) s t
参数：a : α；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mul_singleton`：mul_singleton : s * {b} = (· * b) '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma doubleCoset_eq_image2 (a : α) (s t : Set α) :
    doubleCoset a s t = Set.image2 (· * a * ·) s t := by
  simp_rw [doubleCoset, Set.mul_singleton, ← Set.image2_mul, Set.image2_image_left]
/-
**DoubleCoset.mem_doubleCoset** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：mem_doubleCoset {s t : Set α} {a b : α} : b in doubleCoset a s t ↔ exists 
x in s, exists y in t, b = x * a * y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DoubleCoset.doubleCoset_eq_image2`：doubleCoset_eq_image2 (a : α) (s t : 
Set α) : doubleCoset a s t = Set.image2 (· * a * ·) s t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_doubleCoset {s t : Set α} {a b : α} :
    b ∈ doubleCoset a s t ↔ ∃ x ∈ s, ∃ y ∈ t, b = x * a * y := by
  simp only [doubleCoset_eq_image2, Set.mem_image2, eq_comm]
/-
**DoubleCoset.mem_doubleCoset_self** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：mem_doubleCoset_self (H K : Subgroup G) (a : G) : a in doubleCoset a H K
参数：H K : Subgroup G；a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DoubleCoset.mem_doubleCoset`：mem_doubleCoset {s t : Set α} {a b : α} : b
 in doubleCoset a s t ↔ exists x in s, exists y in t, b = x * a * y
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma mem_doubleCoset_self (H K : Subgroup G) (a : G) : a ∈ doubleCoset a H K :=
  mem_doubleCoset.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mul a).symm.trans (mul_one (1 * a)).symm⟩
/-
**DoubleCoset.doubleCoset_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：doubleCoset_eq_of_mem {H K : Subgroup G} {a b : G} (hb : b in doubleCoset 
a H K) : doubleCoset b H K = doubleCoset a H K
参数：hb : b in doubleCoset a H K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `DoubleCoset.mem_doubleCoset`：mem_doubleCoset {s t : Set α} {a b : α} : b
 in doubleCoset a s t ↔ exists x in s, exists y in t, b = x * a * y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DoubleCoset.doubleCoset.eq_1`：∀ {α : Type u_2} [inst : Mul α] (a : α) (s
 t : Set α), DoubleCoset.doubleCoset a s t = s * {a} * t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_mul_singleton`：singleton_mul_singleton : ({a} : Set α) * {
b} = {a * b}
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Subgroup.singleton_mul_subgroup`：singleton_mul_subgroup {H : Subgroup G}
 {h : G} (hh : h in H) : {h} * (H : Set G) = H
· 使用定理 `Subgroup.subgroup_mul_singleton`：subgroup_mul_singleton {H : Subgroup G}
 {h : G} (hh : h in H) : (H : Set G) * {h} = H
-/
lemma doubleCoset_eq_of_mem {H K : Subgroup G} {a b : G} (hb : b ∈ doubleCoset a H K) :
    doubleCoset b H K = doubleCoset a H K := by
  obtain ⟨h, hh, k, hk, rfl⟩ := mem_doubleCoset.1 hb
  rw [doubleCoset, doubleCoset, ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton,
    mul_assoc, mul_assoc, Subgroup.singleton_mul_subgroup hk, ← mul_assoc, ← mul_assoc,
    Subgroup.subgroup_mul_singleton hh]
/-
**DoubleCoset.mem_doubleCoset_of_not_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `DoubleC
oset`。
形式化陈述：mem_doubleCoset_of_not_disjoint {H K : Subgroup G} {a b : G} (h : ¬Disjoin
t (doubleCoset a H K) (doubleCoset b H K)) : b in doubleCoset a H K
参数：h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
-/
lemma mem_doubleCoset_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) : b ∈ doubleCoset a H K := by
  rw [Set.not_disjoint_iff] at h
  simp only [mem_doubleCoset] at *
  obtain ⟨x, ⟨l, hl, r, hr, hrx⟩, y, hy, ⟨r', hr', rfl⟩⟩ := h
  refine ⟨y⁻¹ * l, H.mul_mem (H.inv_mem hy) hl, r * r'⁻¹, K.mul_mem hr (K.inv_mem hr'), ?_⟩
  rwa [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, eq_mul_inv_iff_mul_eq]
/-
**DoubleCoset.eq_of_not_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：eq_of_not_disjoint {H K : Subgroup G} {a b : G} (h : ¬Disjoint (doubleCose
t a H K) (doubleCoset b H K)) : doubleCoset a H K = doubleCoset b H K
参数：h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DoubleCoset.mem_doubleCoset_of_not_disjoint`：mem_doubleCoset_of_not_disj
oint {H K : Subgroup G} {a b : G} (h : ¬Disjoint (doubleCoset a H K) (doubleCose
t b H K)) : b in doubleCoset a H …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用引理 `DoubleCoset.doubleCoset_eq_of_mem`：doubleCoset_eq_of_mem {H K : Subgroup
 G} {a b : G} (hb : b in doubleCoset a H K) : doubleCoset b H K = doubleCoset a 
H K
-/
lemma eq_of_not_disjoint {H K : Subgroup G} {a b : G}
    (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) :
    doubleCoset a H K = doubleCoset b H K := by
  rw [disjoint_comm] at h
  have ha : a ∈ doubleCoset b H K := mem_doubleCoset_of_not_disjoint h
  apply doubleCoset_eq_of_mem ha

/-- The setoid defined by the `doubleCoset` relation -/
@[instance_reducible]
/-
**DoubleCoset.setoid** 是 Mathlib 中的一个定义，位于命名空间 `DoubleCoset`。
形式化陈述：setoid (H K : Set G) : Setoid G
参数：H K : Set G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid defined by the `doubleCoset` relation
-/
def setoid (H K : Set G) : Setoid G :=
  Setoid.ker fun x => doubleCoset x H K

/-- Quotient of `G` by the double coset relation, i.e. `H \ G / K` -/
/-
**DoubleCoset.Quotient** 是 Mathlib 中的一个定义，位于命名空间 `DoubleCoset`。
形式化陈述：Quotient (H K : Set G) : Type _
参数：H K : Set G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quotient of `G` by the double coset relation, i.e. `H \ G / K`
-/
def Quotient (H K : Set G) : Type _ :=
  _root_.Quotient (setoid H K)
/-
**DoubleCoset.rel_iff** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：rel_iff {H K : Subgroup G} {x y : G} : setoid ↑H ↑K x y ↔ exists a in H, e
xists b in K, y = a * x * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `DoubleCoset.mem_doubleCoset_self`：mem_doubleCoset_self (H K : Subgroup G
) (a : G) : a in doubleCoset a H K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DoubleCoset.doubleCoset_eq_of_mem`：doubleCoset_eq_of_mem {H K : Subgroup
 G} {a b : G} (hb : b in doubleCoset a H K) : doubleCoset b H K = doubleCoset a 
H K
· 使用引理 `DoubleCoset.mem_doubleCoset`：mem_doubleCoset {s t : Set α} {a b : α} : b
 in doubleCoset a s t ↔ exists x in s, exists y in t, b = x * a * y
-/
lemma rel_iff {H K : Subgroup G} {x y : G} :
    setoid ↑H ↑K x y ↔ ∃ a ∈ H, ∃ b ∈ K, y = a * x * b :=
  Iff.trans
    ⟨fun (hxy : doubleCoset x H K = doubleCoset y H K) => hxy ▸ mem_doubleCoset_self H K y,
      fun hxy => (doubleCoset_eq_of_mem hxy).symm⟩ mem_doubleCoset
/-
**DoubleCoset.bot_rel_eq_leftRel** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：bot_rel_eq_leftRel (H : Subgroup G) : ⇑(setoid ↑(⊥ : Subgroup G) ↑H) = ⇑(Q
uotientGroup.leftRel H)
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DoubleCoset.rel_iff`：rel_iff {H K : Subgroup G} {x y : G} : setoid ↑H ↑K
 x y ↔ exists a in H, exists b in K, y = a * x * b
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
lemma bot_rel_eq_leftRel (H : Subgroup G) :
    ⇑(setoid ↑(⊥ : Subgroup G) ↑H) = ⇑(QuotientGroup.leftRel H) := by
  ext a b
  rw [rel_iff, QuotientGroup.leftRel_apply]
  constructor
  · rintro ⟨a, rfl : a = 1, b, hb, rfl⟩
    rwa [one_mul, inv_mul_cancel_left]
  · rintro (h : a⁻¹ * b ∈ H)
    exact ⟨1, rfl, a⁻¹ * b, h, by rw [one_mul, mul_inv_cancel_left]⟩
/-
**DoubleCoset.rel_bot_eq_right_group_rel** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`
。
形式化陈述：rel_bot_eq_right_group_rel (H : Subgroup G) : ⇑(setoid ↑H ↑(⊥ : Subgroup G
)) = ⇑(QuotientGroup.rightRel H)
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DoubleCoset.rel_iff`：rel_iff {H K : Subgroup G} {x y : G} : setoid ↑H ↑K
 x y ↔ exists a in H, exists b in K, y = a * x * b
· 使用定理 `QuotientGroup.rightRel_apply`：rightRel_apply {x y : α} : rightRel s x y 
↔ y * x⁻¹ in s
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
lemma rel_bot_eq_right_group_rel (H : Subgroup G) :
    ⇑(setoid ↑H ↑(⊥ : Subgroup G)) = ⇑(QuotientGroup.rightRel H) := by
  ext a b
  rw [rel_iff, QuotientGroup.rightRel_apply]
  constructor
  · rintro ⟨b, hb, a, rfl : a = 1, rfl⟩
    rwa [mul_one, mul_inv_cancel_right]
  · rintro (h : b * a⁻¹ ∈ H)
    exact ⟨b * a⁻¹, h, 1, rfl, by rw [mul_one, inv_mul_cancel_right]⟩

/-- Create a double coset out of an element of `H \ G / K` -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**DoubleCoset.quotToDoubleCoset** 是 Mathlib 中的一个定义，位于命名空间 `DoubleCoset`。
形式化陈述：quotToDoubleCoset (H K : Subgroup G) (q : Quotient (H : Set G) K) : Set G
参数：H K : Subgroup G；q : Quotient (H : Set G) K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def quotToDoubleCoset (H K : Subgroup G) (q : Quotient (H : Set G) K) : Set G :=
  doubleCoset q.out H K

/-- Map from `G` to `H \ G / K` -/
/-
**DoubleCoset.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `DoubleCoset`。
形式化陈述：mk (H K : Subgroup G) (a : G) : Quotient (H : Set G) K
参数：H K : Subgroup G；a : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Map from `G` to `H \ G / K`
-/
abbrev mk (H K : Subgroup G) (a : G) : Quotient (H : Set G) K :=
  Quotient.mk'' a
/-
**DoubleCoset.** 是 Mathlib 中的一个实例，位于命名空间 `DoubleCoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (H K : Subgroup G) : Inhabited (Quotient (H : Set G) K) :=
  ⟨mk H K (1 : G)⟩
/-
**DoubleCoset.eq''** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：eq'' {a b : G} (H K : Subgroup G) : mk H K a = mk H K b ↔ setoid H K a b
参数：H K : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
-/
lemma eq'' {a b : G} (H K : Subgroup G) : mk H K a = mk H K b ↔ setoid H K a b :=
  Quotient.eq
/-
**DoubleCoset.eq** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：eq (H K : Subgroup G) (a b : G) : mk H K a = mk H K b ↔ exists h in H, exi
sts k in K, b = h * a * k
参数：H K : Subgroup G；a b : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DoubleCoset.eq''`：eq'' {a b : G} (H K : Subgroup G) : mk H K a = mk H K 
b ↔ setoid H K a b
· 使用引理 `DoubleCoset.rel_iff`：rel_iff {H K : Subgroup G} {x y : G} : setoid ↑H ↑K
 x y ↔ exists a in H, exists b in K, y = a * x * b
-/
lemma eq (H K : Subgroup G) (a b : G) :
    mk H K a = mk H K b ↔ ∃ h ∈ H, ∃ k ∈ K, b = h * a * k := by
  rw [eq'']
  exact rel_iff
/-
**DoubleCoset.out_eq'** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：out_eq' (H K : Subgroup G) (q : Quotient ↑H ↑K) : mk H K q.out = q
参数：H K : Subgroup G；q : Quotient ↑H ↑K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
-/
lemma out_eq' (H K : Subgroup G) (q : Quotient ↑H ↑K) : mk H K q.out = q :=
  Quotient.out_eq' q
/-
**DoubleCoset.mk_out_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：mk_out_eq_mul (H K : Subgroup G) (g : G) : exists h k : G, h in H ∧ k in K
 ∧ (mk H K g : Quotient ↑H ↑K).out = h * g * k
参数：H K : Subgroup G；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DoubleCoset.eq`：eq (H K : Subgroup G) (a b : G) : mk H K a = mk H K b ↔ 
exists h in H, exists k in K, b = h * a * k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DoubleCoset.out_eq'`：out_eq' (H K : Subgroup G) (q : Quotient ↑H ↑K) : m
k H K q.out = q
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `eq_mul_inv_of_mul_eq`：eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹
· 使用定理 `eq_inv_mul_of_mul_eq`：eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma mk_out_eq_mul (H K : Subgroup G) (g : G) :
    ∃ h k : G, h ∈ H ∧ k ∈ K ∧ (mk H K g : Quotient ↑H ↑K).out = h * g * k := by
  have := eq H K (mk H K g : Quotient ↑H ↑K).out g
  rw [out_eq'] at this
  obtain ⟨h, h_h, k, hk, T⟩ := this.1 rfl
  refine ⟨h⁻¹, k⁻¹, H.inv_mem h_h, K.inv_mem hk, eq_mul_inv_of_mul_eq (eq_inv_mul_of_mul_eq ?_)⟩
  rw [← mul_assoc, ← T]
/-
**DoubleCoset.mk_eq_of_doubleCoset_eq** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：mk_eq_of_doubleCoset_eq {H K : Subgroup G} {a b : G} (h : doubleCoset a H 
K = doubleCoset b H K) : mk H K a = mk H K b
参数：h : doubleCoset a H K = doubleCoset b H K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DoubleCoset.eq`：eq (H K : Subgroup G) (a b : G) : mk H K a = mk H K b ↔ 
exists h in H, exists k in K, b = h * a * k
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `DoubleCoset.mem_doubleCoset`：mem_doubleCoset {s t : Set α} {a b : α} : b
 in doubleCoset a s t ↔ exists x in s, exists y in t, b = x * a * y
· 使用引理 `DoubleCoset.mem_doubleCoset_self`：mem_doubleCoset_self (H K : Subgroup G
) (a : G) : a in doubleCoset a H K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mk_eq_of_doubleCoset_eq {H K : Subgroup G} {a b : G}
    (h : doubleCoset a H K = doubleCoset b H K) : mk H K a = mk H K b := by
  rw [eq]
  exact mem_doubleCoset.mp (h.symm ▸ mem_doubleCoset_self H K b)

set_option backward.isDefEq.respectTransparency false in
/-
**DoubleCoset.mem_quotToDoubleCoset_iff** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：mem_quotToDoubleCoset_iff {H K : Subgroup G} (i : Quotient (H : Set G) K) 
(a : G) : a in quotToDoubleCoset H K i ↔ mk H K a = i
参数：i : Quotient (H : Set G) K；a : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DoubleCoset.mk_eq_of_doubleCoset_eq`：mk_eq_of_doubleCoset_eq {H K : Subg
roup G} {a b : G} (h : doubleCoset a H K = doubleCoset b H K) : mk H K a = mk H 
K b
· 使用引理 `DoubleCoset.doubleCoset_eq_of_mem`：doubleCoset_eq_of_mem {H K : Subgroup
 G} {a b : G} (hb : b in doubleCoset a H K) : doubleCoset b H K = doubleCoset a 
H K
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DoubleCoset.mem_doubleCoset`：mem_doubleCoset {s t : Set α} {a b : α} : b
 in doubleCoset a s t ↔ exists x in s, exists y in t, b = x * a * y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `DoubleCoset.eq`：eq (H K : Subgroup G) (a b : G) : mk H K a = mk H K b ↔ 
exists h in H, exists k in K, b = h * a * k
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DoubleCoset.out_eq'`：out_eq' (H K : Subgroup G) (q : Quotient ↑H ↑K) : m
k H K q.out = q
-/
lemma mem_quotToDoubleCoset_iff {H K : Subgroup G} (i : Quotient (H : Set G) K) (a : G) :
    a ∈ quotToDoubleCoset H K i ↔ mk H K a = i := by
  refine ⟨fun hg ↦ by simp [mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hg)], fun hg ↦ ?_⟩
  rw [← out_eq' _ _ i] at hg
  exact mem_doubleCoset.mpr ((eq _ _ _ a).mp hg.symm)
/-
**DoubleCoset.disjoint_out** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：disjoint_out {H K : Subgroup G} {a b : Quotient H K} : a != b -> Disjoint 
(doubleCoset a.out H K) (doubleCoset b.out (H : Set G) K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DoubleCoset.out_eq'`：out_eq' (H K : Subgroup G) (q : Quotient ↑H ↑K) : m
k H K q.out = q
· 使用引理 `DoubleCoset.mk_eq_of_doubleCoset_eq`：mk_eq_of_doubleCoset_eq {H K : Subg
roup G} {a b : G} (h : doubleCoset a H K = doubleCoset b H K) : mk H K a = mk H 
K b
· 使用引理 `DoubleCoset.eq_of_not_disjoint`：eq_of_not_disjoint {H K : Subgroup G} {a
 b : G} (h : ¬Disjoint (doubleCoset a H K) (doubleCoset b H K)) : doubleCoset a 
H K = doubleCoset b …
-/
lemma disjoint_out {H K : Subgroup G} {a b : Quotient H K} :
    a ≠ b → Disjoint (doubleCoset a.out H K) (doubleCoset b.out (H : Set G) K) := by
  contrapose
  intro h
  simpa [out_eq'] using mk_eq_of_doubleCoset_eq (eq_of_not_disjoint h)
/-
**DoubleCoset.iUnion_quotToDoubleCoset** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：iUnion_quotToDoubleCoset (H K : Subgroup G) : ⋃ q, quotToDoubleCoset H K q
 = Set.univ
参数：H K : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `DoubleCoset.mk_out_eq_mul`：mk_out_eq_mul (H K : Subgroup G) (g : G) : ex
ists h k : G, h in H ∧ k in K ∧ (mk H K g : Quotient ↑H ↑K).out = h * g * k
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iUnion_quotToDoubleCoset (H K : Subgroup G) : ⋃ q, quotToDoubleCoset H K q = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, quotToDoubleCoset, mem_doubleCoset, SetLike.mem_coe, Set.mem_univ,
    iff_true]
  use mk H K x
  obtain ⟨h, k, h3, h4, h5⟩ := mk_out_eq_mul H K x
  refine ⟨h⁻¹, H.inv_mem h3, k⁻¹, K.inv_mem h4, ?_⟩
  simp only [h5, ← mul_assoc, one_mul, inv_mul_cancel, mul_inv_cancel_right]

@[deprecated (since := "2026-04-03")]
alias union_quotToDoubleCoset := iUnion_quotToDoubleCoset
/-
**DoubleCoset.doubleCoset_union_rightCoset** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCose
t`。
形式化陈述：doubleCoset_union_rightCoset (H K : Subgroup G) (a : G) : ⋃ k : K, op (a *
 k) • ↑H = doubleCoset a H K
参数：H K : Subgroup G；a : G。
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
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma doubleCoset_union_rightCoset (H K : Subgroup G) (a : G) :
    ⋃ k : K, op (a * k) • ↑H = doubleCoset a H K := by
  ext x
  simp only [mem_rightCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset,
    SetLike.mem_coe]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨x * (y⁻¹ * a⁻¹), h_h, y, y.2, ?_⟩
    simp only [← mul_assoc, inv_mul_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    simp only [hxy, ← mul_assoc, hx, mul_inv_cancel_right]
/-
**DoubleCoset.doubleCoset_union_leftCoset** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset
`。
形式化陈述：doubleCoset_union_leftCoset (H K : Subgroup G) (a : G) : ⋃ h : H, (h * a :
 G) • ↑K = doubleCoset a H K
参数：H K : Subgroup G；a : G。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma doubleCoset_union_leftCoset (H K : Subgroup G) (a : G) :
    ⋃ h : H, (h * a : G) • ↑K = doubleCoset a H K := by
  ext x
  simp only [mem_leftCoset_iff, mul_inv_rev, Set.mem_iUnion, mem_doubleCoset]
  constructor
  · rintro ⟨y, h_h⟩
    refine ⟨y, y.2, a⁻¹ * y⁻¹ * x, h_h, ?_⟩
    simp only [← mul_assoc, one_mul, mul_inv_cancel, mul_inv_cancel_right, InvMemClass.coe_inv]
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [hxy, ← mul_assoc, hy, one_mul, inv_mul_cancel, inv_mul_cancel_right]

open Quotient QuotientGroup
/-
**DoubleCoset.left_bot_eq_left_quot** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：left_bot_eq_left_quot (H : Subgroup G) : Quotient (⊥ : Subgroup G) (H : Se
t G) = (G ⧸ H)
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DoubleCoset.bot_rel_eq_leftRel`：bot_rel_eq_leftRel (H : Subgroup G) : ⇑(
setoid ↑(⊥ : Subgroup G) ↑H) = ⇑(QuotientGroup.leftRel H)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma left_bot_eq_left_quot (H : Subgroup G) :
    Quotient (⊥ : Subgroup G) (H : Set G) = (G ⧸ H) := by
  unfold Quotient
  congr
  ext
  simp_rw [← bot_rel_eq_leftRel H]
/-
**DoubleCoset.right_bot_eq_right_quot** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：right_bot_eq_right_quot (H : Subgroup G) : Quotient (H : Set G) (⊥ : Subgr
oup G) = _root_.Quotient (rightRel H)
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DoubleCoset.rel_bot_eq_right_group_rel`：rel_bot_eq_right_group_rel (H : 
Subgroup G) : ⇑(setoid ↑H ↑(⊥ : Subgroup G)) = ⇑(QuotientGroup.rightRel H)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma right_bot_eq_right_quot (H : Subgroup G) :
    Quotient (H : Set G) (⊥ : Subgroup G) = _root_.Quotient (rightRel H) := by
  unfold Quotient
  congr
  ext
  simp_rw [← rel_bot_eq_right_group_rel H]
/-
**DoubleCoset.finite_quotient_iff_exists_finset_iUnion_eq_univ** 是 Mathlib 中的一个引
理，位于命名空间 `DoubleCoset`。
形式化陈述：finite_quotient_iff_exists_finset_iUnion_eq_univ (H K : Subgroup G) : Fini
te (Quotient (H : Set G) K) ↔ exists I : Finset (Quotient (H : Set G) K), ⋃ i in
 I, quotToDoubleCoset H K i = .univ
参数：H K : Subgroup G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用引理 `DoubleCoset.iUnion_quotToDoubleCoset`：iUnion_quotToDoubleCoset (H K : Su
bgroup G) : ⋃ q, quotToDoubleCoset H K q = Set.univ
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `DoubleCoset.mem_quotToDoubleCoset_iff`：mem_quotToDoubleCoset_iff {H K : 
Subgroup G} (i : Quotient (H : Set G) K) (a : G) : a in quotToDoubleCoset H K i 
↔ mk H K a = i
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
lemma finite_quotient_iff_exists_finset_iUnion_eq_univ (H K : Subgroup G) :
    Finite (Quotient (H : Set G) K) ↔
    ∃ I : Finset (Quotient (H : Set G) K), ⋃ i ∈ I, quotToDoubleCoset H K i = .univ := by
  constructor
  · intro _
    cases nonempty_fintype (Quotient (H : Set G) K)
    exact ⟨Finset.univ, by simpa using! iUnion_quotToDoubleCoset _ _⟩
  · rintro ⟨I, hI⟩
    suffices (I : Set (Quotient (H : Set G) K)) = Set.univ by
      simp_rw [← Set.finite_univ_iff, ← this, I.finite_toSet]
    rw [Set.eq_univ_iff_forall] at hI ⊢
    rintro ⟨g⟩
    obtain ⟨_, ⟨i, _, rfl⟩, T, ⟨hi, rfl⟩, hT : g ∈ quotToDoubleCoset H K i⟩ := hI g
    simpa [← (mem_quotToDoubleCoset_iff _ _).mp hT] using! hi
/-
**DoubleCoset.iUnion_image_mk_leftRel** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：iUnion_image_mk_leftRel {H K : Subgroup G} : ⋃ q : Quotient H K, Quot.mk (
leftRel K) '' doubleCoset (out q : G) H K = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DoubleCoset.iUnion_quotToDoubleCoset`：iUnion_quotToDoubleCoset (H K : Su
bgroup G) : ⋃ q, quotToDoubleCoset H K q = Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ne_univ_iff_exists_notMem`：ne_univ_iff_exists_notMem {α : Type*} (s 
: Set α) : s != univ ↔ exists a, a ∉ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma iUnion_image_mk_leftRel {H K : Subgroup G} :
    ⋃ q : Quotient H K, Quot.mk (leftRel K) '' doubleCoset (out q : G) H K = Set.univ := by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : ∃ i : Quotient H K, y ∈ doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exact ⟨i, y, hi, hy⟩
/-
**DoubleCoset.iUnion_image_mk_rightRel** 是 Mathlib 中的一个引理，位于命名空间 `DoubleCoset`。
形式化陈述：iUnion_image_mk_rightRel {H K : Subgroup G} : ⋃ q : Quotient H K, Quot.mk 
(rightRel H) '' doubleCoset (out q : G) H K = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DoubleCoset.iUnion_quotToDoubleCoset`：iUnion_quotToDoubleCoset (H K : Su
bgroup G) : ⋃ q, quotToDoubleCoset H K q = Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ne_univ_iff_exists_notMem`：ne_univ_iff_exists_notMem {α : Type*} (s 
: Set α) : s != univ ↔ exists a, a ∉ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma iUnion_image_mk_rightRel {H K : Subgroup G} :
    ⋃ q : Quotient H K, Quot.mk (rightRel H) '' doubleCoset (out q : G) H K = Set.univ := by
  have cover := iUnion_quotToDoubleCoset H K
  rw [Set.iUnion_eq_univ_iff]
  intro x
  obtain ⟨y, hy⟩ := exists_rep x
  have ⟨i, hi⟩ : ∃ i : Quotient H K, y ∈ doubleCoset (out i) H K := by
    contrapose cover
    exact (Set.ne_univ_iff_exists_notMem _).mpr ⟨y, by simpa using! cover⟩
  exact ⟨i, y, hi, hy⟩
/-
**DoubleCoset.iUnion_finset_leftRel_eq_univ_of_leftRel** 是 Mathlib 中的一个引理，位于命名空间
 `DoubleCoset`。
形式化陈述：iUnion_finset_leftRel_eq_univ_of_leftRel {H K : Subgroup G} {t : Finset (Q
uotient H K)} (ht : Set.univ subseteq ⋃ i in t, Quot.mk (leftRel K) '' doubleCos
et (out i) H K) : ⋃ q in t, doubleCoset (out q) H K = Set.univ
参数：Quotient H K；ht : Set.univ subseteq ⋃ i in t, Quot.mk (leftRel K) '' doubleCo
set (out i) H K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ne_univ_iff_exists_notMem`：ne_univ_iff_exists_notMem {α : Type*} (s 
: Set α) : s != univ ↔ exists a, a ∉ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DoubleCoset.doubleCoset_eq_of_mem`：doubleCoset_eq_of_mem {H K : Subgroup
 G} {a b : G} (hb : b in doubleCoset a H K) : doubleCoset b H K = doubleCoset a 
H K
· 使用引理 `DoubleCoset.mem_doubleCoset`：mem_doubleCoset {s t : Set α} {a b : α} : b
 in doubleCoset a s t ↔ exists x in s, exists y in t, b = x * a * y
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.mem_op`：mem_op {x : Gᵐᵒᵖ} {S : Subgroup G} : x in S.op ↔ x.unop
 in S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_mul_inv_of_mul_eq`：eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹
-/
lemma iUnion_finset_leftRel_eq_univ_of_leftRel {H K : Subgroup G} {t : Finset (Quotient H K)}
    (ht : Set.univ ⊆ ⋃ i ∈ t, Quot.mk (leftRel K) '' doubleCoset (out i) H K) :
    ⋃ q ∈ t, doubleCoset (out q) H K = Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ht
  refine (Set.ne_univ_iff_exists_notMem _).mpr ⟨Quot.mk (leftRel K) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨y, hy, ?_⟩
  rw [← doubleCoset_eq_of_mem hq, mem_doubleCoset]
  obtain ⟨a', ha'⟩ := Quotient.eq.mp hx
  exact ⟨1, one_mem H, MulOpposite.unop a'⁻¹, Subgroup.mem_op.mp (by simp), by simpa
    using (eq_mul_inv_of_mul_eq ha')⟩
/-
**DoubleCoset.iUnion_finset_rightRel_eq_univ_of_rightRel** 是 Mathlib 中的一个引理，位于命名
空间 `DoubleCoset`。
形式化陈述：iUnion_finset_rightRel_eq_univ_of_rightRel {H K : Subgroup G} {t : Finset 
(Quotient H K)} (ht : Set.univ subseteq ⋃ i in t, Quot.mk (rightRel H) '' double
Coset (out i) H K) : ⋃ q in t, doubleCoset (out q) H K = Set.univ
参数：Quotient H K；ht : Set.univ subseteq ⋃ i in t, Quot.mk (rightRel H) '' doubleC
oset (out i) H K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ne_univ_iff_exists_notMem`：ne_univ_iff_exists_notMem {α : Type*} (s 
: Set α) : s != univ ↔ exists a, a ∉ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DoubleCoset.doubleCoset_eq_of_mem`：doubleCoset_eq_of_mem {H K : Subgroup
 G} {a b : G} (hb : b in doubleCoset a H K) : doubleCoset b H K = doubleCoset a 
H K
· 使用引理 `DoubleCoset.mem_doubleCoset`：mem_doubleCoset {s t : Set α} {a b : α} : b
 in doubleCoset a s t ↔ exists x in s, exists y in t, b = x * a * y
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `eq_inv_mul_of_mul_eq`：eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma iUnion_finset_rightRel_eq_univ_of_rightRel {H K : Subgroup G} {t : Finset (Quotient H K)}
    (ht : Set.univ ⊆ ⋃ i ∈ t, Quot.mk (rightRel H) '' doubleCoset (out i) H K) :
    ⋃ q ∈ t, doubleCoset (out q) H K = Set.univ := by
  contrapose ht
  simp only [Set.univ_subset_iff, ← ne_eq] at ⊢ ht
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem _).mp ht
  refine (Set.ne_univ_iff_exists_notMem _).mpr ⟨Quot.mk (rightRel H) x, ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop, not_exists, not_and]
  intro y hy q hq
  contrapose hx
  simp only [Set.mem_iUnion, exists_prop]
  refine ⟨y, hy, ?_⟩
  rw [← doubleCoset_eq_of_mem hq, mem_doubleCoset]
  obtain ⟨a, ha⟩ : ∃ a : H, x = a * q := by
    obtain ⟨a, ha⟩ : ∃ a : H, a * x = q := Quotient.eq.mp hx
    exact ⟨⟨a⁻¹, by simp⟩, eq_inv_mul_of_mul_eq ha⟩
  exact ⟨a.1, a.2, ⟨1, Subgroup.one_mem K, by simpa using ha⟩⟩

end DoubleCoset

