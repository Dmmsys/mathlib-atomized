/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Topology.Sets.Closeds

/-!
# Clopen upper sets

In this file we define the type of clopen upper sets.
-/

@[expose] public section


open Set TopologicalSpace

variable {α : Type*} [TopologicalSpace α] [LE α]

/-! ### Compact open sets -/


/-- The type of clopen upper sets of a topological space. -/
/-
**ClopenUpperSet** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [TopologicalSpace α] → [LE α] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of clopen upper sets of a topological space.
-/
structure ClopenUpperSet (α : Type*) [TopologicalSpace α] [LE α] extends Clopens α where
  upper' : IsUpperSet carrier

namespace ClopenUpperSet

/-
**ClopenUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `ClopenUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (ClopenUpperSet α) α where
  coe s := s.carrier
  coe_injective s t h := by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr
/-
**ClopenUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `ClopenUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (ClopenUpperSet α) := .ofSetLike (ClopenUpperSet α) α

/-- See Note [custom simps projection]. -/
/-
**ClopenUpperSet.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `ClopenUpperSet.Simps`。
形式化陈述：{α : Type u_1} → [inst : TopologicalSpace α] → [inst_1 : LE α] → ClopenUpp
erSet α → Set α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.coe (s : ClopenUpperSet α) : Set α := s

initialize_simps_projections ClopenUpperSet (carrier → coe, as_prefix coe)
/-
**ClopenUpperSet.upper** 是 Mathlib 中的一个定理，位于命名空间 `ClopenUpperSet`。
形式化陈述：upper (s : ClopenUpperSet α) : IsUpperSet (s : Set α)
参数：s : ClopenUpperSet α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClopenUpperSet.upper'`：∀ {α : Type u_2} [inst : TopologicalSpace α] [ins
t_1 : LE α] (self : ClopenUpperSet α), IsUpperSet self.carrier
-/
theorem upper (s : ClopenUpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'
/-
**ClopenUpperSet.isClopen** 是 Mathlib 中的一个定理，位于命名空间 `ClopenUpperSet`。
形式化陈述：isClopen (s : ClopenUpperSet α) : IsClopen (s : Set α)
参数：s : ClopenUpperSet α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Clopens.isClopen'`：∀ {α : Type u_4} [inst : Topological
Space α] (self : TopologicalSpace.Clopens α), IsClopen self.carrier
-/
theorem isClopen (s : ClopenUpperSet α) : IsClopen (s : Set α) :=
  s.isClopen'

/-- Reinterpret an upper clopen as an upper set. -/
@[simps]
/-
**ClopenUpperSet.toUpperSet** 是 Mathlib 中的一个定义，位于命名空间 `ClopenUpperSet`。
形式化陈述：toUpperSet (s : ClopenUpperSet α) : UpperSet α
参数：s : ClopenUpperSet α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ClopenUpperSet.upper`：upper (s : ClopenUpperSet α) : IsUpperSet (s : Set
 α)

--- 原说明 ---
Reinterpret an upper clopen as an upper set.
-/
def toUpperSet (s : ClopenUpperSet α) : UpperSet α :=
  ⟨s, s.upper⟩

@[ext]
/-
**ClopenUpperSet.ext** 是 Mathlib 中的一个定理，位于命名空间 `ClopenUpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [inst_1 : LE α] {s t : Clopen
UpperSet α}, ↑s = ↑t → s = t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
-/
protected theorem ext {s t : ClopenUpperSet α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
/-
**ClopenUpperSet.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ClopenUpperSet`。
形式化陈述：coe_mk (s : Clopens α) (h) : (mk s h : Set α) = s
参数：s : Clopens α；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Clopens α) (h) : (mk s h : Set α) = s :=
  rfl
/-
**ClopenUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `ClopenUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (ClopenUpperSet α) :=
  ⟨fun s t => ⟨s.toClopens ⊔ t.toClopens, s.upper.union t.upper⟩⟩
/-
**ClopenUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `ClopenUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (ClopenUpperSet α) :=
  ⟨fun s t => ⟨s.toClopens ⊓ t.toClopens, s.upper.inter t.upper⟩⟩
/-
**ClopenUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `ClopenUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (ClopenUpperSet α) :=
  ⟨⟨⊤, isUpperSet_univ⟩⟩
/-
**ClopenUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `ClopenUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (ClopenUpperSet α) :=
  ⟨⟨⊥, isUpperSet_empty⟩⟩
/-
**ClopenUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `ClopenUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice (ClopenUpperSet α) :=
  SetLike.coe_injective.lattice _ .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl
/-
**ClopenUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `ClopenUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder (ClopenUpperSet α) :=
  BoundedOrder.lift ((↑) : _ → Set α) (fun _ _ => id) rfl rfl

@[simp]
/-
**ClopenUpperSet.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `ClopenUpperSet`。
形式化陈述：coe_sup (s t : ClopenUpperSet α) : (↑(s ⊔ t) : Set α) = ↑s union ↑t
参数：s t : ClopenUpperSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (s t : ClopenUpperSet α) : (↑(s ⊔ t) : Set α) = ↑s ∪ ↑t :=
  rfl

@[simp]
/-
**ClopenUpperSet.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `ClopenUpperSet`。
形式化陈述：coe_inf (s t : ClopenUpperSet α) : (↑(s ⊓ t) : Set α) = ↑s inter ↑t
参数：s t : ClopenUpperSet α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (s t : ClopenUpperSet α) : (↑(s ⊓ t) : Set α) = ↑s ∩ ↑t :=
  rfl

@[simp]
/-
**ClopenUpperSet.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `ClopenUpperSet`。
形式化陈述：coe_top : (↑(⊤ : ClopenUpperSet α) : Set α) = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : (↑(⊤ : ClopenUpperSet α) : Set α) = univ :=
  rfl

@[simp]
/-
**ClopenUpperSet.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `ClopenUpperSet`。
形式化陈述：coe_bot : (↑(⊥ : ClopenUpperSet α) : Set α) = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : (↑(⊥ : ClopenUpperSet α) : Set α) = ∅ :=
  rfl
/-
**ClopenUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `ClopenUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ClopenUpperSet α) :=
  ⟨⊥⟩

end ClopenUpperSet

