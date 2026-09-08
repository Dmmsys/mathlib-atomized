/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Category.Preord
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# Specialization order

This file defines a type synonym for a topological space considered with its specialisation order.
-/

@[expose] public section

open CategoryTheory Topology

/-- Type synonym for a topological space considered with its specialisation order. -/
/-
**Specialization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Specialization (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for a topological space considered with its specialisation order.
-/
def Specialization (α : Type*) := α

namespace Specialization
variable {α β γ : Type*}

/-- `toEquiv` is the "identity" function to the `Specialization` of a type. -/
/-
**Specialization.toEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Specialization`。
形式化陈述：{α : Type u_1} → α ≃ Specialization α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`toEquiv` is the "identity" function to the `Specialization` of a type.
-/
@[match_pattern] def toEquiv : α ≃ Specialization α := Equiv.refl _

/-- `ofEquiv` is the identity function from the `Specialization` of a type. -/
/-
**Specialization.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Specialization`。
形式化陈述：{α : Type u_1} → Specialization α ≃ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`ofEquiv` is the identity function from the `Specialization` of a type.
-/
@[match_pattern] def ofEquiv : Specialization α ≃ α := Equiv.refl _
/-
**Specialization.toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Specialization`。
形式化陈述：∀ {α : Type u_1}, Specialization.toEquiv.symm = Specialization.ofEquiv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ofEquiv` is the identity function from the `Specialization` of a type.
-/
@[simp] lemma toEquiv_symm : (@toEquiv α).symm = ofEquiv := rfl
/-
**Specialization.ofEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Specialization`。
形式化陈述：∀ {α : Type u_1}, Specialization.ofEquiv.symm = Specialization.toEquiv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ofEquiv` is the identity function from the `Specialization` of a type.
-/
@[simp] lemma ofEquiv_symm : (@ofEquiv α).symm = toEquiv := rfl
/-
**Specialization.toEquiv_ofEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Specialization`。
形式化陈述：∀ {α : Type u_1} (a : Specialization α), Specialization.toEquiv (Specializ
ation.ofEquiv a) = a
参数：a : Specialization α；Specialization.ofEquiv a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofEquiv` is the identity function from the `Specialization` of a type.
-/
@[simp] lemma toEquiv_ofEquiv (a : Specialization α) : toEquiv (ofEquiv a) = a := rfl
/-
**Specialization.ofEquiv_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Specialization`。
形式化陈述：∀ {α : Type u_1} (a : α), Specialization.ofEquiv (Specialization.toEquiv a
) = a
参数：a : α；Specialization.toEquiv a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofEquiv` is the identity function from the `Specialization` of a type.
-/
@[simp] lemma ofEquiv_toEquiv (a : α) : ofEquiv (toEquiv a) = a := rfl

-- In Lean 3, `dsimp` would use theorems proved by `Iff.rfl`.
-- If that were still the case, this would useful as a `@[simp]` lemma,
-- despite the fact that it is provable by `simp` (but not `dsimp`).
@[simp, nolint simpNF] -- See https://github.com/leanprover-community/mathlib4/issues/10675
/-
**Specialization.toEquiv_inj** 是 Mathlib 中的一个引理，位于命名空间 `Specialization`。
形式化陈述：toEquiv_inj {a b : α} : toEquiv a = toEquiv b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toEquiv_inj {a b : α} : toEquiv a = toEquiv b ↔ a = b := Iff.rfl

-- In Lean 3, `dsimp` would use theorems proved by `Iff.rfl`.
-- If that were still the case, this would useful as a `@[simp]` lemma,
-- despite the fact that it is provable by `simp` (but not `dsimp`).
@[simp, nolint simpNF] -- See https://github.com/leanprover-community/mathlib4/issues/10675
/-
**Specialization.ofEquiv_inj** 是 Mathlib 中的一个引理，位于命名空间 `Specialization`。
形式化陈述：ofEquiv_inj {a b : Specialization α} : ofEquiv a = ofEquiv b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofEquiv_inj {a b : Specialization α} : ofEquiv a = ofEquiv b ↔ a = b :=
  Iff.rfl

/-- A recursor for `Specialization`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Specialization.rec** 是 Mathlib 中的一个定义，位于命名空间 `Specialization`。
形式化陈述：{α : Type u_1} →   {β : Specialization α → Sort u_4} → ((a : α) → β (Speci
alization.toEquiv a)) → (a : Specialization α) → β a
参数：(a : α) → β (Specialization.toEquiv a)；a : Specialization α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `Specialization`. Use as `induction x`.
-/
protected def rec {β : Specialization α → Sort*} (h : ∀ a, β (toEquiv a)) (a : Specialization α) :
    β a :=
  h (ofEquiv a)

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
/-
**Specialization.instPreorder** 是 Mathlib 中的一个实例，位于命名空间 `Specialization`。
形式化陈述：instPreorder : Preorder (Specialization α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPreorder : Preorder (Specialization α) :=
  fast_instance% specializationPreorder α
/-
**Specialization.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Specialization`。
形式化陈述：instPartialOrder [T0Space α] : PartialOrder (Specialization α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder [T0Space α] : PartialOrder (Specialization α) :=
  fast_instance% specializationOrder α
/-
**Specialization.toEquiv_le_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Specialization`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {a b : α}, Specialization.toE
quiv a ≤ Specialization.toEquiv b ↔ b ⤳ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma toEquiv_le_toEquiv {a b : α} : toEquiv a ≤ toEquiv b ↔ b ⤳ a := Iff.rfl
/-
**Specialization.ofEquiv_specializes_ofEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Speciali
zation`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {a b : Specialization α},   S
pecialization.ofEquiv a ⤳ Specialization.ofEquiv b ↔ b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofEquiv_specializes_ofEquiv {a b : Specialization α} :
    ofEquiv a ⤳ ofEquiv b ↔ b ≤ a := Iff.rfl
/-
**Specialization.isOpen_toEquiv_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Specializati
on`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {s : S
et (Specialization α)},   IsOpen (⇑Specialization.toEquiv ⁻¹' s) ↔ IsUpperSet s
参数：Specialization α；⇑Specialization.toEquiv ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isOpen_iff_forall_specializes`：∀ {α : Type u_3} [inst : TopologicalSpace
 α] [AlexandrovDiscrete α] {s : Set α},   IsOpen s ↔ ∀ (x y : α), x ⤳ y → y ∈ s 
→ x ∈ s
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
@[simp] lemma isOpen_toEquiv_preimage [AlexandrovDiscrete α] {s : Set (Specialization α)} :
    IsOpen (toEquiv ⁻¹' s) ↔ IsUpperSet s := isOpen_iff_forall_specializes.trans forall_comm
/-
**Specialization.isUpperSet_ofEquiv_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Speciali
zation`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] [AlexandrovDiscrete α] {s : S
et α},   IsUpperSet (⇑Specialization.ofEquiv ⁻¹' s) ↔ IsOpen s
参数：⇑Specialization.ofEquiv ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Specialization.isOpen_toEquiv_preimage`：∀ {α : Type u_1} [inst : Topolog
icalSpace α] [AlexandrovDiscrete α] {s : Set (Specialization α)},   IsOpen (⇑Spe
cialization.toEquiv ⁻¹' s) ↔…
-/
@[simp] lemma isUpperSet_ofEquiv_preimage [AlexandrovDiscrete α] {s : Set α} :
    IsUpperSet (ofEquiv ⁻¹' s) ↔ IsOpen s := isOpen_toEquiv_preimage.symm

/-- A continuous map between topological spaces induces a monotone map between their specialization
orders. -/
/-
**Specialization.map** 是 Mathlib 中的一个定义，位于命名空间 `Specialization`。
形式化陈述：map (f : C(α, β)) : Specialization α ->o Specialization β where toFun
参数：f : C(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous map between topological spaces induces a monotone map between their
 specialization
orders.
-/
def map (f : C(α, β)) : Specialization α →o Specialization β where
  toFun := toEquiv ∘ f ∘ ofEquiv
  monotone' := (map_continuous f).specialization_monotone
/-
**Specialization.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Specialization`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α], Specialization.map (Continuo
usMap.id α) = OrderHom.id
参数：ContinuousMap.id α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_id : map (ContinuousMap.id α) = OrderHom.id := rfl
/-
**Specialization.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Specialization`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : TopologicalSpace α]
 [inst_1 : TopologicalSpace β]   [inst_2 : TopologicalSpace γ] (g : C(β, γ)) (f 
: C(α, β)),   Specialization.map (g.comp f) = (Specialization.map g).comp (Speci
alization.map f)
参数：g : C(β, γ)；f : C(α, β)；g.comp f；Specialization.map g；Specialization.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_comp (g : C(β, γ)) (f : C(α, β)) : map (g.comp f) = (map g).comp (map f) := rfl

end Specialization

open Set Specialization WithUpperSet

/-- A preorder is isomorphic to the specialisation order of its upper set topology. -/
/-
**orderIsoSpecializationWithUpperSetTopology** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：orderIsoSpecializationWithUpperSetTopology (α : Type*) [Preorder α] : α ≃o
 Specialization (WithUpperSet α) where toEquiv
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A preorder is isomorphic to the specialisation order of its upper set topology.
-/
def orderIsoSpecializationWithUpperSetTopology (α : Type*) [Preorder α] :
    α ≃o Specialization (WithUpperSet α) where
  toEquiv := toUpperSet.trans toEquiv
  map_rel_iff' := by simp

/-- An Alexandrov-discrete space is isomorphic to the upper set topology of its specialisation
order. -/
/-
**homeoWithUpperSetTopologyorderIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：homeoWithUpperSetTopologyorderIso (α : Type*) [TopologicalSpace α] [Alexan
drovDiscrete α] : α ≃ₜ WithUpperSet (Specialization α)
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
An Alexandrov-discrete space is isomorphic to the upper set topology of its spec
ialisation
order.
-/
def homeoWithUpperSetTopologyorderIso (α : Type*) [TopologicalSpace α] [AlexandrovDiscrete α] :
    α ≃ₜ WithUpperSet (Specialization α) :=
  (toEquiv.trans toUpperSet).toHomeomorph fun s ↦ by simp [Set.preimage_comp]

/-- Sends a topological space to its specialisation order. -/
@[simps]
/-
**topToPreord** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：topToPreord : TopCat ⥤ Preord where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sends a topological space to its specialisation order.
-/
def topToPreord : TopCat ⥤ Preord where
  obj X := .of <| Specialization X
  map f := Preord.ofHom <| Specialization.map f.hom
