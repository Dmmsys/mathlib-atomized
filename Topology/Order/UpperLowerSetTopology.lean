/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Logic.Lemmas
public import Mathlib.Topology.AlexandrovDiscrete
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order.LowerUpperTopology

/-!
# Upper and lower sets topologies

This file introduces the upper set topology on a preorder as the topology where the open sets are
the upper sets and the lower set topology on a preorder as the topology where the open sets are
the lower sets.

In general the upper set topology does not coincide with the upper topology and the lower set
topology does not coincide with the lower topology.

## Main statements

- `Topology.IsUpperSet.toAlexandrovDiscrete`: The upper set topology is Alexandrov-discrete.
- `Topology.IsUpperSet.isClosed_iff_isLower` - a set is closed if and only if it is a Lower set
- `Topology.IsUpperSet.closure_eq_lowerClosure` - topological closure coincides with lower closure
- `Topology.IsUpperSet.monotone_iff_continuous` - the continuous functions are the monotone
  functions
- `IsUpperSet.monotone_to_upperTopology_continuous`: A monotone map from a preorder with the upper
  set topology to a preorder with the upper topology is continuous.

We provide the upper set topology in three ways (and similarly for the lower set topology):
* `Topology.upperSet`: The upper set topology as a `TopologicalSpace α`
* `Topology.IsUpperSet`: Prop-valued mixin typeclass stating that an existing topology is the upper
  set topology.
* `Topology.WithUpperSet`: Type synonym equipping a preorder with its upper set topology.

## Motivation

An Alexandrov topology is a topology where the intersection of any collection of open sets is open.
The upper set topology is an Alexandrov topology and, given any Alexandrov topological space, we can
equip it with a preorder (namely the specialization preorder) whose upper set topology coincides
with the original topology. See `Topology.Specialization`.

## Tags

upper set topology, lower set topology, preorder, Alexandrov
-/

@[expose] public section

open Set TopologicalSpace Filter

variable {α β γ : Type*}

namespace Topology

/-- Topology whose open sets are upper sets.

Note: In general the upper set topology does not coincide with the upper topology. -/
@[instance_reducible]
/-
**Topology.upperSet** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：upperSet (α : Type*) [Preorder α] : TopologicalSpace α where IsOpen
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topology whose open sets are upper sets.

Note: In general the upper set topology does not coincide with the upper topolog
y.
-/
def upperSet (α : Type*) [Preorder α] : TopologicalSpace α where
  IsOpen := IsUpperSet
  isOpen_univ := isUpperSet_univ
  isOpen_inter _ _ := IsUpperSet.inter
  isOpen_sUnion _ := isUpperSet_sUnion

/-- Topology whose open sets are lower sets.

Note: In general the lower set topology does not coincide with the lower topology. -/
@[instance_reducible]
/-
**Topology.lowerSet** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：lowerSet (α : Type*) [Preorder α] : TopologicalSpace α where IsOpen
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topology whose open sets are lower sets.

Note: In general the lower set topology does not coincide with the lower topolog
y.
-/
def lowerSet (α : Type*) [Preorder α] : TopologicalSpace α where
  IsOpen := IsLowerSet
  isOpen_univ := isLowerSet_univ
  isOpen_inter _ _ := IsLowerSet.inter
  isOpen_sUnion _ := isLowerSet_sUnion

/-- Type synonym for a preorder equipped with the upper set topology. -/
/-
**Topology.WithUpperSet** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：WithUpperSet (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for a preorder equipped with the upper set topology.
-/
def WithUpperSet (α : Type*) := α

namespace WithUpperSet

/-- `toUpperSet` is the identity function to the `WithUpperSet` of a type. -/
/-
**Topology.WithUpperSet.toUpperSet** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithUpper
Set`。
形式化陈述：{α : Type u_1} → α ≃ Topology.WithUpperSet α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`toUpperSet` is the identity function to the `WithUpperSet` of a type.
-/
@[match_pattern] def toUpperSet : α ≃ WithUpperSet α := Equiv.refl _

/-- `ofUpperSet` is the identity function from the `WithUpperSet` of a type. -/
/-
**Topology.WithUpperSet.ofUpperSet** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithUpper
Set`。
形式化陈述：{α : Type u_1} → Topology.WithUpperSet α ≃ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`ofUpperSet` is the identity function from the `WithUpperSet` of a type.
-/
@[match_pattern] def ofUpperSet : WithUpperSet α ≃ α := Equiv.refl _
/-
**Topology.WithUpperSet.toUpperSet_symm** 是 Mathlib 中的一个定理，位于命名空间 `Topology.With
UpperSet`。
形式化陈述：∀ {α : Type u_1}, Topology.WithUpperSet.toUpperSet.symm = Topology.WithUpp
erSet.ofUpperSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ofUpperSet` is the identity function from the `WithUpperSet` of a type.
-/
@[simp] lemma toUpperSet_symm : (@toUpperSet α).symm = ofUpperSet := rfl
/-
**Topology.WithUpperSet.ofUpperSet_symm** 是 Mathlib 中的一个定理，位于命名空间 `Topology.With
UpperSet`。
形式化陈述：∀ {α : Type u_1}, Topology.WithUpperSet.ofUpperSet.symm = Topology.WithUpp
erSet.toUpperSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ofUpperSet` is the identity function from the `WithUpperSet` of a type.
-/
@[simp] lemma ofUpperSet_symm : (@ofUpperSet α).symm = toUpperSet := rfl
/-
**Topology.WithUpperSet.toUpperSet_ofUpperSet** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.WithUpperSet`。
形式化陈述：∀ {α : Type u_1} (a : Topology.WithUpperSet α),   Topology.WithUpperSet.to
UpperSet (Topology.WithUpperSet.ofUpperSet a) = a
参数：a : Topology.WithUpperSet α；Topology.WithUpperSet.ofUpperSet a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofUpperSet` is the identity function from the `WithUpperSet` of a type.
-/
@[simp] lemma toUpperSet_ofUpperSet (a : WithUpperSet α) : toUpperSet (ofUpperSet a) = a := rfl
/-
**Topology.WithUpperSet.ofUpperSet_toUpperSet** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.WithUpperSet`。
形式化陈述：∀ {α : Type u_1} (a : α), Topology.WithUpperSet.ofUpperSet (Topology.WithU
pperSet.toUpperSet a) = a
参数：a : α；Topology.WithUpperSet.toUpperSet a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofUpperSet` is the identity function from the `WithUpperSet` of a type.
-/
@[simp] lemma ofUpperSet_toUpperSet (a : α) : ofUpperSet (toUpperSet a) = a := rfl
/-
**Topology.WithUpperSet.toUpperSet_inj** 是 Mathlib 中的一个引理，位于命名空间 `Topology.WithU
pperSet`。
形式化陈述：toUpperSet_inj {a b : α} : toUpperSet a = toUpperSet b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`ofUpperSet` is the identity function from the `WithUpperSet` of a type.
-/
lemma toUpperSet_inj {a b : α} : toUpperSet a = toUpperSet b ↔ a = b := Iff.rfl
/-
**Topology.WithUpperSet.ofUpperSet_inj** 是 Mathlib 中的一个引理，位于命名空间 `Topology.WithU
pperSet`。
形式化陈述：ofUpperSet_inj {a b : WithUpperSet α} : ofUpperSet a = ofUpperSet b ↔ a = 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofUpperSet_inj {a b : WithUpperSet α} : ofUpperSet a = ofUpperSet b ↔ a = b := Iff.rfl

/-- A recursor for `WithUpperSet`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Topology.WithUpperSet.rec** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithUpperSet`。
形式化陈述：{α : Type u_1} →   {motive : Topology.WithUpperSet α → Sort u_4} →     ((a
 : α) → motive (Topology.WithUpperSet.toUpperSet a)) → (a : Topology.WithUpperSe
t α) → motive a
参数：(a : α) → motive (Topology.WithUpperSet.toUpperSet a)；a : Topology.WithUpperS
et α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `WithUpperSet`. Use as `induction x`.
-/
protected def rec {motive : WithUpperSet α → Sort*} (toUpperSet : ∀ a, motive (toUpperSet a)) :
    ∀ a, motive a :=
  fun a => toUpperSet (ofUpperSet a)
/-
**Topology.WithUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (WithUpperSet α) := ‹Nonempty α›
/-
**Topology.WithUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (WithUpperSet α) := ‹Inhabited α›

variable [Preorder α] [Preorder β]
/-
**Topology.WithUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (WithUpperSet α) := ‹Preorder α›
/-
**Topology.WithUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (WithUpperSet α) :=
  fast_instance% upperSet α
/-
**Topology.WithUpperSet.ofUpperSet_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.Wi
thUpperSet`。
形式化陈述：ofUpperSet_le_iff {a b : WithUpperSet α} : ofUpperSet a <= ofUpperSet b ↔ 
a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofUpperSet_le_iff {a b : WithUpperSet α} : ofUpperSet a ≤ ofUpperSet b ↔ a ≤ b := Iff.rfl
/-
**Topology.WithUpperSet.toUpperSet_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.Wi
thUpperSet`。
形式化陈述：toUpperSet_le_iff {a b : α} : toUpperSet a <= toUpperSet b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toUpperSet_le_iff {a b : α} : toUpperSet a ≤ toUpperSet b ↔ a ≤ b := Iff.rfl

/-- `ofUpperSet` as an `OrderIso` -/
/-
**Topology.WithUpperSet.ofUpperSetOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Topology.W
ithUpperSet`。
形式化陈述：ofUpperSetOrderIso : WithUpperSet α ≃o α where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.WithUpperSet.ofUpperSet_le_iff`：ofUpperSet_le_iff {a b : WithUp
perSet α} : ofUpperSet a <= ofUpperSet b ↔ a <= b

--- 原说明 ---
`ofUpperSet` as an `OrderIso`
-/
def ofUpperSetOrderIso : WithUpperSet α ≃o α where
  toEquiv := ofUpperSet
  map_rel_iff' := ofUpperSet_le_iff

/-- `toUpperSet` as an `OrderIso` -/
/-
**Topology.WithUpperSet.toUpperSetOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Topology.W
ithUpperSet`。
形式化陈述：toUpperSetOrderIso : α ≃o WithUpperSet α where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.WithUpperSet.toUpperSet_le_iff`：toUpperSet_le_iff {a b : α} : t
oUpperSet a <= toUpperSet b ↔ a <= b

--- 原说明 ---
`toUpperSet` as an `OrderIso`
-/
def toUpperSetOrderIso : α ≃o WithUpperSet α where
  toEquiv := toUpperSet
  map_rel_iff' := toUpperSet_le_iff

end WithUpperSet

/-- Type synonym for a preorder equipped with the lower set topology. -/
/-
**Topology.WithLowerSet** 是 Mathlib 中的一个定义，位于命名空间 `Topology`。
形式化陈述：WithLowerSet (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for a preorder equipped with the lower set topology.
-/
def WithLowerSet (α : Type*) := α

namespace WithLowerSet

/-- `toLowerSet` is the identity function to the `WithLowerSet` of a type. -/
/-
**Topology.WithLowerSet.toLowerSet** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithLower
Set`。
形式化陈述：{α : Type u_1} → α ≃ Topology.WithLowerSet α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`toLowerSet` is the identity function to the `WithLowerSet` of a type.
-/
@[match_pattern] def toLowerSet : α ≃ WithLowerSet α := Equiv.refl _

/-- `ofLowerSet` is the identity function from the `WithLowerSet` of a type. -/
/-
**Topology.WithLowerSet.ofLowerSet** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithLower
Set`。
形式化陈述：{α : Type u_1} → Topology.WithLowerSet α ≃ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`ofLowerSet` is the identity function from the `WithLowerSet` of a type.
-/
@[match_pattern] def ofLowerSet : WithLowerSet α ≃ α := Equiv.refl _
/-
**Topology.WithLowerSet.toLowerSet_symm** 是 Mathlib 中的一个定理，位于命名空间 `Topology.With
LowerSet`。
形式化陈述：∀ {α : Type u_1}, Topology.WithLowerSet.toLowerSet.symm = Topology.WithLow
erSet.ofLowerSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ofLowerSet` is the identity function from the `WithLowerSet` of a type.
-/
@[simp] lemma toLowerSet_symm : (@toLowerSet α).symm = ofLowerSet := rfl
/-
**Topology.WithLowerSet.ofLowerSet_symm** 是 Mathlib 中的一个定理，位于命名空间 `Topology.With
LowerSet`。
形式化陈述：∀ {α : Type u_1}, Topology.WithLowerSet.ofLowerSet.symm = Topology.WithLow
erSet.toLowerSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`ofLowerSet` is the identity function from the `WithLowerSet` of a type.
-/
@[simp] lemma ofLowerSet_symm : (@ofLowerSet α).symm = toLowerSet := rfl
/-
**Topology.WithLowerSet.toLowerSet_ofLowerSet** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.WithLowerSet`。
形式化陈述：∀ {α : Type u_1} (a : Topology.WithLowerSet α),   Topology.WithLowerSet.to
LowerSet (Topology.WithLowerSet.ofLowerSet a) = a
参数：a : Topology.WithLowerSet α；Topology.WithLowerSet.ofLowerSet a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofLowerSet` is the identity function from the `WithLowerSet` of a type.
-/
@[simp] lemma toLowerSet_ofLowerSet (a : WithLowerSet α) : toLowerSet (ofLowerSet a) = a := rfl
/-
**Topology.WithLowerSet.ofLowerSet_toLowerSet** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.WithLowerSet`。
形式化陈述：∀ {α : Type u_1} (a : α), Topology.WithLowerSet.ofLowerSet (Topology.WithL
owerSet.toLowerSet a) = a
参数：a : α；Topology.WithLowerSet.toLowerSet a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofLowerSet` is the identity function from the `WithLowerSet` of a type.
-/
@[simp] lemma ofLowerSet_toLowerSet (a : α) : ofLowerSet (toLowerSet a) = a := rfl
/-
**Topology.WithLowerSet.toLowerSet_inj** 是 Mathlib 中的一个引理，位于命名空间 `Topology.WithL
owerSet`。
形式化陈述：toLowerSet_inj {a b : α} : toLowerSet a = toLowerSet b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`ofLowerSet` is the identity function from the `WithLowerSet` of a type.
-/
lemma toLowerSet_inj {a b : α} : toLowerSet a = toLowerSet b ↔ a = b := Iff.rfl
/-
**Topology.WithLowerSet.ofLowerSet_inj** 是 Mathlib 中的一个引理，位于命名空间 `Topology.WithL
owerSet`。
形式化陈述：ofLowerSet_inj {a b : WithLowerSet α} : ofLowerSet a = ofLowerSet b ↔ a = 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofLowerSet_inj {a b : WithLowerSet α} : ofLowerSet a = ofLowerSet b ↔ a = b := Iff.rfl

/-- A recursor for `WithLowerSet`. Use as `induction x`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Topology.WithLowerSet.rec** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithLowerSet`。
形式化陈述：{α : Type u_1} →   {motive : Topology.WithLowerSet α → Sort u_4} →     ((a
 : α) → motive (Topology.WithLowerSet.toLowerSet a)) → (a : Topology.WithLowerSe
t α) → motive a
参数：(a : α) → motive (Topology.WithLowerSet.toLowerSet a)；a : Topology.WithLowerS
et α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `WithLowerSet`. Use as `induction x`.
-/
protected def rec {motive : WithLowerSet α → Sort*} (toLowerSet : ∀ a, motive (toLowerSet a)) :
    ∀ a, motive a :=
  fun a => toLowerSet (ofLowerSet a)
/-
**Topology.WithLowerSet.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithLowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty α] : Nonempty (WithLowerSet α) := ‹Nonempty α›
/-
**Topology.WithLowerSet.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithLowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (WithLowerSet α) := ‹Inhabited α›

variable [Preorder α]
/-
**Topology.WithLowerSet.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithLowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (WithLowerSet α) := ‹Preorder α›
/-
**Topology.WithLowerSet.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.WithLowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (WithLowerSet α) :=
  fast_instance% lowerSet α
/-
**Topology.WithLowerSet.ofLowerSet_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.Wi
thLowerSet`。
形式化陈述：ofLowerSet_le_iff {a b : WithLowerSet α} : ofLowerSet a <= ofLowerSet b ↔ 
a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma ofLowerSet_le_iff {a b : WithLowerSet α} : ofLowerSet a ≤ ofLowerSet b ↔ a ≤ b := Iff.rfl
/-
**Topology.WithLowerSet.toLowerSet_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Topology.Wi
thLowerSet`。
形式化陈述：toLowerSet_le_iff {a b : α} : toLowerSet a <= toLowerSet b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toLowerSet_le_iff {a b : α} : toLowerSet a ≤ toLowerSet b ↔ a ≤ b := Iff.rfl

/-- `ofLowerSet` as an `OrderIso` -/
/-
**Topology.WithLowerSet.ofLowerSetOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Topology.W
ithLowerSet`。
形式化陈述：ofLowerSetOrderIso : WithLowerSet α ≃o α where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.WithLowerSet.ofLowerSet_le_iff`：ofLowerSet_le_iff {a b : WithLo
werSet α} : ofLowerSet a <= ofLowerSet b ↔ a <= b

--- 原说明 ---
`ofLowerSet` as an `OrderIso`
-/
def ofLowerSetOrderIso : WithLowerSet α ≃o α where
  toEquiv := ofLowerSet
  map_rel_iff' := ofLowerSet_le_iff

/-- `toLowerSet` as an `OrderIso` -/
/-
**Topology.WithLowerSet.toLowerSetOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Topology.W
ithLowerSet`。
形式化陈述：toLowerSetOrderIso : α ≃o WithLowerSet α where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.WithLowerSet.toLowerSet_le_iff`：toLowerSet_le_iff {a b : α} : t
oLowerSet a <= toLowerSet b ↔ a <= b

--- 原说明 ---
`toLowerSet` as an `OrderIso`
-/
def toLowerSetOrderIso : α ≃o WithLowerSet α where
  toEquiv := toLowerSet
  map_rel_iff' := toLowerSet_le_iff

end WithLowerSet

/--
The Upper Set topology is homeomorphic to the Lower Set topology on the dual order
-/
/-
**Topology.WithUpperSet.toDualHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Topology.Wit
hUpperSet`。
形式化陈述：{α : Type u_1} → [inst : Preorder α] → Topology.WithUpperSet α ≃ₜ Topology
.WithLowerSet αᵒᵈ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderDual.toDual_ofDual`：∀ {α : Type u_1} (a : αᵒᵈ), OrderDual.toDual (O
rderDual.ofDual a) = a

--- 原说明 ---
The Upper Set topology is homeomorphic to the Lower Set topology on the dual ord
er
-/
def WithUpperSet.toDualHomeomorph [Preorder α] : WithUpperSet α ≃ₜ WithLowerSet αᵒᵈ where
  toFun := OrderDual.toDual
  invFun := OrderDual.ofDual
  left_inv := OrderDual.toDual_ofDual
  right_inv := OrderDual.ofDual_toDual
  continuous_toFun := continuous_coinduced_rng
  continuous_invFun := continuous_coinduced_rng

/-- Prop-valued mixin for an ordered topological space to be
The upper set topology is the topology where the open sets are the upper sets. In general the upper
set topology does not coincide with the upper topology.
-/
/-
**Topology.IsUpperSet** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：(α : Type u_4) → [t : TopologicalSpace α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prop-valued mixin for an ordered topological space to be
The upper set topology is the topology where the open sets are the upper sets. I
n general the upper
set topology does not coincide with the upper topology.
-/
protected class IsUpperSet (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_upperSetTopology : t = upperSet α

attribute [nolint docBlame] IsUpperSet.topology_eq_upperSetTopology
/-
**Topology.** 是 Mathlib 中的一个实例，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : Topology.IsUpperSet (WithUpperSet α) := ⟨rfl⟩
/-
**Topology.** 是 Mathlib 中的一个实例，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : @Topology.IsUpperSet α (upperSet α) _ := by
  let := upperSet α
  exact ⟨rfl⟩

/--
The lower set topology is the topology where the open sets are the lower sets. In general the lower
set topology does not coincide with the lower topology.
-/
/-
**Topology.IsLowerSet** 是 Mathlib 中的一个归纳类型，位于命名空间 `Topology`。
形式化陈述：(α : Type u_4) → [t : TopologicalSpace α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lower set topology is the topology where the open sets are the lower sets. I
n general the lower
set topology does not coincide with the lower topology.
-/
protected class IsLowerSet (α : Type*) [t : TopologicalSpace α] [Preorder α] : Prop where
  topology_eq_lowerSetTopology : t = lowerSet α

attribute [nolint docBlame] IsLowerSet.topology_eq_lowerSetTopology
/-
**Topology.** 是 Mathlib 中的一个实例，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : Topology.IsLowerSet (WithLowerSet α) := ⟨rfl⟩
/-
**Topology.** 是 Mathlib 中的一个实例，位于命名空间 `Topology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : @Topology.IsLowerSet α (lowerSet α) _ := by
  let := lowerSet α
  exact ⟨rfl⟩

namespace IsUpperSet

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [Topology.IsUpperSet α] {s : Set α}

/-
**Topology.IsUpperSet.topology_eq** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsUpperSet
`。
形式化陈述：topology_eq : ‹_› = upperSet α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsUpperSet.topology_eq_upperSetTopology`：∀ {α : Type u_4} {t : 
TopologicalSpace α} {inst : Preorder α} [self : Topology.IsUpperSet α], t = Topo
logy.upperSet α
-/
lemma topology_eq : ‹_› = upperSet α := topology_eq_upperSetTopology

variable {α}

set_option backward.isDefEq.respectTransparency false in
/-
**Topology.IsUpperSet._root_.OrderDual.instIsLowerSet** 是 Mathlib 中的一个实例，位于命名空间 
`Topology.IsUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.OrderDual.instIsLowerSet : Topology.IsLowerSet αᵒᵈ where
  topology_eq_lowerSetTopology := by ext; rw [IsUpperSet.topology_eq α]

/-- If `α` is equipped with the upper set topology, then it is homeomorphic to
`WithUpperSet α`. -/
/-
**Topology.IsUpperSet.WithUpperSetHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Topology
.IsUpperSet`。
形式化陈述：WithUpperSetHomeomorph : WithUpperSet α ≃ₜ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is equipped with the upper set topology, then it is homeomorphic to
`WithUpperSet α`.
-/
def WithUpperSetHomeomorph : WithUpperSet α ≃ₜ α :=
  WithUpperSet.ofUpperSet.toHomeomorphOfIsInducing ⟨topology_eq α ▸ induced_id.symm⟩
/-
**Topology.IsUpperSet.isOpen_iff_isUpperSet** 是 Mathlib 中的一个引理，位于命名空间 `Topology.
IsUpperSet`。
形式化陈述：isOpen_iff_isUpperSet : IsOpen s ↔ IsUpperSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsUpperSet.topology_eq`：topology_eq : ‹_› = upperSet α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isOpen_iff_isUpperSet : IsOpen s ↔ IsUpperSet s := by
  rw [topology_eq α]
  rfl
/-
**Topology.IsUpperSet.toAlexandrovDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `Topology.I
sUpperSet`。
形式化陈述：toAlexandrovDiscrete : AlexandrovDiscrete α where isOpen_sInter S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `isUpperSet_sInter`：isUpperSet_sInter {S : Set (Set α)} (hf : forall s in
 S, IsUpperSet s) : IsUpperSet (⋂₀ S)
-/
instance toAlexandrovDiscrete : AlexandrovDiscrete α where
  isOpen_sInter S := by simpa only [isOpen_iff_isUpperSet] using isUpperSet_sInter (α := α)

-- c.f. isClosed_iff_lower_and_subset_implies_LUB_mem
/-
**Topology.IsUpperSet.isClosed_iff_isLower** 是 Mathlib 中的一个引理，位于命名空间 `Topology.I
sUpperSet`。
形式化陈述：isClosed_iff_isLower : IsClosed s ↔ IsLowerSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用引理 `Topology.IsUpperSet.isOpen_iff_isUpperSet`：isOpen_iff_isUpperSet : IsOpe
n s ↔ IsUpperSet s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isLowerSet_compl`：∀ {α : Type u_1} [inst : LE α] {s : Set α}, IsLowerSet
 sᶜ ↔ IsUpperSet s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClosed_iff_isLower : IsClosed s ↔ IsLowerSet s := by
  rw [← isOpen_compl_iff, isOpen_iff_isUpperSet,
    isLowerSet_compl.symm, compl_compl]
/-
**Topology.IsUpperSet.closure_eq_lowerClosure** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
y.IsUpperSet`。
形式化陈述：closure_eq_lowerClosure {s : Set α} : closure s = lowerClosure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `subset_lowerClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, s
 ⊆ ↑(lowerClosure s)
· 使用引理 `Topology.IsUpperSet.isClosed_iff_isLower`：isClosed_iff_isLower : IsClose
d s ↔ IsLowerSet s
· 使用定理 `LowerSet.lower`：∀ {α : Type u_1} [inst : LE α] (s : LowerSet α), IsLower
Set ↑s
· 使用定理 `lowerClosure_min`：∀ {α : Type u_1} [inst : Preorder α] {s t : Set α}, s 
⊆ t → IsLowerSet t → ↑(lowerClosure s) ⊆ t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
lemma closure_eq_lowerClosure {s : Set α} : closure s = lowerClosure s := by
  rw [subset_antisymm_iff]
  refine ⟨?_, lowerClosure_min subset_closure (isClosed_iff_isLower.1 isClosed_closure)⟩
  · apply closure_minimal subset_lowerClosure _
    rw [isClosed_iff_isLower]
    exact LowerSet.lower (lowerClosure s)

/--
The closure of a singleton `{a}` in the upper set topology is the right-closed left-infinite
interval $(-∞,a]$.
-/
/-
**Topology.IsUpperSet.closure_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsUp
perSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : TopologicalSpace α] [Topolo
gy.IsUpperSet α] {a : α},   closure {a} = Set.Iic a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsUpperSet.closure_eq_lowerClosure`：closure_eq_lowerClosure {s 
: Set α} : closure s = lowerClosure s
· 使用定理 `lowerClosure_singleton`：∀ {α : Type u_1} [inst : Preorder α] (a : α), lo
werClosure {a} = LowerSet.Iic a

--- 原说明 ---
The closure of a singleton `{a}` in the upper set topology is the right-closed l
eft-infinite
interval $(-∞,a]$.
-/
@[simp] lemma closure_singleton {a : α} : closure {a} = Iic a := by
  rw [closure_eq_lowerClosure, lowerClosure_singleton]
  rfl
/-
**Topology.IsUpperSet.specializes_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsU
pperSet`。
形式化陈述：specializes_iff_le {a b : α} : a ⤳ b ↔ b <= a
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
· 使用定理 `Topology.IsUpperSet.closure_singleton`：∀ {α : Type u_1} [inst : Preorder
 α] [inst_1 : TopologicalSpace α] [Topology.IsUpperSet α] {a : α},   closure {a}
 = Set.Iic a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma specializes_iff_le {a b : α} : a ⤳ b ↔ b ≤ a := by
  simp only [specializes_iff_closure_subset, closure_singleton, Iic_subset_Iic]
/-
**Topology.IsUpperSet.nhdsKer_eq_upperClosure** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
y.IsUpperSet`。
形式化陈述：nhdsKer_eq_upperClosure (s : Set α) : nhdsKer s = ↑(upperClosure s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nhdsKer_eq_upperClosure (s : Set α) : nhdsKer s = ↑(upperClosure s) := by
  ext; simp [mem_nhdsKer_iff_specializes, specializes_iff_le]
/-
**Topology.IsUpperSet.nhdsKer_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsUp
perSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : TopologicalSpace α] [Topolo
gy.IsUpperSet α] (a : α),   nhdsKer {a} = Set.Ici a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsUpperSet.nhdsKer_eq_upperClosure`：nhdsKer_eq_upperClosure (s 
: Set α) : nhdsKer s = ↑(upperClosure s)
· 使用定理 `upperClosure_singleton`：upperClosure_singleton (a : α) : upperClosure ({
a} : Set α) = UpperSet.Ici a
· 使用定理 `UpperSet.coe_Ici`：coe_Ici (a : α) : ↑(Ici a) = Set.Ici a
-/
@[simp] lemma nhdsKer_singleton (a : α) : nhdsKer {a} = Ici a := by
  rw [nhdsKer_eq_upperClosure, upperClosure_singleton, UpperSet.coe_Ici]
/-
**Topology.IsUpperSet.nhds_eq_principal_Ici** 是 Mathlib 中的一个引理，位于命名空间 `Topology.
IsUpperSet`。
形式化陈述：nhds_eq_principal_Ici (a : α) : 𝓝 a = 𝓟 (Ici a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `principal_nhdsKer_singleton`：∀ {α : Type u_3} [inst : TopologicalSpace α
] [AlexandrovDiscrete α] (a : α), Filter.principal (nhdsKer {a}) = nhds a
· 使用定理 `Topology.IsUpperSet.nhdsKer_singleton`：∀ {α : Type u_1} [inst : Preorder
 α] [inst_1 : TopologicalSpace α] [Topology.IsUpperSet α] (a : α),   nhdsKer {a}
 = Set.Ici a
-/
lemma nhds_eq_principal_Ici (a : α) : 𝓝 a = 𝓟 (Ici a) := by
  rw [← principal_nhdsKer_singleton, nhdsKer_singleton]
/-
**Topology.IsUpperSet.nhdsSet_eq_principal_upperClosure** 是 Mathlib 中的一个引理，位于命名空
间 `Topology.IsUpperSet`。
形式化陈述：nhdsSet_eq_principal_upperClosure (s : Set α) : 𝓝ˢ s = 𝓟 ↑(upperClosure s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `principal_nhdsKer`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexand
rovDiscrete α] (s : Set α),   Filter.principal (nhdsKer s) = nhdsSet s
· 使用引理 `Topology.IsUpperSet.nhdsKer_eq_upperClosure`：nhdsKer_eq_upperClosure (s 
: Set α) : nhdsKer s = ↑(upperClosure s)
-/
lemma nhdsSet_eq_principal_upperClosure (s : Set α) : 𝓝ˢ s = 𝓟 ↑(upperClosure s) := by
  rw [← principal_nhdsKer, nhdsKer_eq_upperClosure]

end Preorder

/-
**Topology.IsUpperSet._root_.Topology.isUpperSet_iff_nhds** 是 Mathlib 中的一个引理，位于命
名空间 `Topology.IsUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.Topology.isUpperSet_iff_nhds {α : Type*} [TopologicalSpace α] [Preorder α] :
    Topology.IsUpperSet α ↔ (∀ a : α, 𝓝 a = 𝓟 (Ici a)) where
  mp _ a := nhds_eq_principal_Ici a
  mpr hα := ⟨by simp [TopologicalSpace.ext_iff_nhds, hα, nhds_eq_principal_Ici]⟩
/-
**Topology.IsUpperSet.** 是 Mathlib 中的一个实例，位于命名空间 `Topology.IsUpperSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Topology.IsUpperSet Prop := by
  simp [Topology.isUpperSet_iff_nhds, Prop.forall]

section maps

variable [Preorder α] [Preorder β]

open Topology

/-
**Topology.IsUpperSet.monotone_iff_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.IsUpperSet`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : TopologicalSpace α]   [inst_3 : TopologicalSpace β] [Topology.IsUpperS
et α] [Topology.IsUpperSet β] {f : α → β}, Monotone f ↔ Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsUpperSet.preimage`：IsUpperSet.preimage (hs : IsUpperSet s) {f : β -> α
} (hf : Monotone f) : IsUpperSet (f ⁻¹' s : Set β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `Topology.IsUpperSet.closure_singleton`：∀ {α : Type u_1} [inst : Preorder
 α] [inst_1 : TopologicalSpace α] [Topology.IsUpperSet α] {a : α},   closure {a}
 = Set.Iic a
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
protected lemma monotone_iff_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsUpperSet α] [Topology.IsUpperSet β] {f : α → β} : Monotone f ↔ Continuous f := by
  constructor
  · intro hf
    simp_rw [continuous_def, isOpen_iff_isUpperSet]
    exact fun _ hs ↦ IsUpperSet.preimage hs hf
  · intro hf a b hab
    rw [← mem_Iic, ← closure_singleton] at hab ⊢
    apply Continuous.closure_preimage_subset hf {f b}
    apply mem_of_mem_of_subset hab
    apply closure_mono
    rw [singleton_subset_iff, mem_preimage, mem_singleton_iff]
/-
**Topology.IsUpperSet.monotone_to_upperTopology_continuous** 是 Mathlib 中的一个引理，位于
命名空间 `Topology.IsUpperSet`。
形式化陈述：monotone_to_upperTopology_continuous [TopologicalSpace α] [TopologicalSpac
e β] [Topology.IsUpperSet α] [IsUpper β] {f : α -> β} (hf : Monotone f) : Contin
uous f
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsUpperSet.preimage`：IsUpperSet.preimage (hs : IsUpperSet s) {f : β -> α
} (hf : Monotone f) : IsUpperSet (f ⁻¹' s : Set β)
· 使用定理 `Topology.IsUpper.isUpperSet_of_isOpen`：isUpperSet_of_isOpen (h : IsOpen 
s) : IsUpperSet s
-/
lemma monotone_to_upperTopology_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsUpperSet α] [IsUpper β] {f : α → β} (hf : Monotone f) : Continuous f := by
  simp_rw [continuous_def, isOpen_iff_isUpperSet]
  intro s hs
  exact (IsUpper.isUpperSet_of_isOpen hs).preimage hf
/-
**Topology.IsUpperSet.upperSet_le_upper** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsUp
perSet`。
形式化陈述：upperSet_le_upper {t₁ t₂ : TopologicalSpace α} [@Topology.IsUpperSet α t₁ 
_] [@Topology.IsUpper α t₂ _] : t₁ <= t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsUpperSet.isOpen_iff_isUpperSet`：isOpen_iff_isUpperSet : IsOpe
n s ↔ IsUpperSet s
· 使用定理 `Topology.IsUpper.isUpperSet_of_isOpen`：isUpperSet_of_isOpen (h : IsOpen 
s) : IsUpperSet s
-/
lemma upperSet_le_upper {t₁ t₂ : TopologicalSpace α} [@Topology.IsUpperSet α t₁ _]
    [@Topology.IsUpper α t₂ _] : t₁ ≤ t₂ := fun s hs => by
  rw [@isOpen_iff_isUpperSet α _ t₁]
  exact IsUpper.isUpperSet_of_isOpen hs

end maps

end IsUpperSet

namespace IsLowerSet

section Preorder

variable (α)
variable [Preorder α] [TopologicalSpace α] [Topology.IsLowerSet α] {s : Set α}

/-
**Topology.IsLowerSet.topology_eq** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsLowerSet
`。
形式化陈述：topology_eq : ‹_› = lowerSet α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsLowerSet.topology_eq_lowerSetTopology`：∀ {α : Type u_4} {t : 
TopologicalSpace α} {inst : Preorder α} [self : Topology.IsLowerSet α], t = Topo
logy.lowerSet α
-/
lemma topology_eq : ‹_› = lowerSet α := topology_eq_lowerSetTopology

variable {α}

set_option backward.isDefEq.respectTransparency false in
/-
**Topology.IsLowerSet._root_.OrderDual.instIsUpperSet** 是 Mathlib 中的一个实例，位于命名空间 
`Topology.IsLowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.OrderDual.instIsUpperSet : Topology.IsUpperSet αᵒᵈ where
  topology_eq_upperSetTopology := by ext; rw [IsLowerSet.topology_eq α]

/-- If `α` is equipped with the lower set topology, then it is homeomorphic to `WithLowerSet α`. -/
/-
**Topology.IsLowerSet.WithLowerSetHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Topology
.IsLowerSet`。
形式化陈述：WithLowerSetHomeomorph : WithLowerSet α ≃ₜ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is equipped with the lower set topology, then it is homeomorphic to `With
LowerSet α`.
-/
def WithLowerSetHomeomorph : WithLowerSet α ≃ₜ α :=
  WithLowerSet.ofLowerSet.toHomeomorphOfIsInducing ⟨topology_eq α ▸ induced_id.symm⟩
/-
**Topology.IsLowerSet.isOpen_iff_isLowerSet** 是 Mathlib 中的一个引理，位于命名空间 `Topology.
IsLowerSet`。
形式化陈述：isOpen_iff_isLowerSet : IsOpen s ↔ IsLowerSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsLowerSet.topology_eq`：topology_eq : ‹_› = lowerSet α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isOpen_iff_isLowerSet : IsOpen s ↔ IsLowerSet s := by rw [topology_eq α]; rfl
/-
**Topology.IsLowerSet.toAlexandrovDiscrete** 是 Mathlib 中的一个实例，位于命名空间 `Topology.I
sLowerSet`。
形式化陈述：toAlexandrovDiscrete : AlexandrovDiscrete α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderDual.instIsUpperSet`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 :
 TopologicalSpace α] [Topology.IsLowerSet α], Topology.IsUpperSet αᵒᵈ
-/
instance toAlexandrovDiscrete : AlexandrovDiscrete α := IsUpperSet.toAlexandrovDiscrete (α := αᵒᵈ)
/-
**Topology.IsLowerSet.isClosed_iff_isUpper** 是 Mathlib 中的一个引理，位于命名空间 `Topology.I
sLowerSet`。
形式化陈述：isClosed_iff_isUpper : IsClosed s ↔ IsUpperSet s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用引理 `Topology.IsLowerSet.isOpen_iff_isLowerSet`：isOpen_iff_isLowerSet : IsOpe
n s ↔ IsLowerSet s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isUpperSet_compl`：isUpperSet_compl : IsUpperSet sᶜ ↔ IsLowerSet s
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClosed_iff_isUpper : IsClosed s ↔ IsUpperSet s := by
  rw [← isOpen_compl_iff, isOpen_iff_isLowerSet, isUpperSet_compl.symm, compl_compl]
/-
**Topology.IsLowerSet.closure_eq_upperClosure** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
y.IsLowerSet`。
形式化陈述：closure_eq_upperClosure {s : Set α} : closure s = upperClosure s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsUpperSet.closure_eq_lowerClosure`：closure_eq_lowerClosure {s 
: Set α} : closure s = lowerClosure s
· 使用定理 `OrderDual.instIsUpperSet`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 :
 TopologicalSpace α] [Topology.IsLowerSet α], Topology.IsUpperSet αᵒᵈ
-/
lemma closure_eq_upperClosure {s : Set α} : closure s = upperClosure s :=
  IsUpperSet.closure_eq_lowerClosure (α := αᵒᵈ)

/--
The closure of a singleton `{a}` in the lower set topology is the right-closed left-infinite
interval $(-∞,a]$.
-/
/-
**Topology.IsLowerSet.closure_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsLo
werSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : TopologicalSpace α] [Topolo
gy.IsLowerSet α] {a : α},   closure {a} = Set.Ici a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsLowerSet.closure_eq_upperClosure`：closure_eq_upperClosure {s 
: Set α} : closure s = upperClosure s
· 使用定理 `upperClosure_singleton`：upperClosure_singleton (a : α) : upperClosure ({
a} : Set α) = UpperSet.Ici a

--- 原说明 ---
The closure of a singleton `{a}` in the lower set topology is the right-closed l
eft-infinite
interval $(-∞,a]$.
-/
@[simp] lemma closure_singleton {a : α} : closure {a} = Ici a := by
  rw [closure_eq_upperClosure, upperClosure_singleton]
  rfl
/-
**Topology.IsLowerSet.specializes_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsL
owerSet`。
形式化陈述：specializes_iff_le {a b : α} : a ⤳ b ↔ a <= b
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
· 使用定理 `Topology.IsLowerSet.closure_singleton`：∀ {α : Type u_1} [inst : Preorder
 α] [inst_1 : TopologicalSpace α] [Topology.IsLowerSet α] {a : α},   closure {a}
 = Set.Ici a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma specializes_iff_le {a b : α} : a ⤳ b ↔ a ≤ b := by
  simp only [specializes_iff_closure_subset, closure_singleton, Ici_subset_Ici]
/-
**Topology.IsLowerSet.nhdsKer_eq_lowerClosure** 是 Mathlib 中的一个引理，位于命名空间 `Topolog
y.IsLowerSet`。
形式化陈述：nhdsKer_eq_lowerClosure (s : Set α) : nhdsKer s = ↑(lowerClosure s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nhdsKer_eq_lowerClosure (s : Set α) : nhdsKer s = ↑(lowerClosure s) := by
  ext; simp [mem_nhdsKer_iff_specializes, specializes_iff_le]
/-
**Topology.IsLowerSet.nhdsKer_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Topology.IsLo
werSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : TopologicalSpace α] [Topolo
gy.IsLowerSet α] (a : α),   nhdsKer {a} = Set.Iic a
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsLowerSet.nhdsKer_eq_lowerClosure`：nhdsKer_eq_lowerClosure (s 
: Set α) : nhdsKer s = ↑(lowerClosure s)
· 使用定理 `lowerClosure_singleton`：∀ {α : Type u_1} [inst : Preorder α] (a : α), lo
werClosure {a} = LowerSet.Iic a
· 使用定理 `LowerSet.coe_Iic`：∀ {α : Type u_1} [inst : Preorder α] (a : α), ↑(LowerS
et.Iic a) = Set.Iic a
-/
@[simp] lemma nhdsKer_singleton (a : α) : nhdsKer {a} = Iic a := by
  rw [nhdsKer_eq_lowerClosure, lowerClosure_singleton, LowerSet.coe_Iic]
/-
**Topology.IsLowerSet.nhds_eq_principal_Iic** 是 Mathlib 中的一个引理，位于命名空间 `Topology.
IsLowerSet`。
形式化陈述：nhds_eq_principal_Iic (a : α) : 𝓝 a = 𝓟 (Iic a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `principal_nhdsKer_singleton`：∀ {α : Type u_3} [inst : TopologicalSpace α
] [AlexandrovDiscrete α] (a : α), Filter.principal (nhdsKer {a}) = nhds a
· 使用定理 `Topology.IsLowerSet.nhdsKer_singleton`：∀ {α : Type u_1} [inst : Preorder
 α] [inst_1 : TopologicalSpace α] [Topology.IsLowerSet α] (a : α),   nhdsKer {a}
 = Set.Iic a
-/
lemma nhds_eq_principal_Iic (a : α) : 𝓝 a = 𝓟 (Iic a) := by
  rw [← principal_nhdsKer_singleton, nhdsKer_singleton]
/-
**Topology.IsLowerSet.nhdsSet_eq_principal_lowerClosure** 是 Mathlib 中的一个引理，位于命名空
间 `Topology.IsLowerSet`。
形式化陈述：nhdsSet_eq_principal_lowerClosure (s : Set α) : 𝓝ˢ s = 𝓟 ↑(lowerClosure s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `principal_nhdsKer`：∀ {α : Type u_3} [inst : TopologicalSpace α] [Alexand
rovDiscrete α] (s : Set α),   Filter.principal (nhdsKer s) = nhdsSet s
· 使用引理 `Topology.IsLowerSet.nhdsKer_eq_lowerClosure`：nhdsKer_eq_lowerClosure (s 
: Set α) : nhdsKer s = ↑(lowerClosure s)
-/
lemma nhdsSet_eq_principal_lowerClosure (s : Set α) : 𝓝ˢ s = 𝓟 ↑(lowerClosure s) := by
  rw [← principal_nhdsKer, nhdsKer_eq_lowerClosure]

end Preorder

/-
**Topology.IsLowerSet._root_.Topology.isLowerSet_iff_nhds** 是 Mathlib 中的一个引理，位于命
名空间 `Topology.IsLowerSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.Topology.isLowerSet_iff_nhds {α : Type*} [TopologicalSpace α] [Preorder α] :
    Topology.IsLowerSet α ↔ (∀ a : α, 𝓝 a = 𝓟 (Iic a)) where
  mp _ a := nhds_eq_principal_Iic a
  mpr hα := ⟨by simp [TopologicalSpace.ext_iff_nhds, hα, nhds_eq_principal_Iic]⟩

section maps

variable [Preorder α] [Preorder β]

open Topology
open OrderDual

/-
**Topology.IsLowerSet.monotone_iff_continuous** 是 Mathlib 中的一个定理，位于命名空间 `Topolog
y.IsLowerSet`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : TopologicalSpace α]   [inst_3 : TopologicalSpace β] [Topology.IsLowerS
et α] [Topology.IsLowerSet β] {f : α → β}, Monotone f ↔ Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `monotone_dual_iff`：monotone_dual_iff : Monotone (toDual ∘ f ∘ ofDual : α
ᵒᵈ -> βᵒᵈ) ↔ Monotone f
· 使用定理 `Topology.IsUpperSet.monotone_iff_continuous`：∀ {α : Type u_1} {β : Type 
u_2} [inst : Preorder α] [inst_1 : Preorder β] [inst_2 : TopologicalSpace α]   [
inst_3 : TopologicalSpace β] [Top…
· 使用定理 `OrderDual.instIsUpperSet`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 :
 TopologicalSpace α] [Topology.IsLowerSet α], Topology.IsUpperSet αᵒᵈ
-/
protected lemma monotone_iff_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsLowerSet α] [Topology.IsLowerSet β] {f : α → β} : Monotone f ↔ Continuous f := by
  rw [← monotone_dual_iff]
  exact IsUpperSet.monotone_iff_continuous (α := αᵒᵈ) (β := βᵒᵈ)
    (f := (toDual ∘ f ∘ ofDual : αᵒᵈ → βᵒᵈ))
/-
**Topology.IsLowerSet.monotone_to_lowerTopology_continuous** 是 Mathlib 中的一个引理，位于
命名空间 `Topology.IsLowerSet`。
形式化陈述：monotone_to_lowerTopology_continuous [TopologicalSpace α] [TopologicalSpac
e β] [Topology.IsLowerSet α] [IsLower β] {f : α -> β} (hf : Monotone f) : Contin
uous f
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsUpperSet.monotone_to_upperTopology_continuous`：monotone_to_up
perTopology_continuous [TopologicalSpace α] [TopologicalSpace β] [Topology.IsUpp
erSet α] [IsUpper β] {f : α -> β} (hf : Monoto…
· 使用定理 `OrderDual.instIsUpperSet`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 :
 TopologicalSpace α] [Topology.IsLowerSet α], Topology.IsUpperSet αᵒᵈ
· 使用定理 `OrderDual.instIsUpper`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : To
pologicalSpace α] [Topology.IsLower α], Topology.IsUpper αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
lemma monotone_to_lowerTopology_continuous [TopologicalSpace α] [TopologicalSpace β]
    [Topology.IsLowerSet α] [IsLower β] {f : α → β} (hf : Monotone f) : Continuous f :=
  IsUpperSet.monotone_to_upperTopology_continuous (α := αᵒᵈ) (β := βᵒᵈ) hf.dual
/-
**Topology.IsLowerSet.lowerSet_le_lower** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsLo
werSet`。
形式化陈述：lowerSet_le_lower {t₁ t₂ : TopologicalSpace α} [@Topology.IsLowerSet α t₁ 
_] [@IsLower α t₂ _] : t₁ <= t₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsLowerSet.isOpen_iff_isLowerSet`：isOpen_iff_isLowerSet : IsOpe
n s ↔ IsLowerSet s
· 使用定理 `Topology.IsLower.isLowerSet_of_isOpen`：isLowerSet_of_isOpen (h : IsOpen 
s) : IsLowerSet s
-/
lemma lowerSet_le_lower {t₁ t₂ : TopologicalSpace α} [@Topology.IsLowerSet α t₁ _]
    [@IsLower α t₂ _] : t₁ ≤ t₂ := fun s hs => by
  rw [@isOpen_iff_isLowerSet α _ t₁]
  exact IsLower.isLowerSet_of_isOpen hs

end maps

end IsLowerSet

/-
**Topology.isUpperSet_orderDual** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：isUpperSet_orderDual [Preorder α] [TopologicalSpace α] : Topology.IsUpperS
et αᵒᵈ ↔ Topology.IsLowerSet α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderDual.instIsLowerSet`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 :
 TopologicalSpace α] [Topology.IsUpperSet α], Topology.IsLowerSet αᵒᵈ
· 使用定理 `OrderDual.instIsUpperSet`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 :
 TopologicalSpace α] [Topology.IsLowerSet α], Topology.IsUpperSet αᵒᵈ
-/
lemma isUpperSet_orderDual [Preorder α] [TopologicalSpace α] :
    Topology.IsUpperSet αᵒᵈ ↔ Topology.IsLowerSet α := by
  constructor
  · apply OrderDual.instIsLowerSet
  · apply OrderDual.instIsUpperSet
/-
**Topology.isLowerSet_orderDual** 是 Mathlib 中的一个引理，位于命名空间 `Topology`。
形式化陈述：isLowerSet_orderDual [Preorder α] [TopologicalSpace α] : Topology.IsLowerS
et αᵒᵈ ↔ Topology.IsUpperSet α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.isUpperSet_orderDual`：isUpperSet_orderDual [Preorder α] [Topolo
gicalSpace α] : Topology.IsUpperSet αᵒᵈ ↔ Topology.IsLowerSet α
-/
lemma isLowerSet_orderDual [Preorder α] [TopologicalSpace α] :
    Topology.IsLowerSet αᵒᵈ ↔ Topology.IsUpperSet α := isUpperSet_orderDual.symm

namespace WithUpperSet
variable [Preorder α] [Preorder β] [Preorder γ]

/-- A monotone map between preorders spaces induces a continuous map between themselves considered
with the upper set topology. -/
/-
**Topology.WithUpperSet.map** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithUpperSet`。
形式化陈述：map (f : α ->o β) : C(WithUpperSet α, WithUpperSet β) where toFun
参数：f : α ->o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monotone map between preorders spaces induces a continuous map between themsel
ves considered
with the upper set topology.
-/
def map (f : α →o β) : C(WithUpperSet α, WithUpperSet β) where
  toFun := toUpperSet ∘ f ∘ ofUpperSet
  continuous_toFun := continuous_def.2 fun _s hs ↦ IsUpperSet.preimage hs f.monotone
/-
**Topology.WithUpperSet.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Topology.WithUpperSet`
。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α], Topology.WithUpperSet.map OrderHom.i
d = ContinuousMap.id (Topology.WithUpperSet α)
参数：Topology.WithUpperSet α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_id : map (OrderHom.id : α →o α) = ContinuousMap.id _ := rfl
/-
**Topology.WithUpperSet.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.WithUpperSe
t`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Preorder α] [inst_1
 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α →o β),   Topology.Wit
hUpperSet.map (g.comp f) = (Topology.WithUpperSet.map g).comp (Topology.WithUppe
rSet.map f)
参数：g : β →o γ；f : α →o β；g.comp f；Topology.WithUpperSet.map g；Topology.WithUpper
Set.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_comp (g : β →o γ) (f : α →o β) : map (g.comp f) = (map g).comp (map f) := rfl
/-
**Topology.WithUpperSet.toUpperSet_specializes_toUpperSet** 是 Mathlib 中的一个定理，位于命
名空间 `Topology.WithUpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α},   Topology.WithUpperSet.to
UpperSet a ⤳ Topology.WithUpperSet.toUpperSet b ↔ b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Topology.IsUpperSet.closure_singleton`：∀ {α : Type u_1} [inst : Preorder
 α] [inst_1 : TopologicalSpace α] [Topology.IsUpperSet α] {a : α},   closure {a}
 = Set.Iic a
· 使用定理 `Topology.instIsUpperSetWithUpperSet`：∀ {α : Type u_1} [inst : Preorder α
], Topology.IsUpperSet (Topology.WithUpperSet α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toUpperSet_specializes_toUpperSet {a b : α} :
    toUpperSet a ⤳ toUpperSet b ↔ b ≤ a := by
  simp_rw [specializes_iff_closure_subset, IsUpperSet.closure_singleton, Iic_subset_Iic,
    toUpperSet_le_iff]
/-
**Topology.WithUpperSet.ofUpperSet_le_ofUpperSet** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.WithUpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : Topology.WithUpperSet α},   To
pology.WithUpperSet.ofUpperSet a ≤ Topology.WithUpperSet.ofUpperSet b ↔ b ⤳ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.WithUpperSet.toUpperSet_specializes_toUpperSet`：∀ {α : Type u_1
} [inst : Preorder α] {a b : α},   Topology.WithUpperSet.toUpperSet a ⤳ Topology
.WithUpperSet.toUpperSet b ↔ b ≤ a
-/
@[simp] lemma ofUpperSet_le_ofUpperSet {a b : WithUpperSet α} :
    ofUpperSet a ≤ ofUpperSet b ↔ b ⤳ a := toUpperSet_specializes_toUpperSet.symm
/-
**Topology.WithUpperSet.isUpperSet_toUpperSet_preimage** 是 Mathlib 中的一个定理，位于命名空间
 `Topology.WithUpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set (Topology.WithUpperSet α)}, 
  IsUpperSet (⇑Topology.WithUpperSet.toUpperSet ⁻¹' s) ↔ IsOpen s
参数：Topology.WithUpperSet α；⇑Topology.WithUpperSet.toUpperSet ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isUpperSet_toUpperSet_preimage {s : Set (WithUpperSet α)} :
    IsUpperSet (toUpperSet ⁻¹' s) ↔ IsOpen s := Iff.rfl
/-
**Topology.WithUpperSet.isOpen_ofUpperSet_preimage** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.WithUpperSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, IsOpen (⇑Topology.WithUp
perSet.ofUpperSet ⁻¹' s) ↔ IsUpperSet s
参数：⇑Topology.WithUpperSet.ofUpperSet ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.WithUpperSet.isUpperSet_toUpperSet_preimage`：∀ {α : Type u_1} [
inst : Preorder α] {s : Set (Topology.WithUpperSet α)},   IsUpperSet (⇑Topology.
WithUpperSet.toUpperSet ⁻¹' s) ↔ IsOpen s
-/
@[simp] lemma isOpen_ofUpperSet_preimage {s : Set α} :
    IsOpen (ofUpperSet ⁻¹' s) ↔ IsUpperSet s := isUpperSet_toUpperSet_preimage.symm

end WithUpperSet

namespace WithLowerSet
variable [Preorder α] [Preorder β] [Preorder γ]

/-- A monotone map between preorders spaces induces a continuous map between themselves considered
with the lower set topology. -/
/-
**Topology.WithLowerSet.map** 是 Mathlib 中的一个定义，位于命名空间 `Topology.WithLowerSet`。
形式化陈述：map (f : α ->o β) : C(WithLowerSet α, WithLowerSet β) where toFun
参数：f : α ->o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monotone map between preorders spaces induces a continuous map between themsel
ves considered
with the lower set topology.
-/
def map (f : α →o β) : C(WithLowerSet α, WithLowerSet β) where
  toFun := toLowerSet ∘ f ∘ ofLowerSet
  continuous_toFun := continuous_def.2 fun _s hs ↦ IsLowerSet.preimage hs f.monotone
/-
**Topology.WithLowerSet.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Topology.WithLowerSet`
。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α], Topology.WithLowerSet.map OrderHom.i
d = ContinuousMap.id (Topology.WithLowerSet α)
参数：Topology.WithLowerSet α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_id : map (OrderHom.id : α →o α) = ContinuousMap.id _ := rfl
/-
**Topology.WithLowerSet.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Topology.WithLowerSe
t`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Preorder α] [inst_1
 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α →o β),   Topology.Wit
hLowerSet.map (g.comp f) = (Topology.WithLowerSet.map g).comp (Topology.WithLowe
rSet.map f)
参数：g : β →o γ；f : α →o β；g.comp f；Topology.WithLowerSet.map g；Topology.WithLower
Set.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_comp (g : β →o γ) (f : α →o β) : map (g.comp f) = (map g).comp (map f) := rfl
/-
**Topology.WithLowerSet.toLowerSet_specializes_toLowerSet** 是 Mathlib 中的一个定理，位于命
名空间 `Topology.WithLowerSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α},   Topology.WithLowerSet.to
LowerSet a ⤳ Topology.WithLowerSet.toLowerSet b ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Topology.IsLowerSet.closure_singleton`：∀ {α : Type u_1} [inst : Preorder
 α] [inst_1 : TopologicalSpace α] [Topology.IsLowerSet α] {a : α},   closure {a}
 = Set.Ici a
· 使用定理 `Topology.instIsLowerSetWithLowerSet`：∀ {α : Type u_1} [inst : Preorder α
], Topology.IsLowerSet (Topology.WithLowerSet α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toLowerSet_specializes_toLowerSet {a b : α} :
    toLowerSet a ⤳ toLowerSet b ↔ a ≤ b := by
  simp_rw [specializes_iff_closure_subset, IsLowerSet.closure_singleton, Ici_subset_Ici,
    toLowerSet_le_iff]
/-
**Topology.WithLowerSet.ofLowerSet_le_ofLowerSet** 是 Mathlib 中的一个定理，位于命名空间 `Topo
logy.WithLowerSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : Topology.WithLowerSet α},   To
pology.WithLowerSet.ofLowerSet a ≤ Topology.WithLowerSet.ofLowerSet b ↔ a ⤳ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.WithLowerSet.toLowerSet_specializes_toLowerSet`：∀ {α : Type u_1
} [inst : Preorder α] {a b : α},   Topology.WithLowerSet.toLowerSet a ⤳ Topology
.WithLowerSet.toLowerSet b ↔ a ≤ b
-/
@[simp] lemma ofLowerSet_le_ofLowerSet {a b : WithLowerSet α} :
    ofLowerSet a ≤ ofLowerSet b ↔ a ⤳ b := toLowerSet_specializes_toLowerSet.symm
/-
**Topology.WithLowerSet.isLowerSet_toLowerSet_preimage** 是 Mathlib 中的一个定理，位于命名空间
 `Topology.WithLowerSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set (Topology.WithLowerSet α)}, 
  IsLowerSet (⇑Topology.WithLowerSet.toLowerSet ⁻¹' s) ↔ IsOpen s
参数：Topology.WithLowerSet α；⇑Topology.WithLowerSet.toLowerSet ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isLowerSet_toLowerSet_preimage {s : Set (WithLowerSet α)} :
    IsLowerSet (toLowerSet ⁻¹' s) ↔ IsOpen s := Iff.rfl
/-
**Topology.WithLowerSet.isOpen_ofLowerSet_preimage** 是 Mathlib 中的一个定理，位于命名空间 `To
pology.WithLowerSet`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, IsOpen (⇑Topology.WithLo
werSet.ofLowerSet ⁻¹' s) ↔ IsLowerSet s
参数：⇑Topology.WithLowerSet.ofLowerSet ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.WithLowerSet.isLowerSet_toLowerSet_preimage`：∀ {α : Type u_1} [
inst : Preorder α] {s : Set (Topology.WithLowerSet α)},   IsLowerSet (⇑Topology.
WithLowerSet.toLowerSet ⁻¹' s) ↔ IsOpen s
-/
@[simp] lemma isOpen_ofLowerSet_preimage {s : Set α} :
    IsOpen (ofLowerSet ⁻¹' s) ↔ IsLowerSet s := isLowerSet_toLowerSet_preimage.symm

end WithLowerSet
end Topology

