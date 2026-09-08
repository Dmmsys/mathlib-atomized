/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.GameAdd
public import Mathlib.SetTheory.ZFC.Cardinal
public import Mathlib.SetTheory.ZFC.Rank

/-!
# Von Neumann ordinals

This file works towards the development of von Neumann ordinals, i.e. transitive sets, well-ordered
under `∈`.

## Definitions

- `ZFSet.IsTransitive` means that every element of a set is a subset.
- `ZFSet.IsOrdinal` means that the set is transitive and well-ordered under `∈`. We show multiple
  equivalences to this definition.
- `Ordinal.toZFSet` converts Lean's type-theoretic ordinals into ZFC ordinals. We prove that these
  two notions are order-isomorphic.
-/

@[expose] public section

universe u

variable {x y z w : ZFSet.{u}}

open Set

namespace ZFSet

/-! ### Transitive sets -/

/-- A transitive set is one where every element is a subset.

This is equivalent to being an infinite-open interval in the transitive closure of membership. -/
/-
**ZFSet.IsTransitive** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
形式化陈述：IsTransitive (x : ZFSet) : Prop
参数：x : ZFSet。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A transitive set is one where every element is a subset.

This is equivalent to being an infinite-open interval in the transitive closure 
of membership.
-/
def IsTransitive (x : ZFSet) : Prop :=
  ∀ y ∈ x, y ⊆ x

@[simp]
/-
**ZFSet.isTransitive_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：isTransitive_empty : IsTransitive ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.notMem_empty`：notMem_empty (x) : x ∉ (∅ : ZFSet.{u})
-/
theorem isTransitive_empty : IsTransitive ∅ := fun y hy => (notMem_empty y hy).elim
/-
**ZFSet.IsTransitive.subset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsTransitive
`。
形式化陈述：∀ {x y : ZFSet.{u}}, x.IsTransitive → y ∈ x → y ⊆ x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsTransitive.subset_of_mem (h : x.IsTransitive) : y ∈ x → y ⊆ x := h y
/-
**ZFSet.isTransitive_iff_mem_trans** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：isTransitive_iff_mem_trans : z.IsTransitive ↔ forall {x y : ZFSet}, x in y
 -> y in z -> x in z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.IsTransitive.subset_of_mem`：∀ {x y : ZFSet.{u}}, x.IsTransitive → 
y ∈ x → y ⊆ x
-/
theorem isTransitive_iff_mem_trans : z.IsTransitive ↔ ∀ {x y : ZFSet}, x ∈ y → y ∈ z → x ∈ z :=
  ⟨fun h _ _ hx hy => h.subset_of_mem hy hx, fun H _ hx _ hy => H hy hx⟩

alias ⟨IsTransitive.mem_trans, _⟩ := isTransitive_iff_mem_trans
/-
**ZFSet.IsTransitive.inter** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsTransitive`。
形式化陈述：∀ {x y : ZFSet.{u}}, x.IsTransitive → y.IsTransitive → (x ∩ y).IsTransitiv
e
参数：x ∩ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.mem_inter`：∀ {x y z : ZFSet.{u}}, z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y
· 使用定理 `ZFSet.IsTransitive.mem_trans`：∀ {z : ZFSet.{u}}, z.IsTransitive → ∀ {x y
 : ZFSet.{u}}, x ∈ y → y ∈ z → x ∈ z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem IsTransitive.inter (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∩ y).IsTransitive := fun z hz w hw => by
  rw [mem_inter] at hz ⊢
  exact ⟨hx.mem_trans hw hz.1, hy.mem_trans hw hz.2⟩

/-- The union of a transitive set is transitive. -/
/-
**ZFSet.IsTransitive.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsTransitive`。
形式化陈述：∀ {x : ZFSet.{u}}, x.IsTransitive → x.sUnion.IsTransitive
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.mem_sUnion`：mem_sUnion {x y : ZFSet.{u}} : y in ⋃₀ x ↔ exists z in
 x, y in z
· 使用定理 `ZFSet.mem_sUnion_of_mem`：mem_sUnion_of_mem {x y z : ZFSet} (hy : y in z)
 (hz : z in x) : y in ⋃₀ x
· 使用定理 `ZFSet.IsTransitive.mem_trans`：∀ {z : ZFSet.{u}}, z.IsTransitive → ∀ {x y
 : ZFSet.{u}}, x ∈ y → y ∈ z → x ∈ z

--- 原说明 ---
The union of a transitive set is transitive.
-/
protected theorem IsTransitive.sUnion (h : x.IsTransitive) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem hz (h.mem_trans hw' hw)

/-- The union of transitive sets is transitive. -/
/-
**ZFSet.IsTransitive.sUnion'** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsTransitive`。
形式化陈述：∀ {x : ZFSet.{u}}, (∀ y ∈ x, y.IsTransitive) → x.sUnion.IsTransitive
参数：∀ y ∈ x, y.IsTransitive。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.mem_sUnion`：mem_sUnion {x y : ZFSet.{u}} : y in ⋃₀ x ↔ exists z in
 x, y in z
· 使用定理 `ZFSet.mem_sUnion_of_mem`：mem_sUnion_of_mem {x y z : ZFSet} (hy : y in z)
 (hz : z in x) : y in ⋃₀ x
· 使用定理 `ZFSet.IsTransitive.mem_trans`：∀ {z : ZFSet.{u}}, z.IsTransitive → ∀ {x y
 : ZFSet.{u}}, x ∈ y → y ∈ z → x ∈ z

--- 原说明 ---
The union of transitive sets is transitive.
-/
theorem IsTransitive.sUnion' (H : ∀ y ∈ x, IsTransitive y) :
    (⋃₀ x : ZFSet).IsTransitive := fun y hy z hz => by
  rcases mem_sUnion.1 hy with ⟨w, hw, hw'⟩
  exact mem_sUnion_of_mem ((H w hw).mem_trans hz hw') hw
/-
**ZFSet.IsTransitive.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsTransitive`。
形式化陈述：∀ {α : Type u_1} [inst : Small.{u, u_1} α] {f : α → ZFSet.{u}},   (∀ (i : 
α), (f i).IsTransitive) → (ZFSet.iUnion fun i => f i).IsTransitive
参数：∀ (i : α), (f i).IsTransitive；ZFSet.iUnion fun i => f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.IsTransitive.sUnion'`：∀ {x : ZFSet.{u}}, (∀ y ∈ x, y.IsTransitive)
 → x.sUnion.IsTransitive
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected theorem IsTransitive.iUnion {α : Type*} [Small.{u} α] {f : α → ZFSet.{u}}
    (hf : ∀ i, (f i).IsTransitive) : (⋃ i, f i).IsTransitive :=
  sUnion' (by simpa)
/-
**ZFSet.IsTransitive.union** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsTransitive`。
形式化陈述：∀ {x y : ZFSet.{u}}, x.IsTransitive → y.IsTransitive → (x ∪ y).IsTransitiv
e
参数：x ∪ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.sUnion_pair`：∀ (x y : ZFSet.{u}), {x, y}.sUnion = x ∪ y
· 使用定理 `ZFSet.IsTransitive.sUnion'`：∀ {x : ZFSet.{u}}, (∀ y ∈ x, y.IsTransitive)
 → x.sUnion.IsTransitive
· 使用定理 `ZFSet.mem_pair`：mem_pair {x y z : ZFSet.{u}} : x in ({y, z} : ZFSet) ↔ x
 = y ∨ x = z
-/
protected theorem IsTransitive.union (hx : x.IsTransitive) (hy : y.IsTransitive) :
    (x ∪ y).IsTransitive := by
  rw [← sUnion_pair]
  apply IsTransitive.sUnion'
  intro
  rw [mem_pair]
  rintro (rfl | rfl)
  assumption'
/-
**ZFSet.IsTransitive.powerset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsTransitive`。
形式化陈述：∀ {x : ZFSet.{u}}, x.IsTransitive → x.powerset.IsTransitive
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.mem_powerset`：mem_powerset {x y : ZFSet.{u}} : y in powerset x ↔ y
 subseteq x
· 使用定理 `ZFSet.IsTransitive.subset_of_mem`：∀ {x y : ZFSet.{u}}, x.IsTransitive → 
y ∈ x → y ⊆ x
-/
protected theorem IsTransitive.powerset (h : x.IsTransitive) : (powerset x).IsTransitive :=
  fun y hy z hz => by
  rw [mem_powerset] at hy ⊢
  exact h.subset_of_mem (hy hz)
/-
**ZFSet.isTransitive_iff_sUnion_subset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：isTransitive_iff_sUnion_subset : x.IsTransitive ↔ (⋃₀ x : ZFSet) subseteq 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.mem_sUnion`：mem_sUnion {x y : ZFSet.{u}} : y in ⋃₀ x ↔ exists z in
 x, y in z
· 使用定理 `ZFSet.IsTransitive.mem_trans`：∀ {z : ZFSet.{u}}, z.IsTransitive → ∀ {x y
 : ZFSet.{u}}, x ∈ y → y ∈ z → x ∈ z
· 使用定理 `ZFSet.mem_sUnion_of_mem`：mem_sUnion_of_mem {x y z : ZFSet} (hy : y in z)
 (hz : z in x) : y in ⋃₀ x
-/
theorem isTransitive_iff_sUnion_subset : x.IsTransitive ↔ (⋃₀ x : ZFSet) ⊆ x := by
  constructor <;>
  intro h y hy
  · obtain ⟨z, hz, hz'⟩ := mem_sUnion.1 hy
    exact h.mem_trans hz' hz
  · exact fun z hz ↦ h <| mem_sUnion_of_mem hz hy

alias ⟨IsTransitive.sUnion_subset, _⟩ := isTransitive_iff_sUnion_subset
/-
**ZFSet.isTransitive_iff_subset_powerset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：isTransitive_iff_subset_powerset : x.IsTransitive ↔ x subseteq powerset x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.mem_powerset`：mem_powerset {x y : ZFSet.{u}} : y in powerset x ↔ y
 subseteq x
· 使用定理 `ZFSet.IsTransitive.subset_of_mem`：∀ {x y : ZFSet.{u}}, x.IsTransitive → 
y ∈ x → y ⊆ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem isTransitive_iff_subset_powerset : x.IsTransitive ↔ x ⊆ powerset x :=
  ⟨fun h _ hy => mem_powerset.2 <| h.subset_of_mem hy, fun H _ hy _ hz => mem_powerset.1 (H hy) hz⟩

alias ⟨IsTransitive.subset_powerset, _⟩ := isTransitive_iff_subset_powerset

/-! ### Ordinals -/

/-- A set `x` is a von Neumann ordinal when it's a transitive set, that's transitive under `∈`. We
prove that this further implies that `x` is well-ordered under `∈` in `isOrdinal_iff_isWellOrder`.

The transitivity condition `a ∈ b → b ∈ c → a ∈ c` can be written without assuming `a ∈ x` and
`b ∈ x`. The lemma `isOrdinal_iff_isTrans` shows this condition is equivalent to the usual one. -/
/-
**ZFSet.IsOrdinal** 是 Mathlib 中的一个归纳类型，位于命名空间 `ZFSet`。
形式化陈述：ZFSet.{u_1} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `x` is a von Neumann ordinal when it's a transitive set, that's transitive
 under `∈`. We
prove that this further implies that `x` is well-ordered under `∈` in `isOrdinal
_iff_isWellOrder`.

The transitivity condition `a ∈ b → b ∈ c → a ∈ c` can be written without assumi
ng `a ∈ x` and
`b ∈ x`. The lemma `isOrdinal_iff_isTrans` shows this condition is equivalent to
 the usual one.
-/
structure IsOrdinal (x : ZFSet) : Prop where
  /-- An ordinal is a transitive set. -/
  isTransitive : x.IsTransitive
  /-- The membership operation within an ordinal is transitive. -/
  mem_trans' {y z w : ZFSet} : y ∈ z → z ∈ w → w ∈ x → y ∈ w

namespace IsOrdinal

/-
**ZFSet.IsOrdinal.subset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：subset_of_mem (h : x.IsOrdinal) : y in x -> y subseteq x
参数：h : x.IsOrdinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.IsTransitive.subset_of_mem`：∀ {x y : ZFSet.{u}}, x.IsTransitive → 
y ∈ x → y ⊆ x
· 使用定理 `ZFSet.IsOrdinal.isTransitive`：∀ {x : ZFSet.{u_1}}, x.IsOrdinal → x.IsTra
nsitive
-/
theorem subset_of_mem (h : x.IsOrdinal) : y ∈ x → y ⊆ x :=
  h.isTransitive.subset_of_mem
/-
**ZFSet.IsOrdinal.mem_trans** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：mem_trans (h : z.IsOrdinal) : x in y -> y in z -> x in z
参数：h : z.IsOrdinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.IsTransitive.mem_trans`：∀ {z : ZFSet.{u}}, z.IsTransitive → ∀ {x y
 : ZFSet.{u}}, x ∈ y → y ∈ z → x ∈ z
· 使用定理 `ZFSet.IsOrdinal.isTransitive`：∀ {x : ZFSet.{u_1}}, x.IsOrdinal → x.IsTra
nsitive
-/
theorem mem_trans (h : z.IsOrdinal) : x ∈ y → y ∈ z → x ∈ z :=
  h.isTransitive.mem_trans
/-
**ZFSet.IsOrdinal.isTrans** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：∀ {x : ZFSet.{u}}, x.IsOrdinal → IsTrans (↥x) (Subrel (fun x1 x2 => x1 ∈ x
2) fun x_1 => x_1 ∈ x)
参数：↥x；Subrel (fun x1 x2 => x1 ∈ x2) fun x_1 => x_1 ∈ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.IsOrdinal.mem_trans'`：∀ {x : ZFSet.{u_1}}, x.IsOrdinal → ∀ {y z w 
: ZFSet.{u_1}}, y ∈ z → z ∈ w → w ∈ x → y ∈ w
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
protected theorem isTrans (h : x.IsOrdinal) : IsTrans _ (Subrel (· ∈ ·) (· ∈ x)) :=
  ⟨fun _ _ c hab hbc => h.mem_trans' hab hbc c.2⟩

/-- The simplified form of transitivity used within `IsOrdinal` yields an equivalent definition to
the standard one. -/
/-
**ZFSet.IsOrdinal._root_.ZFSet.isOrdinal_iff_isTrans** 是 Mathlib 中的一个定理，位于命名空间 `
ZFSet.IsOrdinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The simplified form of transitivity used within `IsOrdinal` yields an equivalent
 definition to
the standard one.
-/
theorem _root_.ZFSet.isOrdinal_iff_isTrans :
    x.IsOrdinal ↔ x.IsTransitive ∧ IsTrans _ (Subrel (· ∈ ·) (· ∈ x)) where
  mp h := ⟨h.isTransitive, h.isTrans⟩
  mpr := by
    rintro ⟨h₁, ⟨h₂⟩⟩
    refine ⟨h₁, fun {y z w} hyz hzw hwx ↦ ?_⟩
    have hzx := h₁.mem_trans hzw hwx
    exact h₂ ⟨y, h₁.mem_trans hyz hzx⟩ ⟨z, hzx⟩ ⟨w, hwx⟩ hyz hzw
/-
**ZFSet.IsOrdinal.mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：∀ {x y : ZFSet.{u}}, x.IsOrdinal → y ∈ x → y.IsOrdinal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.IsOrdinal.isTrans`：∀ {x : ZFSet.{u}}, x.IsOrdinal → IsTrans (↥x) (
Subrel (fun x1 x2 => x1 ∈ x2) fun x_1 => x_1 ∈ x)
· 使用定理 `ZFSet.IsOrdinal.subset_of_mem`：subset_of_mem (h : x.IsOrdinal) : y in x 
-> y subseteq x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZFSet.isOrdinal_iff_isTrans`：∀ {x : ZFSet.{u}}, x.IsOrdinal ↔ x.IsTransi
tive ∧ IsTrans (↥x) (Subrel (fun x1 x2 => x1 ∈ x2) fun x_1 => x_1 ∈ x)
· 使用定理 `ZFSet.IsOrdinal.mem_trans'`：∀ {x : ZFSet.{u_1}}, x.IsOrdinal → ∀ {y z w 
: ZFSet.{u_1}}, y ∈ z → z ∈ w → w ∈ x → y ∈ w
· 使用定理 `RelEmbedding.isTrans`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
 {s : β → β → Prop} (x : r ↪r s) [IsTrans β s], IsTrans α r
-/
protected theorem mem (hx : x.IsOrdinal) (hy : y ∈ x) : y.IsOrdinal :=
  have := hx.isTrans
  let f : _ ↪r Subrel (· ∈ ·) (· ∈ x) := Subrel.inclusionEmbedding (· ∈ ·) (hx.subset_of_mem hy)
  isOrdinal_iff_isTrans.2 ⟨fun _ hz _ ha ↦ hx.mem_trans' ha hz hy, f.isTrans⟩

/-- An ordinal is a transitive set of transitive sets. -/
/-
**ZFSet.IsOrdinal._root_.ZFSet.isOrdinal_iff_forall_mem_isTransitive** 是 Mathlib
 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordinal is a transitive set of transitive sets.
-/
theorem _root_.ZFSet.isOrdinal_iff_forall_mem_isTransitive :
    x.IsOrdinal ↔ x.IsTransitive ∧ ∀ y ∈ x, y.IsTransitive where
  mp h := ⟨h.isTransitive, fun _ hy ↦ (h.mem hy).isTransitive⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun hyz hzw hwx ↦ (h₂ _ hwx).mem_trans hyz hzw⟩

/-- An ordinal is a transitive set of ordinals. -/
/-
**ZFSet.IsOrdinal._root_.ZFSet.isOrdinal_iff_forall_mem_isOrdinal** 是 Mathlib 中的
一个定理，位于命名空间 `ZFSet.IsOrdinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordinal is a transitive set of ordinals.
-/
theorem _root_.ZFSet.isOrdinal_iff_forall_mem_isOrdinal :
    x.IsOrdinal ↔ x.IsTransitive ∧ ∀ y ∈ x, y.IsOrdinal where
  mp h := ⟨h.isTransitive, fun _ ↦ h.mem⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ isOrdinal_iff_forall_mem_isTransitive.2
    ⟨h₁, fun y hy ↦ (h₂ y hy).isTransitive⟩
/-
**ZFSet.IsOrdinal.subset_iff_eq_or_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdina
l`。
形式化陈述：subset_iff_eq_or_mem (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x subseteq y 
↔ x = y ∨ x in y
参数：hx : x.IsOrdinal；hy : y.IsOrdinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.mem_wf`：mem_wf : @WellFounded ZFSet (· in ·)
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_nonempty`：sdiff_nonempty {s t : Set α} : (s \ t).Nonempty ↔ ¬s
 subseteq t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ZFSet.IsOrdinal.mem_trans`：mem_trans (h : z.IsOrdinal) : x in y -> y in 
z -> x in z
· 使用定理 `Sym2.GameAdd.fst_snd`：∀ {α : Type u_1} {rα : α → α → Prop} {a₁ a₂ b : α}
, rα a₁ a₂ → Sym2.GameAdd rα s(a₁, b) s(b, a₂)
· 使用定理 `ZFSet.IsOrdinal.mem`：∀ {x y : ZFSet.{u}}, x.IsOrdinal → y ∈ x → y.IsOrdi
nal
· 使用定理 `Set.notMem_of_mem_sdiff`：notMem_of_mem_sdiff {s t : Set α} {x : α} (h : 
x in s \ t) : x ∉ t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ZFSet.IsOrdinal.subset_of_mem`：subset_of_mem (h : x.IsOrdinal) : y in x 
-> y subseteq x
-/
theorem subset_iff_eq_or_mem (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ⊆ y ↔ x = y ∨ x ∈ y := by
  constructor
  · revert hx hy
    refine Sym2.GameAdd.recursion mem_wf ?_ x y
    intro x y IH hx hy hxy
    by_cases hyx : y ⊆ x
    · exact Or.inl (subset_antisymm hxy hyx)
    · obtain ⟨m, hm, hm'⟩ := mem_wf.has_min (y \ x) (Set.sdiff_nonempty.2 hyx)
      have hmy : m ∈ y := by simp only [Set.mem_sdiff, SetLike.mem_coe] at hm; exact hm.1
      have hmx : m ⊆ x := by
        intro z hzm
        by_contra hzx
        exact hm' _ ⟨hy.mem_trans hzm hmy, hzx⟩ hzm
      obtain rfl | H := IH m x (Sym2.GameAdd.fst_snd hmy) (hy.mem hmy) hx hmx
      · exact Or.inr hmy
      · cases Set.notMem_of_mem_sdiff hm H
  · rintro (rfl | h)
    · rfl
    · exact hy.subset_of_mem h

alias ⟨eq_or_mem_of_subset, _⟩ := subset_iff_eq_or_mem
/-
**ZFSet.IsOrdinal.mem_of_subset_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdina
l`。
形式化陈述：mem_of_subset_of_mem (h : x.IsOrdinal) (hz : z.IsOrdinal) (hx : x subseteq
 y) (hy : y in z) : x in z
参数：h : x.IsOrdinal；hz : z.IsOrdinal；hx : x subseteq y；hy : y in z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.IsOrdinal.eq_or_mem_of_subset`：∀ {x y : ZFSet.{u}}, x.IsOrdinal → 
y.IsOrdinal → x ⊆ y → x = y ∨ x ∈ y
· 使用定理 `ZFSet.IsOrdinal.mem`：∀ {x y : ZFSet.{u}}, x.IsOrdinal → y ∈ x → y.IsOrdi
nal
· 使用定理 `ZFSet.IsOrdinal.mem_trans`：mem_trans (h : z.IsOrdinal) : x in y -> y in 
z -> x in z
-/
theorem mem_of_subset_of_mem (h : x.IsOrdinal) (hz : z.IsOrdinal) (hx : x ⊆ y) (hy : y ∈ z) :
    x ∈ z := by
  obtain rfl | hx := h.eq_or_mem_of_subset (hz.mem hy) hx
  · exact hy
  · exact hz.mem_trans hx hy
/-
**ZFSet.IsOrdinal.notMem_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：notMem_iff_subset (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ∉ y ↔ y subset
eq x
参数：hx : x.IsOrdinal；hy : y.IsOrdinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.mem_wf`：mem_wf : @WellFounded ZFSet (· in ·)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ZFSet.IsOrdinal.mem_of_subset_of_mem`：mem_of_subset_of_mem (h : x.IsOrdi
nal) (hz : z.IsOrdinal) (hx : x subseteq y) (hy : y in z) : x in z
· 使用定理 `Sym2.GameAdd.fst_snd`：∀ {α : Type u_1} {rα : α → α → Prop} {a₁ a₂ b : α}
, rα a₁ a₂ → Sym2.GameAdd rα s(a₁, b) s(b, a₂)
· 使用定理 `ZFSet.IsOrdinal.mem`：∀ {x y : ZFSet.{u}}, x.IsOrdinal → y ∈ x → y.IsOrdi
nal
· 使用定理 `ZFSet.mem_irrefl`：mem_irrefl (x : ZFSet) : x ∉ x
-/
theorem notMem_iff_subset (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ∉ y ↔ y ⊆ x := by
  refine ⟨?_, fun hxy hyx ↦ mem_irrefl _ (hxy hyx)⟩
  revert hx hy
  refine Sym2.GameAdd.recursion mem_wf (fun x y IH hx hy hyx z hzy ↦ ?_) x y
  by_contra hzx
  exact hyx (mem_of_subset_of_mem hx hy (IH z x (Sym2.GameAdd.fst_snd hzy) (hy.mem hzy) hx hzx) hzy)
/-
**ZFSet.IsOrdinal.not_subset_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`
。
形式化陈述：not_subset_iff_mem (hx : x.IsOrdinal) (hy : y.IsOrdinal) : ¬ x subseteq y 
↔ y in x
参数：hx : x.IsOrdinal；hy : y.IsOrdinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `ZFSet.IsOrdinal.notMem_iff_subset`：notMem_iff_subset (hx : x.IsOrdinal) 
(hy : y.IsOrdinal) : x ∉ y ↔ y subseteq x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_subset_iff_mem (hx : x.IsOrdinal) (hy : y.IsOrdinal) : ¬ x ⊆ y ↔ y ∈ x := by
  rw [not_iff_comm, notMem_iff_subset hy hx]
/-
**ZFSet.IsOrdinal.mem_or_subset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：mem_or_subset (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x in y ∨ y subseteq 
x
参数：hx : x.IsOrdinal；hy : y.IsOrdinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `ZFSet.IsOrdinal.notMem_iff_subset`：notMem_iff_subset (hx : x.IsOrdinal) 
(hy : y.IsOrdinal) : x ∉ y ↔ y subseteq x
-/
theorem mem_or_subset (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ∈ y ∨ y ⊆ x := by
  rw [or_iff_not_imp_left, notMem_iff_subset hx hy]
  exact id
/-
**ZFSet.IsOrdinal.subset_total** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：subset_total (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x subseteq y ∨ y subs
eteq x
参数：hx : x.IsOrdinal；hy : y.IsOrdinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.IsOrdinal.mem_or_subset`：mem_or_subset (hx : x.IsOrdinal) (hy : y.
IsOrdinal) : x in y ∨ y subseteq x
· 使用定理 `ZFSet.IsOrdinal.subset_of_mem`：subset_of_mem (h : x.IsOrdinal) : y in x 
-> y subseteq x
-/
theorem subset_total (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ⊆ y ∨ y ⊆ x := by
  obtain h | h := mem_or_subset hx hy
  · exact Or.inl (hy.subset_of_mem h)
  · exact Or.inr h
/-
**ZFSet.IsOrdinal.mem_trichotomous** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：mem_trichotomous (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x in y ∨ x = y ∨ 
y in x
参数：hx : x.IsOrdinal；hy : y.IsOrdinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.IsOrdinal.subset_iff_eq_or_mem`：subset_iff_eq_or_mem (hx : x.IsOrd
inal) (hy : y.IsOrdinal) : x subseteq y ↔ x = y ∨ x in y
· 使用定理 `ZFSet.IsOrdinal.mem_or_subset`：mem_or_subset (hx : x.IsOrdinal) (hy : y.
IsOrdinal) : x in y ∨ y subseteq x
-/
theorem mem_trichotomous (hx : x.IsOrdinal) (hy : y.IsOrdinal) : x ∈ y ∨ x = y ∨ y ∈ x := by
  rw [eq_comm, ← subset_iff_eq_or_mem hy hx]
  exact mem_or_subset hx hy
/-
**ZFSet.IsOrdinal.trichotomous** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：∀ {x : ZFSet.{u}}, x.IsOrdinal → Std.Trichotomous (Subrel (fun x1 x2 => x1
 ∈ x2) fun x_1 => x_1 ∈ x)
参数：Subrel (fun x1 x2 => x1 ∈ x2) fun x_1 => x_1 ∈ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.trichotomous_of_rel_or_eq_or_rel_swap`：∀ {α : Sort u_1} {r : α → α →
 Prop}, (∀ {a b : α}, r a b ∨ a = b ∨ r b a) → Std.Trichotomous r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `ZFSet.IsOrdinal.mem_trichotomous`：mem_trichotomous (hx : x.IsOrdinal) (h
y : y.IsOrdinal) : x in y ∨ x = y ∨ y in x
· 使用定理 `ZFSet.IsOrdinal.mem`：∀ {x y : ZFSet.{u}}, x.IsOrdinal → y ∈ x → y.IsOrdi
nal
-/
protected theorem trichotomous (h : x.IsOrdinal) : Std.Trichotomous (Subrel (· ∈ ·) (· ∈ x)) :=
  Std.trichotomous_of_rel_or_eq_or_rel_swap <| by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    simpa using mem_trichotomous (h.mem ha) (h.mem hb)

@[deprecated (since := "2026-01-24")] protected alias isTrichotomous := IsOrdinal.trichotomous

/-- An ordinal is a transitive set, trichotomous under membership. -/
/-
**ZFSet.IsOrdinal._root_.ZFSet.isOrdinal_iff_trichotomous** 是 Mathlib 中的一个定理，位于命
名空间 `ZFSet.IsOrdinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordinal is a transitive set, trichotomous under membership.
-/
theorem _root_.ZFSet.isOrdinal_iff_trichotomous :
    x.IsOrdinal ↔ x.IsTransitive ∧ Std.Trichotomous (Subrel (· ∈ ·) (· ∈ x)) where
  mp h := ⟨h.isTransitive, h.trichotomous⟩
  mpr := by
    rintro ⟨h₁, h₂⟩
    rw [isOrdinal_iff_isTrans]
    refine ⟨h₁, ⟨@fun y z w hyz hzw ↦ ?_⟩⟩
    obtain hyw | rfl | hwy := trichotomous_of (Subrel (· ∈ ·) (· ∈ x)) y w
    · exact hyw
    · cases asymm hyz hzw
    · cases mem_wf.asymmetric₃ _ _ _ hyz hzw hwy

@[deprecated (since := "2026-01-24")]
alias _root_.ZFSet.isOrdinal_iff_isTrichotomous := _root_.ZFSet.isOrdinal_iff_trichotomous
/-
**ZFSet.IsOrdinal.isWellOrder** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：∀ {x : ZFSet.{u}}, x.IsOrdinal → IsWellOrder (↥x) (Subrel (fun x1 x2 => x1
 ∈ x2) fun x_1 => x_1 ∈ x)
参数：↥x；Subrel (fun x1 x2 => x1 ∈ x2) fun x_1 => x_1 ∈ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s), WellFounded s → WellFounded r
· 使用定理 `ZFSet.mem_wf`：mem_wf : @WellFounded ZFSet (· in ·)
· 使用定理 `ZFSet.IsOrdinal.trichotomous`：∀ {x : ZFSet.{u}}, x.IsOrdinal → Std.Trich
otomous (Subrel (fun x1 x2 => x1 ∈ x2) fun x_1 => x_1 ∈ x)
-/
protected theorem isWellOrder (h : x.IsOrdinal) : IsWellOrder _ (Subrel (· ∈ ·) (· ∈ x)) where
  wf := (Subrel.relEmbedding _ _).wellFounded mem_wf
  trichotomous := h.trichotomous.1

/-- An ordinal is a transitive set, well-ordered under membership. -/
/-
**ZFSet.IsOrdinal._root_.ZFSet.isOrdinal_iff_isWellOrder** 是 Mathlib 中的一个定理，位于命名
空间 `ZFSet.IsOrdinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordinal is a transitive set, well-ordered under membership.
-/
theorem _root_.ZFSet.isOrdinal_iff_isWellOrder : x.IsOrdinal ↔
    x.IsTransitive ∧ IsWellOrder _ (Subrel (· ∈ ·) (· ∈ x)) := by
  use fun h ↦ ⟨h.isTransitive, h.isWellOrder⟩
  rintro ⟨h₁, h₂⟩
  refine isOrdinal_iff_isTrans.2 ⟨h₁, ?_⟩
  infer_instance
/-
**ZFSet.IsOrdinal.rank_lt_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：rank_lt_iff_mem {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) : rank
 x < rank y ↔ x in y
参数：hx : IsOrdinal x；hy : IsOrdinal y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.IsOrdinal.not_subset_iff_mem`：not_subset_iff_mem (hx : x.IsOrdinal
) (hy : y.IsOrdinal) : ¬ x subseteq y ↔ y in x
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `ZFSet.rank_mono`：∀ {x y : ZFSet.{u}}, x ⊆ y → x.rank ≤ y.rank
· 使用定理 `ZFSet.rank_lt_of_mem`：rank_lt_of_mem : y in x -> rank y < rank x
-/
theorem rank_lt_iff_mem {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    rank x < rank y ↔ x ∈ y := by
  refine ⟨fun h ↦ ?_, rank_lt_of_mem⟩
  rw [← hy.not_subset_iff_mem hx]
  exact fun h' ↦ (rank_mono h').not_gt h
/-
**ZFSet.IsOrdinal.rank_le_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`
。
形式化陈述：rank_le_iff_subset {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) : r
ank x <= rank y ↔ x subseteq y
参数：hx : IsOrdinal x；hy : IsOrdinal y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.IsOrdinal.notMem_iff_subset`：notMem_iff_subset (hx : x.IsOrdinal) 
(hy : y.IsOrdinal) : x ∉ y ↔ y subseteq x
· 使用定理 `ZFSet.IsOrdinal.rank_lt_iff_mem`：rank_lt_iff_mem {x y : ZFSet} (hx : IsO
rdinal x) (hy : IsOrdinal y) : rank x < rank y ↔ x in y
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rank_le_iff_subset {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    rank x ≤ rank y ↔ x ⊆ y := by
  rw [← notMem_iff_subset hy hx, ← rank_lt_iff_mem hy hx, not_lt]
/-
**ZFSet.IsOrdinal.rank_inj** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：rank_inj {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) : rank x = ra
nk y ↔ x = y
参数：hx : IsOrdinal x；hy : IsOrdinal y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `ZFSet.IsOrdinal.rank_le_iff_subset`：rank_le_iff_subset {x y : ZFSet} (hx
 : IsOrdinal x) (hy : IsOrdinal y) : rank x <= rank y ↔ x subseteq y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rank_inj {x y : ZFSet} (hx : IsOrdinal x) (hy : IsOrdinal y) :
    rank x = rank y ↔ x = y := by
  rw [le_antisymm_iff, subset_antisymm_iff, rank_le_iff_subset hx hy, rank_le_iff_subset hy hx]

end IsOrdinal

@[simp]
/-
**ZFSet.isOrdinal_empty** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：isOrdinal_empty : IsOrdinal ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.isTransitive_empty`：isTransitive_empty : IsTransitive ∅
· 使用定理 `ZFSet.notMem_empty`：notMem_empty (x) : x ∉ (∅ : ZFSet.{u})
-/
theorem isOrdinal_empty : IsOrdinal ∅ :=
  ⟨isTransitive_empty, fun _ _ H ↦ (notMem_empty _ H).elim⟩
/-
**ZFSet.isOrdinal_succ** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：isOrdinal_succ {x : ZFSet} (h : IsOrdinal x) : IsOrdinal (insert x x)
参数：h : IsOrdinal x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.mem_insert_iff`：mem_insert_iff {x y z : ZFSet.{u}} : x in insert y
 z ↔ x = y ∨ x in z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ZFSet.IsOrdinal.subset_of_mem`：subset_of_mem (h : x.IsOrdinal) : y in x 
-> y subseteq x
· 使用定理 `ZFSet.IsOrdinal.mem_trans`：mem_trans (h : z.IsOrdinal) : x in y -> y in 
z -> x in z
· 使用定理 `ZFSet.IsOrdinal.mem_trans'`：∀ {x : ZFSet.{u_1}}, x.IsOrdinal → ∀ {y z w 
: ZFSet.{u_1}}, y ∈ z → z ∈ w → w ∈ x → y ∈ w
-/
theorem isOrdinal_succ {x : ZFSet} (h : IsOrdinal x) : IsOrdinal (insert x x) := by
  refine ⟨fun y hy ↦ ?_, @fun y z w hyz hzw hw ↦ ?_⟩
  · obtain rfl | hy := mem_insert_iff.1 hy
    on_goal 2 => apply (h.subset_of_mem hy).trans
    all_goals simp_all [subset_def]
  · obtain rfl | hw := mem_insert_iff.1 hw
    exacts [h.mem_trans hyz hzw, h.mem_trans' hyz hzw hw]

end ZFSet

/-! ### Type-theoretic ordinals to von Neumann ordinals -/

namespace Ordinal
open ZFSet

/-- The von Neumann ordinal corresponding to a given `Ordinal`, as a `PSet`.

The elements of `o.toPSet` are all `a.toPSet` with `a < o`. -/
/-
**Ordinal.toPSet** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：toPSet (o : Ordinal.{u}) : PSet.{u}
参数：o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The von Neumann ordinal corresponding to a given `Ordinal`, as a `PSet`.

The elements of `o.toPSet` are all `a.toPSet` with `a < o`.
-/
noncomputable def toPSet (o : Ordinal.{u}) : PSet.{u} :=
  ⟨o.ToType, fun a ↦ toPSet a⟩
termination_by o
decreasing_by exact a.toOrd.prop

@[simp]
/-
**Ordinal.type_toPSet** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：type_toPSet (o : Ordinal) : o.toPSet.Type = o.ToType
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.toPSet.eq_1`：∀ (o : Ordinal.{u}), o.toPSet = PSet.mk o.ToType fu
n a => (↑a.toOrd).toPSet
-/
theorem type_toPSet (o : Ordinal) : o.toPSet.Type = o.ToType := by
  rw [toPSet]
  rfl
/-
**Ordinal.mem_toPSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_toPSet_iff {o : Ordinal} {x : PSet} : x in o.toPSet ↔ exists a < o, x.
Equiv a.toPSet
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.toPSet.eq_1`：∀ (o : Ordinal.{u}), o.toPSet = PSet.mk o.ToType fu
n a => (↑a.toOrd).toPSet
· 使用定理 `PSet.mem_def`：mem_def {x y : PSet} : x in y ↔ exists b, Equiv x (y.Func 
b)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
-/
theorem mem_toPSet_iff {o : Ordinal} {x : PSet} : x ∈ o.toPSet ↔ ∃ a < o, x.Equiv a.toPSet := by
  rw [toPSet, PSet.mem_def]
  simpa using ((@ToType.mk o).exists_congr_left (p := fun y ↦ x.Equiv y.1.toPSet)).symm

@[simp]
/-
**Ordinal.rank_toPSet** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：rank_toPSet (o : Ordinal) : o.toPSet.rank = o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.toPSet.eq_1`：∀ (o : Ordinal.{u}), o.toPSet = PSet.mk o.ToType fu
n a => (↑a.toOrd).toPSet
· 使用定理 `PSet.rank.eq_1`：∀ (α : Type u) (A : α → PSet.{u}), (PSet.mk α A).rank = 
⨆ a, Order.succ (A a).rank
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_succ`：iSup_succ [SuccOrder α] (x : α) : ⨆ a : Iio x, succ a.1 = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
-/
theorem rank_toPSet (o : Ordinal) : o.toPSet.rank = o := by
  rw [toPSet, PSet.rank]
  conv_rhs => rw [← _root_.iSup_succ o]
  convert! ToType.mk.symm.iSup_comp (g := fun x ↦ Order.succ x.1.toPSet.rank)
  rw [rank_toPSet]
termination_by o
decreasing_by rename_i x; exact x.2

/-- The von Neumann ordinal corresponding to a given `Ordinal`, as a `ZFSet`.

The elements of `o.toZFSet` are all `a.toZFSet` with `a < o`. -/
/-
**Ordinal.toZFSet** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：toZFSet (o : Ordinal.{u}) : ZFSet.{u}
参数：o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The von Neumann ordinal corresponding to a given `Ordinal`, as a `ZFSet`.

The elements of `o.toZFSet` are all `a.toZFSet` with `a < o`.
-/
noncomputable def toZFSet (o : Ordinal.{u}) : ZFSet.{u} :=
  .mk o.toPSet

@[simp]
/-
**Ordinal.mk_toPSet** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mk_toPSet (o : Ordinal) : .mk o.toPSet = o.toZFSet
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_toPSet (o : Ordinal) : .mk o.toPSet = o.toZFSet :=
  rfl
/-
**Ordinal.mem_toZFSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_toZFSet_iff {o : Ordinal} {x : ZFSet} : x in o.toZFSet ↔ exists a < o,
 a.toZFSet = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.toZFSet.eq_1`：∀ (o : Ordinal.{u}), o.toZFSet = ZFSet.mk o.toPSet
· 使用定理 `ZFSet.mk_eq`：mk_eq (x : PSet) : @Eq ZFSet ⟦x⟧ (mk x)
· 使用定理 `ZFSet.mk_mem_iff`：mk_mem_iff {x y : PSet} : mk x in mk y ↔ x in y
· 使用定理 `Ordinal.mem_toPSet_iff`：mem_toPSet_iff {o : Ordinal} {x : PSet} : x in o
.toPSet ↔ exists a < o, x.Equiv a.toPSet
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ZFSet.eq`：eq {x y : PSet} : mk x = mk y ↔ Equiv x y
· 使用定理 `PSet.Equiv.comm`：∀ {x : PSet.{u_1}} {y : PSet.{u_2}}, x.Equiv y ↔ y.Equi
v x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toZFSet_iff {o : Ordinal} {x : ZFSet} : x ∈ o.toZFSet ↔ ∃ a < o, a.toZFSet = x := by
  induction x using Quotient.ind
  rw [toZFSet, mk_eq, ZFSet.mk_mem_iff, mem_toPSet_iff]
  congr!
  rw [toZFSet, eq, PSet.Equiv.comm]

@[simp]
/-
**Ordinal.rank_toZFSet** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：rank_toZFSet (o : Ordinal) : o.toZFSet.rank = o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.rank_toPSet`：rank_toPSet (o : Ordinal) : o.toPSet.rank = o
-/
theorem rank_toZFSet (o : Ordinal) : o.toZFSet.rank = o :=
  rank_toPSet o

@[simp]
/-
**Ordinal.coe_toZFSet** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：coe_toZFSet {o : Ordinal} : o.toZFSet = toZFSet '' Iio o
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_toZFSet {o : Ordinal} : o.toZFSet = toZFSet '' Iio o := by
  ext
  simp [mem_toZFSet_iff]
/-
**Ordinal.toZFSet_mem_toZFSet_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem toZFSet_mem_toZFSet_of_lt {a b : Ordinal} (h : a < b) :
    a.toZFSet ∈ b.toZFSet := by
  rw [mem_toZFSet_iff]
  exact ⟨a, h, rfl⟩
/-
**Ordinal.toZFSet_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：toZFSet_monotone : Monotone toZFSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.mem_toZFSet_iff`：mem_toZFSet_iff {o : Ordinal} {x : ZFSet} : x i
n o.toZFSet ↔ exists a < o, a.toZFSet = x
· 使用定理 `_private.Mathlib.SetTheory.ZFC.Ordinal.0.Ordinal.toZFSet_mem_toZFSet_of_
lt`：∀ {a b : Ordinal.{u_1}}, a < b → a.toZFSet ∈ b.toZFSet
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem toZFSet_monotone : Monotone toZFSet := by
  intro a b h x hx
  obtain ⟨c, hc, rfl⟩ := mem_toZFSet_iff.1 hx
  exact toZFSet_mem_toZFSet_of_lt (hc.trans_le h)

@[simp]
/-
**Ordinal.toZFSet_mem_toZFSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：toZFSet_mem_toZFSet_iff {a b : Ordinal} : a.toZFSet in b.toZFSet ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ZFSet.notMem_of_subset`：notMem_of_subset {x y : ZFSet} (h : x subseteq y
) : y ∉ x
· 使用定理 `Ordinal.toZFSet_monotone`：toZFSet_monotone : Monotone toZFSet
· 使用定理 `_private.Mathlib.SetTheory.ZFC.Ordinal.0.Ordinal.toZFSet_mem_toZFSet_of_
lt`：∀ {a b : Ordinal.{u_1}}, a < b → a.toZFSet ∈ b.toZFSet
-/
theorem toZFSet_mem_toZFSet_iff {a b : Ordinal} : a.toZFSet ∈ b.toZFSet ↔ a < b := by
  refine ⟨?_, toZFSet_mem_toZFSet_of_lt⟩
  contrapose!
  exact fun h ↦ notMem_of_subset (toZFSet_monotone h)

@[simp]
/-
**Ordinal.toZFSet_subset_toZFSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：toZFSet_subset_toZFSet_iff {a b : Ordinal} : a.toZFSet subseteq b.toZFSet 
↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ZFSet.not_subset_of_mem`：not_subset_of_mem {x y : ZFSet} (h : x in y) : 
¬ y subseteq x
· 使用定理 `_private.Mathlib.SetTheory.ZFC.Ordinal.0.Ordinal.toZFSet_mem_toZFSet_of_
lt`：∀ {a b : Ordinal.{u_1}}, a < b → a.toZFSet ∈ b.toZFSet
· 使用定理 `Ordinal.toZFSet_monotone`：toZFSet_monotone : Monotone toZFSet
-/
theorem toZFSet_subset_toZFSet_iff {a b : Ordinal} : a.toZFSet ⊆ b.toZFSet ↔ a ≤ b := by
  refine ⟨?_, fun h ↦ toZFSet_monotone h⟩
  contrapose!
  exact fun h ↦ not_subset_of_mem (toZFSet_mem_toZFSet_of_lt h)
/-
**Ordinal.toZFSet_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：toZFSet_strictMono : StrictMono toZFSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ssubset_iff_subset_not_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder
 α] [inst : Preorder α] {a b : α}, a ⊂ b ↔ a ⊆ b ∧ ¬b ⊆ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem toZFSet_strictMono : StrictMono toZFSet :=
  fun _ _ h ↦ by rw [ssubset_iff_subset_not_subset]; simp [h, h.le]
/-
**Ordinal.toZFSet_injective** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：toZFSet_injective : Function.Injective toZFSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Ordinal.toZFSet_strictMono`：toZFSet_strictMono : StrictMono toZFSet
-/
theorem toZFSet_injective : Function.Injective toZFSet :=
  toZFSet_strictMono.injective

@[simp]
/-
**Ordinal.toZFSet_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：toZFSet_zero : toZFSet 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toZFSet_zero : toZFSet 0 = ∅ := by
  ext; simp [mem_toZFSet_iff]

@[simp]
/-
**Ordinal.toZFSet_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：toZFSet_add_one (o : Ordinal) : toZFSet (o + 1) = insert (toZFSet o) (toZF
Set o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZFSet.ext`：∀ {x y : ZFSet.{u}}, (∀ (z : ZFSet.{u}), z ∈ x ↔ z ∈ y) → x =
 y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toZFSet_add_one (o : Ordinal) : toZFSet (o + 1) = insert (toZFSet o) (toZFSet o) := by
  aesop (add simp [mem_toZFSet_iff, le_iff_eq_or_lt])

@[deprecated toZFSet_add_one (since := "2026-02-24")]
/-
**Ordinal.toZFSet_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：toZFSet_succ (o : Ordinal) : toZFSet (Order.succ o) = insert (toZFSet o) (
toZFSet o)
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.toZFSet_add_one`：toZFSet_add_one (o : Ordinal) : toZFSet (o + 1)
 = insert (toZFSet o) (toZFSet o)
-/
theorem toZFSet_succ (o : Ordinal) : toZFSet (Order.succ o) = insert (toZFSet o) (toZFSet o) :=
  toZFSet_add_one o

@[simp]
/-
**Ordinal.card_toZFSet** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：card_toZFSet (o : Ordinal) : (toZFSet o).card = o.card
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZFSet.cardinalMk_coe_sort`：cardinalMk_coe_sort : #x = lift.{u + 1, u} (c
ard x)
· 使用定理 `Cardinal.mk_Iio_ordinal`：∀ (o : Ordinal.{u}), Cardinal.mk ↑(Set.Iio o) =
 Cardinal.lift.{u + 1, u} o.card
· 使用定理 `Cardinal.mk_image_eq`：mk_image_eq {α β : Type u} {f : α -> β} {s : Set α
} (hf : Injective f) : #(f '' s) = #s
· 使用定理 `Ordinal.toZFSet_injective`：toZFSet_injective : Function.Injective toZFSe
t
-/
theorem card_toZFSet (o : Ordinal) : (toZFSet o).card = o.card := by
  simpa [← coe_toZFSet, cardinalMk_coe_sort, Cardinal.mk_Iio_ordinal, ← lift_card] using
    Cardinal.mk_image_eq (s := Iio o) toZFSet_injective

end Ordinal

namespace ZFSet
open Ordinal

/-
**ZFSet.isOrdinal_toZFSet** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：isOrdinal_toZFSet (o : Ordinal) : IsOrdinal o.toZFSet
参数：o : Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.mem_toZFSet_iff`：mem_toZFSet_iff {o : Ordinal} {x : ZFSet} : x i
n o.toZFSet ↔ exists a < o, a.toZFSet = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.toZFSet_mem_toZFSet_iff`：toZFSet_mem_toZFSet_iff {a b : Ordinal}
 : a.toZFSet in b.toZFSet ↔ a < b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem isOrdinal_toZFSet (o : Ordinal) : IsOrdinal o.toZFSet := by
  refine ⟨fun x hx y hy ↦ ?_, fun {z y x} hz hy hx ↦ ?_⟩
  all_goals
    obtain ⟨a, ha, rfl⟩ := mem_toZFSet_iff.1 hx
    obtain ⟨b, hb, rfl⟩ := mem_toZFSet_iff.1 hy
  · exact toZFSet_mem_toZFSet_iff.2 (hb.trans ha)
  · obtain ⟨c, hc, rfl⟩ := mem_toZFSet_iff.1 hz
    exact toZFSet_mem_toZFSet_iff.2 (hc.trans hb)
/-
**ZFSet.IsOrdinal.toZFSet_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet.IsOrdinal`。
形式化陈述：∀ {x : ZFSet.{u_1}}, x.IsOrdinal → x.rank.toZFSet = x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZFSet.IsOrdinal.rank_inj`：rank_inj {x y : ZFSet} (hx : IsOrdinal x) (hy 
: IsOrdinal y) : rank x = rank y ↔ x = y
· 使用定理 `ZFSet.isOrdinal_toZFSet`：isOrdinal_toZFSet (o : Ordinal) : IsOrdinal o.t
oZFSet
· 使用定理 `Ordinal.rank_toZFSet`：rank_toZFSet (o : Ordinal) : o.toZFSet.rank = o
-/
theorem IsOrdinal.toZFSet_rank_eq {x : ZFSet} (hx : IsOrdinal x) : x.rank.toZFSet = x :=
  (IsOrdinal.rank_inj (isOrdinal_toZFSet _) hx).1 (rank_toZFSet _)
/-
**ZFSet.isOrdinal_iff_mem_range_toZFSet** 是 Mathlib 中的一个定理，位于命名空间 `ZFSet`。
形式化陈述：isOrdinal_iff_mem_range_toZFSet {x : ZFSet.{u}} : IsOrdinal x ↔ x in Set.r
ange toZFSet.{u}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZFSet.IsOrdinal.toZFSet_rank_eq`：∀ {x : ZFSet.{u_1}}, x.IsOrdinal → x.ra
nk.toZFSet = x
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `ZFSet.isOrdinal_toZFSet`：isOrdinal_toZFSet (o : Ordinal) : IsOrdinal o.t
oZFSet
-/
theorem isOrdinal_iff_mem_range_toZFSet {x : ZFSet.{u}} :
    IsOrdinal x ↔ x ∈ Set.range toZFSet.{u} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rw [← h.toZFSet_rank_eq]
    exact Set.mem_range_self _
  · rintro ⟨a, rfl⟩
    exact isOrdinal_toZFSet a

set_option backward.isDefEq.respectTransparency false in
/-- `Ordinal` is order-equivalent to the type of von Neumann ordinals. -/
@[simps apply symm_apply]
/-
**ZFSet._root_.Ordinal.toZFSetIso** 是 Mathlib 中的一个定义，位于命名空间 `ZFSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ordinal` is order-equivalent to the type of von Neumann ordinals.
-/
noncomputable def _root_.Ordinal.toZFSetIso : Ordinal ≃o {x // ZFSet.IsOrdinal x} where
  toFun o := ⟨_, isOrdinal_toZFSet o⟩
  invFun x := rank x.1
  left_inv o := rank_toZFSet o
  right_inv := fun ⟨x, hx⟩ ↦ by simpa using hx.toZFSet_rank_eq
  map_rel_iff' {a b} := by simp

end ZFSet

