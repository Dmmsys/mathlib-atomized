/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sets.OpenCover

/-!
# Sober spaces

A quasi-sober space is a topological space where every irreducible closed subset has a generic
point.
A sober space is a quasi-sober space where every irreducible closed subset
has a *unique* generic point. This is if and only if the space is T0, and thus sober spaces can be
stated via `[QuasiSober α] [T0Space α]`.

## Main definition

* `IsGenericPoint` : `x` is the generic point of `S` if `S` is the closure of `x`.
* `QuasiSober` : A space is quasi-sober if every irreducible closed subset has a generic point.
* `genericPoints` : The set of generic points of irreducible components.

-/

@[expose] public section


open Set

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

section genericPoint

/-- `x` is a generic point of `S` if `S` is the closure of `x`. -/
@[stacks 004X "(1)"]
/-
**IsGenericPoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsGenericPoint (x : α) (S : Set α) : Prop
参数：x : α；S : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x` is a generic point of `S` if `S` is the closure of `x`.
-/
def IsGenericPoint (x : α) (S : Set α) : Prop :=
  closure ({x} : Set α) = S
/-
**isGenericPoint_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGenericPoint_def {x : α} {S : Set α} : IsGenericPoint x S ↔ closure ({x}
 : Set α) = S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isGenericPoint_def {x : α} {S : Set α} : IsGenericPoint x S ↔ closure ({x} : Set α) = S :=
  Iff.rfl
/-
**IsGenericPoint.def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGenericPoint.def {x : α} {S : Set α} (h : IsGenericPoint x S) : closure 
({x} : Set α) = S
参数：h : IsGenericPoint x S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsGenericPoint.def {x : α} {S : Set α} (h : IsGenericPoint x S) :
    closure ({x} : Set α) = S :=
  h
/-
**isGenericPoint_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGenericPoint_closure {x : α} : IsGenericPoint x (closure ({x} : Set α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
-/
theorem isGenericPoint_closure {x : α} : IsGenericPoint x (closure ({x} : Set α)) :=
  refl _

variable {x y : α} {S U Z : Set α}
/-
**isGenericPoint_iff_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGenericPoint_iff_specializes : IsGenericPoint x S ↔ forall y, x ⤳ y ↔ y 
in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isGenericPoint_iff_specializes : IsGenericPoint x S ↔ ∀ y, x ⤳ y ↔ y ∈ S := by
  simp only [specializes_iff_mem_closure, IsGenericPoint, Set.ext_iff]

namespace IsGenericPoint

/-
**IsGenericPoint.specializes_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：specializes_iff_mem (h : IsGenericPoint x S) : x ⤳ y ↔ y in S
参数：h : IsGenericPoint x S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isGenericPoint_iff_specializes`：isGenericPoint_iff_specializes : IsGener
icPoint x S ↔ forall y, x ⤳ y ↔ y in S
-/
theorem specializes_iff_mem (h : IsGenericPoint x S) : x ⤳ y ↔ y ∈ S :=
  isGenericPoint_iff_specializes.1 h y
/-
**IsGenericPoint.specializes** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {x y : α} {S : Set α}, IsGene
ricPoint x S → y ∈ S → x ⤳ y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsGenericPoint.specializes_iff_mem`：specializes_iff_mem (h : IsGenericPo
int x S) : x ⤳ y ↔ y in S
-/
protected theorem specializes (h : IsGenericPoint x S) (h' : y ∈ S) : x ⤳ y :=
  h.specializes_iff_mem.2 h'
/-
**IsGenericPoint.mem** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {x : α} {S : Set α}, IsGeneri
cPoint x S → x ∈ S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsGenericPoint.specializes_iff_mem`：specializes_iff_mem (h : IsGenericPo
int x S) : x ⤳ y ↔ y in S
· 使用定理 `specializes_rfl`：specializes_rfl : x ⤳ x
-/
protected theorem mem (h : IsGenericPoint x S) : x ∈ S :=
  h.specializes_iff_mem.1 specializes_rfl
/-
**IsGenericPoint.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {x : α} {S : Set α}, IsGeneri
cPoint x S → IsClosed S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `IsGenericPoint.def`：IsGenericPoint.def {x : α} {S : Set α} (h : IsGeneri
cPoint x S) : closure ({x} : Set α) = S
-/
protected theorem isClosed (h : IsGenericPoint x S) : IsClosed S :=
  h.def ▸ isClosed_closure
/-
**IsGenericPoint.isIrreducible** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {x : α} {S : Set α}, IsGeneri
cPoint x S → IsIrreducible S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIrreducible.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsIrreducible s → IsIrreducible (closure s)
· 使用定理 `isIrreducible_singleton`：isIrreducible_singleton {x} : IsIrreducible ({x
} : Set X)
· 使用定理 `IsGenericPoint.def`：IsGenericPoint.def {x : α} {S : Set α} (h : IsGeneri
cPoint x S) : closure ({x} : Set α) = S
-/
protected theorem isIrreducible (h : IsGenericPoint x S) : IsIrreducible S :=
  h.def ▸ isIrreducible_singleton.closure
/-
**IsGenericPoint.inseparable** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {x y : α} {S : Set α},   IsGe
nericPoint x S → IsGenericPoint y S → Inseparable x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Specializes.antisymm`：Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x
 ~ᵢ y
· 使用定理 `IsGenericPoint.specializes`：∀ {α : Type u_1} [inst : TopologicalSpace α]
 {x y : α} {S : Set α}, IsGenericPoint x S → y ∈ S → x ⤳ y
· 使用定理 `IsGenericPoint.mem`：∀ {α : Type u_1} [inst : TopologicalSpace α] {x : α}
 {S : Set α}, IsGenericPoint x S → x ∈ S
-/
protected theorem inseparable (h : IsGenericPoint x S) (h' : IsGenericPoint y S) :
    Inseparable x y :=
  (h.specializes h'.mem).antisymm (h'.specializes h.mem)

/-- In a T₀ space, each set has at most one generic point. -/
/-
**IsGenericPoint.eq** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {x y : α} {S : Set α} [T0Spac
e α],   IsGenericPoint x S → IsGenericPoint y S → x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Inseparable.eq`：Inseparable.eq [T0Space X] {x y : X} (h : Inseparable x 
y) : x = y
· 使用定理 `IsGenericPoint.inseparable`：∀ {α : Type u_1} [inst : TopologicalSpace α]
 {x y : α} {S : Set α},   IsGenericPoint x S → IsGenericPoint y S → Inseparable 
x y

--- 原说明 ---
In a T₀ space, each set has at most one generic point.
-/
protected theorem eq [T0Space α] (h : IsGenericPoint x S) (h' : IsGenericPoint y S) : x = y :=
  (h.inseparable h').eq
/-
**IsGenericPoint.mem_open_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：mem_open_set_iff (h : IsGenericPoint x S) (hU : IsOpen U) : x in U ↔ (S in
ter U).Nonempty
参数：h : IsGenericPoint x S；hU : IsOpen U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGenericPoint.mem`：∀ {α : Type u_1} [inst : TopologicalSpace α] {x : α}
 {S : Set α}, IsGenericPoint x S → x ∈ S
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `IsGenericPoint.specializes`：∀ {α : Type u_1} [inst : TopologicalSpace α]
 {x y : α} {S : Set α}, IsGenericPoint x S → y ∈ S → x ⤳ y
-/
theorem mem_open_set_iff (h : IsGenericPoint x S) (hU : IsOpen U) : x ∈ U ↔ (S ∩ U).Nonempty :=
  ⟨fun h' => ⟨x, h.mem, h'⟩, fun ⟨_y, hyS, hyU⟩ => (h.specializes hyS).mem_open hU hyU⟩
/-
**IsGenericPoint.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：disjoint_iff (h : IsGenericPoint x S) (hU : IsOpen U) : Disjoint S U ↔ x ∉
 U
参数：h : IsGenericPoint x S；hU : IsOpen U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGenericPoint.mem_open_set_iff`：mem_open_set_iff (h : IsGenericPoint x 
S) (hU : IsOpen U) : x in U ↔ (S inter U).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_iff (h : IsGenericPoint x S) (hU : IsOpen U) : Disjoint S U ↔ x ∉ U := by
  rw [h.mem_open_set_iff hU, ← not_disjoint_iff_nonempty_inter, Classical.not_not]
/-
**IsGenericPoint.mem_closed_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：mem_closed_set_iff (h : IsGenericPoint x S) (hZ : IsClosed Z) : x in Z ↔ S
 subseteq Z
参数：h : IsGenericPoint x S；hZ : IsClosed Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGenericPoint.def`：IsGenericPoint.def {x : α} {S : Set α} (h : IsGeneri
cPoint x S) : closure ({x} : Set α) = S
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closed_set_iff (h : IsGenericPoint x S) (hZ : IsClosed Z) : x ∈ Z ↔ S ⊆ Z := by
  rw [← h.def, hZ.closure_subset_iff, singleton_subset_iff]
/-
**IsGenericPoint.image** 是 Mathlib 中的一个定理，位于命名空间 `IsGenericPoint`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {x : α} {S : Set α},   IsGenericPoint x S → ∀ {f : α → β}, Conti
nuous f → IsGenericPoint (f x) (closure (f '' S))
参数：f x；closure (f '' S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isGenericPoint_def`：isGenericPoint_def {x : α} {S : Set α} : IsGenericPo
int x S ↔ closure ({x} : Set α) = S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGenericPoint.def`：IsGenericPoint.def {x : α} {S : Set α} (h : IsGeneri
cPoint x S) : closure ({x} : Set α) = S
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `closure_image_closure`：closure_image_closure (h : Continuous f) : closur
e (f '' closure s) = closure (f '' s)
-/
protected theorem image (h : IsGenericPoint x S) {f : α → β} (hf : Continuous f) :
    IsGenericPoint (f x) (closure (f '' S)) := by
  rw [isGenericPoint_def, ← h.def, ← image_singleton, closure_image_closure hf]

end IsGenericPoint

/-
**isGenericPoint_iff_forall_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGenericPoint_iff_forall_closed (hS : IsClosed S) (hxS : x in S) : IsGene
ricPoint x S ↔ forall Z : Set α, IsClosed Z -> x in Z -> S subseteq Z
参数：hS : IsClosed S；hxS : x in S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isGenericPoint_iff_forall_closed (hS : IsClosed S) (hxS : x ∈ S) :
    IsGenericPoint x S ↔ ∀ Z : Set α, IsClosed Z → x ∈ Z → S ⊆ Z := by
  have : closure {x} ⊆ S := closure_minimal (singleton_subset_iff.2 hxS) hS
  simp_rw [IsGenericPoint, subset_antisymm_iff, this, true_and, closure, subset_sInter_iff,
    mem_ofPred_eq, and_imp, singleton_subset_iff]

end genericPoint

section Sober

/-- A space is sober if every irreducible closed subset has a generic point. -/
@[mk_iff, stacks 004X "(3)"]
/-
**QuasiSober** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_3) → [TopologicalSpace α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A space is sober if every irreducible closed subset has a generic point.
-/
class QuasiSober (α : Type*) [TopologicalSpace α] : Prop where
  sober : ∀ {S : Set α}, IsIrreducible S → IsClosed S → ∃ x, IsGenericPoint x S

/-- A generic point of the closure of an irreducible space. -/
/-
**IsIrreducible.genericPoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsIrreducible.genericPoint [QuasiSober α] {S : Set α} (hS : IsIrreducible 
S) : α
参数：hS : IsIrreducible S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A generic point of the closure of an irreducible space.
-/
noncomputable def IsIrreducible.genericPoint [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    α :=
  (QuasiSober.sober hS.closure isClosed_closure).choose
/-
**IsIrreducible.isGenericPoint_genericPoint_closure** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsIrreducible.isGenericPoint_genericPoint_closure [QuasiSober α] {S : Set 
α} (hS : IsIrreducible S) : IsGenericPoint hS.genericPoint (closure S)
参数：hS : IsIrreducible S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `QuasiSober.sober`：∀ {α : Type u_3} {inst : TopologicalSpace α} [self : Q
uasiSober α] {S : Set α},   IsIrreducible S → IsClosed S → ∃ x, IsGenericPoint x
 S
· 使用定理 `IsIrreducible.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsIrreducible s → IsIrreducible (closure s)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem IsIrreducible.isGenericPoint_genericPoint_closure
    [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    IsGenericPoint hS.genericPoint (closure S) :=
  (QuasiSober.sober hS.closure isClosed_closure).choose_spec
/-
**IsIrreducible.isGenericPoint_genericPoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIrreducible.isGenericPoint_genericPoint [QuasiSober α] {S : Set α} (hS :
 IsIrreducible S) (hS' : IsClosed S) : IsGenericPoint hS.genericPoint S
参数：hS : IsIrreducible S；hS' : IsClosed S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `IsIrreducible.isGenericPoint_genericPoint_closure`：IsIrreducible.isGener
icPoint_genericPoint_closure [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
 IsGenericPoint hS.genericPoint (closur…
-/
theorem IsIrreducible.isGenericPoint_genericPoint [QuasiSober α] {S : Set α}
    (hS : IsIrreducible S) (hS' : IsClosed S) :
    IsGenericPoint hS.genericPoint S := by
  convert! hS.isGenericPoint_genericPoint_closure; exact hS'.closure_eq.symm

@[simp]
/-
**IsIrreducible.genericPoint_closure_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIrreducible.genericPoint_closure_eq [QuasiSober α] {S : Set α} (hS : IsI
rreducible S) : closure ({hS.genericPoint} : Set α) = closure S
参数：hS : IsIrreducible S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIrreducible.isGenericPoint_genericPoint_closure`：IsIrreducible.isGener
icPoint_genericPoint_closure [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
 IsGenericPoint hS.genericPoint (closur…
-/
theorem IsIrreducible.genericPoint_closure_eq [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    closure ({hS.genericPoint} : Set α) = closure S :=
  hS.isGenericPoint_genericPoint_closure
/-
**IsIrreducible.closure_genericPoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIrreducible.closure_genericPoint [QuasiSober α] {S : Set α} (hS : IsIrre
ducible S) (hS' : IsClosed S) : closure ({hS.genericPoint} : Set α) = S
参数：hS : IsIrreducible S；hS' : IsClosed S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsIrreducible.isGenericPoint_genericPoint_closure`：IsIrreducible.isGener
icPoint_genericPoint_closure [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
 IsGenericPoint hS.genericPoint (closur…
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem IsIrreducible.closure_genericPoint [QuasiSober α] {S : Set α}
    (hS : IsIrreducible S) (hS' : IsClosed S) :
    closure ({hS.genericPoint} : Set α) = S :=
  hS.isGenericPoint_genericPoint_closure.trans hS'.closure_eq

variable (α)

/-- A generic point of a sober irreducible space. -/
/-
**genericPoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：genericPoint [QuasiSober α] [IrreducibleSpace α] : α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IrreducibleSpace.isIrreducible_univ`：IrreducibleSpace.isIrreducible_univ
 (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] : IsIrreducible (univ : S
et X)

--- 原说明 ---
A generic point of a sober irreducible space.
-/
noncomputable def genericPoint [QuasiSober α] [IrreducibleSpace α] : α :=
  (IrreducibleSpace.isIrreducible_univ α).genericPoint
/-
**genericPoint_spec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：genericPoint_spec [QuasiSober α] [IrreducibleSpace α] : IsGenericPoint (ge
nericPoint α) univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IrreducibleSpace.isIrreducible_univ`：IrreducibleSpace.isIrreducible_univ
 (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] : IsIrreducible (univ : S
et X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsIrreducible.isGenericPoint_genericPoint_closure`：IsIrreducible.isGener
icPoint_genericPoint_closure [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
 IsGenericPoint hS.genericPoint (closur…
-/
theorem genericPoint_spec [QuasiSober α] [IrreducibleSpace α] :
    IsGenericPoint (genericPoint α) univ := by
  simpa using! (IrreducibleSpace.isIrreducible_univ α).isGenericPoint_genericPoint_closure

@[simp]
/-
**genericPoint_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：genericPoint_closure [QuasiSober α] [IrreducibleSpace α] : closure ({gener
icPoint α} : Set α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `genericPoint_spec`：genericPoint_spec [QuasiSober α] [IrreducibleSpace α]
 : IsGenericPoint (genericPoint α) univ
-/
theorem genericPoint_closure [QuasiSober α] [IrreducibleSpace α] :
    closure ({genericPoint α} : Set α) = univ :=
  genericPoint_spec α

variable {α}
/-
**genericPoint_specializes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：genericPoint_specializes [QuasiSober α] [IrreducibleSpace α] (x : α) : gen
ericPoint α ⤳ x
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGenericPoint.specializes`：∀ {α : Type u_1} [inst : TopologicalSpace α]
 {x y : α} {S : Set α}, IsGenericPoint x S → y ∈ S → x ⤳ y
· 使用定理 `IrreducibleSpace.isIrreducible_univ`：IrreducibleSpace.isIrreducible_univ
 (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] : IsIrreducible (univ : S
et X)
· 使用定理 `IsIrreducible.isGenericPoint_genericPoint_closure`：IsIrreducible.isGener
icPoint_genericPoint_closure [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
 IsGenericPoint hS.genericPoint (closur…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
theorem genericPoint_specializes [QuasiSober α] [IrreducibleSpace α] (x : α) : genericPoint α ⤳ x :=
  (IsIrreducible.isGenericPoint_genericPoint_closure _).specializes (by simp)

attribute [local instance] specializationOrder

set_option backward.isDefEq.respectTransparency false in
/-- The closed irreducible subsets of a sober space bijects with the points of the space. -/
/-
**irreducibleSetEquivPoints** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：irreducibleSetEquivPoints [QuasiSober α] [T0Space α] : TopologicalSpace.Ir
reducibleCloseds α ≃o α where toFun s
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IrreducibleCloseds.isIrreducible'`：∀ {α : Type u_4} [in
st : TopologicalSpace α] (self : TopologicalSpace.IrreducibleCloseds α), IsIrred
ucible self.carrier

--- 原说明 ---
The closed irreducible subsets of a sober space bijects with the points of the s
pace.
-/
noncomputable def irreducibleSetEquivPoints [QuasiSober α] [T0Space α] :
    TopologicalSpace.IrreducibleCloseds α ≃o α where
  toFun s := s.2.genericPoint
  invFun x := ⟨closure ({x} : Set α), isIrreducible_singleton.closure, isClosed_closure⟩
  left_inv s := by
    refine TopologicalSpace.IrreducibleCloseds.ext ?_
    simp only [IsIrreducible.genericPoint_closure_eq, TopologicalSpace.IrreducibleCloseds.coe_mk,
      closure_eq_iff_isClosed.mpr s.3]
    rfl
  right_inv x := isIrreducible_singleton.closure.isGenericPoint_genericPoint_closure.eq
      (by rw [closure_closure]; exact isGenericPoint_closure)
  map_rel_iff' := by
    rintro ⟨s, hs, hs'⟩ ⟨t, ht, ht'⟩
    refine specializes_iff_closure_subset.trans ?_
    simp
    rfl

@[simp]
/-
**coe_irreducibleEquivPoints_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_irreducibleEquivPoints_symm_apply [QuasiSober α] [T0Space α] (x : α) :
 (irreducibleSetEquivPoints.symm x : Set α) = closure {x}
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_irreducibleEquivPoints_symm_apply [QuasiSober α] [T0Space α] (x : α) :
    (irreducibleSetEquivPoints.symm x : Set α) = closure {x} := rfl
/-
**Topology.IsClosedEmbedding.quasiSober** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsClosedEmbedding.quasiSober {f : α -> β} (hf : IsClosedEmbedding
 f) [QuasiSober β] : QuasiSober α where sober hS hS'
参数：hf : IsClosedEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIrreducible.image`：IsIrreducible.image (H : IsIrreducible s) (f : X ->
 Y) (hf : ContinuousOn f s) : IsIrreducible (f '' s)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `QuasiSober.sober`：∀ {α : Type u_3} {inst : TopologicalSpace α} [self : Q
uasiSober α] {S : Set α},   IsIrreducible S → IsClosed S → ∃ x, IsGenericPoint x
 S
· 使用定理 `Topology.IsClosedEmbedding.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → IsCl…
· 使用定理 `IsGenericPoint.mem`：∀ {α : Type u_1} [inst : TopologicalSpace α] {x : α}
 {S : Set α}, IsGenericPoint x S → x ∈ S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGenericPoint.def`：IsGenericPoint.def {x : α} {S : Set α} (h : IsGeneri
cPoint x S) : closure ({x} : Set α) = S
· 使用定理 `Topology.IsClosedEmbedding.closure_image_eq`：∀ {X : Type u_1} {Y : Type 
u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   To
pology.IsClosedEmbedding f → ∀ (s…
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
-/
lemma Topology.IsClosedEmbedding.quasiSober {f : α → β} (hf : IsClosedEmbedding f) [QuasiSober β] :
    QuasiSober α where
  sober hS hS' := by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS'' (hf.isClosedMap _ hS')
    obtain ⟨y, -, rfl⟩ := hx.mem
    use y
    apply image_injective.mpr hf.injective
    rw [← hx.def, ← hf.closure_image_eq, image_singleton]
/-
**Topology.IsOpenEmbedding.quasiSober** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsOpenEmbedding.quasiSober {f : α -> β} (hf : IsOpenEmbedding f) 
[QuasiSober β] : QuasiSober α where sober hS hS'
参数：hf : IsOpenEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIrreducible.image`：IsIrreducible.image (H : IsIrreducible s) (f : X ->
 Y) (hf : ContinuousOn f s) : IsIrreducible (f '' s)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Topology.IsOpenEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Contin…
· 使用定理 `QuasiSober.sober`：∀ {α : Type u_3} {inst : TopologicalSpace α} [self : Q
uasiSober α] {S : Set α},   IsIrreducible S → IsClosed S → ∃ x, IsGenericPoint x
 S
· 使用定理 `IsIrreducible.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s :
 Set X}, IsIrreducible s → IsIrreducible (closure s)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isClosed_iff`：isClosed_iff (hf : IsInducing f) {s : 
Set X} : IsClosed s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `IsGenericPoint.mem`：∀ {α : Type u_1} [inst : TopologicalSpace α] {x : α}
 {S : Set α}, IsGenericPoint x S → x ∈ S
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `IsGenericPoint.mem_open_set_iff`：mem_open_set_iff (h : IsGenericPoint x 
S) (hU : IsOpen U) : x in U ↔ (S inter U).Nonempty
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Topology.IsEmbedding.closure_eq_preimage_closure_image`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsEmbedding f → ∀ (s : Set…
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_injective`：image_injective : Injective (image f) ↔ Injective f
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
（共 33 条，此处仅展示前 30 条）
-/
theorem Topology.IsOpenEmbedding.quasiSober {f : α → β} (hf : IsOpenEmbedding f) [QuasiSober β] :
    QuasiSober α where
  sober hS hS' := by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS''.closure isClosed_closure
    obtain ⟨T, hT, rfl⟩ := hf.isInducing.isClosed_iff.mp hS'
    rw [image_preimage_eq_inter_range] at hx hS''
    have hxT : x ∈ T := by
      rw [← hT.closure_eq]
      exact closure_mono inter_subset_left hx.mem
    obtain ⟨y, rfl⟩ : x ∈ range f := by
      rw [hx.mem_open_set_iff hf.isOpen_range]
      refine Nonempty.mono ?_ hS''.1
      simpa using subset_closure
    use y
    change _ = _
    rw [hf.isEmbedding.closure_eq_preimage_closure_image, image_singleton, show _ = _ from hx]
    apply image_injective.mpr hf.injective
    ext z
    simp only [image_preimage_eq_inter_range, mem_inter_iff, and_congr_left_iff]
    exact fun hy => ⟨fun h => hT.closure_eq ▸ closure_mono inter_subset_left h,
      fun h => subset_closure ⟨h, hy⟩⟩
/-
**TopologicalSpace.IsOpenCover.quasiSober_iff_forall** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：TopologicalSpace.IsOpenCover.quasiSober_iff_forall {ι : Type*} {U : ι -> O
pens α} (hU : TopologicalSpace.IsOpenCover U) : QuasiSober α ↔ forall i, QuasiSo
ber (U i)
参数：hU : TopologicalSpace.IsOpenCover U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.quasiSober`：Topology.IsOpenEmbedding.quasiSober
 {f : α -> β} (hf : IsOpenEmbedding f) [QuasiSober β] : QuasiSober α where sober
 hS hS'
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding'`：isOpenEmbedding' (U : Opens α) 
: IsOpenEmbedding (Subtype.val : U -> α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `quasiSober_iff`：∀ (α : Type u_3) [inst : TopologicalSpace α],   QuasiSob
er α ↔ ∀ {S : Set α}, IsIrreducible S → IsClosed S → ∃ x, IsGenericPoint x S
· 使用引理 `TopologicalSpace.IsOpenCover.exists_mem`：exists_mem (hu : IsOpenCover u)
 (a : X) : exists i, a in u i
· 使用引理 `IsPreirreducible.preimage`：IsPreirreducible.preimage (ht : IsPreirreduci
ble t) {f : Y -> X} (hf : IsOpenEmbedding f) : IsPreirreducible (f ⁻¹' t)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `IsGenericPoint.mem`：∀ {α : Type u_1} [inst : TopologicalSpace α] {x : α}
 {S : Set α}, IsGenericPoint x S → x ∈ S
· 使用定理 `IsIrreducible.isGenericPoint_genericPoint_closure`：IsIrreducible.isGener
icPoint_genericPoint_closure [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
 IsGenericPoint hS.genericPoint (closur…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `closure_image_closure`：closure_image_closure (h : Continuous f) : closur
e (f '' closure s) = closure (f '' s)
· 使用定理 `IsGenericPoint.def`：IsGenericPoint.def {x : α} {S : Set α} (h : IsGeneri
cPoint x S) : closure ({x} : Set α) = S
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure_inter_of_isPreirreducible_of_isOpen`：subset_closure_inter
_of_isPreirreducible_of_isOpen {S U : Set X} (hS : IsPreirreducible S) (hU : IsO
pen U) (h : (S inter U).Nonempty) : S su…
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
lemma TopologicalSpace.IsOpenCover.quasiSober_iff_forall {ι : Type*} {U : ι → Opens α}
    (hU : TopologicalSpace.IsOpenCover U) : QuasiSober α ↔ ∀ i, QuasiSober (U i) := by
  refine ⟨fun h i ↦ (U i).isOpenEmbedding'.quasiSober, fun hU' ↦ (quasiSober_iff _).mpr ?_⟩
  · rintro t ⟨⟨x, hx⟩, h⟩ h'
    obtain ⟨i, hi⟩ := hU.exists_mem x
    have H : IsIrreducible ((↑) ⁻¹' t : Set (U i)) :=
      ⟨⟨⟨x, hi⟩, hx⟩, h.preimage (U i).isOpenEmbedding'⟩
    use H.genericPoint
    apply le_antisymm
    · simpa [h'.closure_subset_iff, h'.closure_eq] using!
        continuous_subtype_val.closure_preimage_subset _ H.isGenericPoint_genericPoint_closure.mem
    rw [← image_singleton, ← closure_image_closure continuous_subtype_val,
      H.isGenericPoint_genericPoint_closure.def]
    refine (subset_closure_inter_of_isPreirreducible_of_isOpen h (U i).isOpen ⟨x, ⟨hx, hi⟩⟩).trans
      (closure_mono ?_)
    simpa only [inter_comm t, ← Subtype.image_preimage_coe] using! Set.image_mono subset_closure
/-
**TopologicalSpace.IsOpenCover.quasiSober** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TopologicalSpace.IsOpenCover.quasiSober {ι : Type*} {U : ι -> Opens α} (hU
 : TopologicalSpace.IsOpenCover U) [forall i, QuasiSober (U i)] : QuasiSober α
参数：hU : TopologicalSpace.IsOpenCover U；U i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`：TopologicalSpace.IsO
penCover.quasiSober_iff_forall {ι : Type*} {U : ι -> Opens α} (hU : TopologicalS
pace.IsOpenCover U) : QuasiSober α ↔ for…
-/
lemma TopologicalSpace.IsOpenCover.quasiSober {ι : Type*} {U : ι → Opens α}
    (hU : TopologicalSpace.IsOpenCover U) [∀ i, QuasiSober (U i)] : QuasiSober α :=
  hU.quasiSober_iff_forall.mpr ‹_›

/-- A space is quasi-sober if it can be covered by open quasi-sober subsets. -/
/-
**quasiSober_of_open_cover** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quasiSober_of_open_cover (S : Set (Set α)) (hS : forall s : S, IsOpen (s :
 Set α)) [forall s : S, QuasiSober s] (hS' : ⋃₀ S = ⊤) : QuasiSober α
参数：S : Set (Set α)；hS : forall s : S, IsOpen (s : Set α)；hS' : ⋃₀ S = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopologicalSpace.IsOpenCover.quasiSober`：TopologicalSpace.IsOpenCover.qu
asiSober {ι : Type*} {U : ι -> Opens α} (hU : TopologicalSpace.IsOpenCover U) [f
orall i, QuasiSober (U i)] : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i

--- 原说明 ---
A space is quasi-sober if it can be covered by open quasi-sober subsets.
-/
theorem quasiSober_of_open_cover (S : Set (Set α)) (hS : ∀ s : S, IsOpen (s : Set α))
    [∀ s : S, QuasiSober s] (hS' : ⋃₀ S = ⊤) : QuasiSober α :=
  TopologicalSpace.IsOpenCover.quasiSober (U := fun s : S ↦ ⟨s, hS s⟩) <| by
    simpa [TopologicalSpace.IsOpenCover, ← SetLike.coe_set_eq, sUnion_eq_iUnion] using hS'

/--
Any R1 space is a quasi-sober space because any irreducible set is
contained in the closure of a singleton.
-/
-- see note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) R1Space.quasiSober [R1Space α] : QuasiSober α where
  sober h hs := by
    obtain ⟨x, hx⟩ := h.nonempty
    use x
    apply subset_antisymm
    · rw [← hs.closure_eq]
      exact closure_mono (singleton_subset_iff.mpr hx)
    · exact isPreirreducible_iff_forall_mem_subset_closure_singleton.mp h.isPreirreducible x hx

open scoped Set.Notation in
/-
**QuasiSober.of_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuasiSober.of_subset {V W : Set α} [QuasiSober W] (hV : IsClosed (W ↓inter
 V)) (h : V subseteq W) : QuasiSober V
参数：hV : IsClosed (W ↓inter V)；h : V subseteq W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsClosedEmbedding.quasiSober`：Topology.IsClosedEmbedding.quasiS
ober {f : α -> β} (hf : IsClosedEmbedding f) [QuasiSober β] : QuasiSober α where
 sober hS hS'
· 使用定理 `Topology.IsClosedEmbedding.inclusion`：∀ {X : Type u} [inst : Topological
Space X] {s t : Set X} (hst : s ⊆ t),   IsClosed (Subtype.val ⁻¹' s) → Topology.
IsClosedEmbedding (Set.inc…
-/
lemma QuasiSober.of_subset {V W : Set α} [QuasiSober W] (hV : IsClosed (W ↓∩ V)) (h : V ⊆ W) :
    QuasiSober V := Topology.IsClosedEmbedding.quasiSober <| .inclusion h hV
/-
**QuasiSober.inter_of_isClosed_of_quasiSober_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuasiSober.inter_of_isClosed_of_quasiSober_left {V : Set α} (W : Set α) [Q
uasiSober W] (hV : IsClosed V) : QuasiSober (W inter V : Set α)
参数：W : Set α；hV : IsClosed V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `QuasiSober.of_subset`：QuasiSober.of_subset {V W : Set α} [QuasiSober W] 
(hV : IsClosed (W ↓inter V)) (h : V subseteq W) : QuasiSober V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.preimage_coe_self_inter`：preimage_coe_self_inter (s t : Set α) :
 ((↑) : s -> α) ⁻¹' (s inter t) = ((↑) : s -> α) ⁻¹' t
· 使用引理 `IsClosed.preimage_val`：IsClosed.preimage_val {s t : Set X} (ht : IsClose
d t) : IsClosed (s ↓inter t)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
lemma QuasiSober.inter_of_isClosed_of_quasiSober_left {V : Set α} (W : Set α) [QuasiSober W]
    (hV : IsClosed V) : QuasiSober (W ∩ V : Set α) := by
  refine QuasiSober.of_subset ?_ (Set.inter_subset_left : W ∩ V ⊆ W)
  rw [Subtype.preimage_coe_self_inter W V]
  exact IsClosed.preimage_val hV
/-
**QuasiSober.inter_of_isClosed_of_quasiSober_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuasiSober.inter_of_isClosed_of_quasiSober_right {V : Set α} (W : Set α) [
QuasiSober V] (hW : IsClosed W) : QuasiSober (W inter V : Set α)
参数：W : Set α；hW : IsClosed W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用引理 `QuasiSober.inter_of_isClosed_of_quasiSober_left`：QuasiSober.inter_of_isC
losed_of_quasiSober_left {V : Set α} (W : Set α) [QuasiSober W] (hV : IsClosed V
) : QuasiSober (W inter V : Set α)
-/
lemma QuasiSober.inter_of_isClosed_of_quasiSober_right {V : Set α} (W : Set α) [QuasiSober V]
    (hW : IsClosed W) : QuasiSober (W ∩ V : Set α) := by
  rw [inter_comm]
  exact .inter_of_isClosed_of_quasiSober_left V hW

end Sober

section genericPoints

variable (α) in
/-- The set of generic points of irreducible components. -/
/-
**genericPoints** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：genericPoints : Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of generic points of irreducible components.
-/
def genericPoints : Set α := { x | closure {x} ∈ irreducibleComponents α }

namespace genericPoints

/-- The irreducible component of a generic point -/
/-
**genericPoints.component** 是 Mathlib 中的一个定义，位于命名空间 `genericPoints`。
形式化陈述：component (x : genericPoints α) : irreducibleComponents α
参数：x : genericPoints α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The irreducible component of a generic point
-/
def component (x : genericPoints α) : irreducibleComponents α :=
  ⟨closure {x.1}, x.2⟩
/-
**genericPoints.isGenericPoint** 是 Mathlib 中的一个引理，位于命名空间 `genericPoints`。
形式化陈述：isGenericPoint (x : genericPoints α) : IsGenericPoint x.1 (component x).1
参数：x : genericPoints α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isGenericPoint (x : genericPoints α) : IsGenericPoint x.1 (component x).1 := rfl
/-
**genericPoints.component_injective** 是 Mathlib 中的一个引理，位于命名空间 `genericPoints`。
形式化陈述：component_injective [T0Space α] : Function.Injective (component (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `IsGenericPoint.eq`：∀ {α : Type u_1} [inst : TopologicalSpace α] {x y : α
} {S : Set α} [T0Space α],   IsGenericPoint x S → IsGenericPoint y S → x = y
· 使用引理 `genericPoints.isGenericPoint`：isGenericPoint (x : genericPoints α) : IsG
enericPoint x.1 (component x).1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma component_injective [T0Space α] : Function.Injective (component (α := α)) :=
  fun x y e ↦ Subtype.ext ((isGenericPoint x).eq (e ▸ isGenericPoint y))

/-- The generic point of an irreducible component. -/
noncomputable
/-
**genericPoints.ofComponent** 是 Mathlib 中的一个定义，位于命名空间 `genericPoints`。
形式化陈述：ofComponent [QuasiSober α] (x : irreducibleComponents α) : genericPoints α
参数：x : irreducibleComponents α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofComponent [QuasiSober α] (x : irreducibleComponents α) : genericPoints α :=
  ⟨x.2.1.genericPoint, show _ ∈ irreducibleComponents α from
    (x.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents x.1 x.2)).symm ▸ x.2⟩
/-
**genericPoints.isGenericPoint_ofComponent** 是 Mathlib 中的一个引理，位于命名空间 `genericPoi
nts`。
形式化陈述：isGenericPoint_ofComponent [QuasiSober α] (x : irreducibleComponents α) : 
IsGenericPoint (ofComponent x).1 x
参数：x : irreducibleComponents α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIrreducible.isGenericPoint_genericPoint`：IsIrreducible.isGenericPoint_
genericPoint [QuasiSober α] {S : Set α} (hS : IsIrreducible S) (hS' : IsClosed S
) : IsGenericPoint hS.genericPo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `isClosed_of_mem_irreducibleComponents`：isClosed_of_mem_irreducibleCompon
ents (s) (H : s in irreducibleComponents X) : IsClosed s
-/
lemma isGenericPoint_ofComponent [QuasiSober α] (x : irreducibleComponents α) :
    IsGenericPoint (ofComponent x).1 x :=
    x.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents x.1 x.2)

@[simp]
/-
**genericPoints.component_ofComponent** 是 Mathlib 中的一个引理，位于命名空间 `genericPoints`。
形式化陈述：component_ofComponent [QuasiSober α] (x : irreducibleComponents α) : compo
nent (ofComponent x) = x
参数：x : irreducibleComponents α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `genericPoints.isGenericPoint_ofComponent`：isGenericPoint_ofComponent [Qu
asiSober α] (x : irreducibleComponents α) : IsGenericPoint (ofComponent x).1 x
-/
lemma component_ofComponent [QuasiSober α] (x : irreducibleComponents α) :
    component (ofComponent x) = x :=
  Subtype.ext (isGenericPoint_ofComponent x)

@[simp]
/-
**genericPoints.ofComponent_component** 是 Mathlib 中的一个引理，位于命名空间 `genericPoints`。
形式化陈述：ofComponent_component [T0Space α] [QuasiSober α] (x : genericPoints α) : o
fComponent (component x) = x
参数：x : genericPoints α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `genericPoints.component_injective`：component_injective [T0Space α] : Fun
ction.Injective (component (α
· 使用引理 `genericPoints.component_ofComponent`：component_ofComponent [QuasiSober α
] (x : irreducibleComponents α) : component (ofComponent x) = x
-/
lemma ofComponent_component [T0Space α] [QuasiSober α] (x : genericPoints α) :
    ofComponent (component x) = x :=
  component_injective (component_ofComponent _)
/-
**genericPoints.component_surjective** 是 Mathlib 中的一个引理，位于命名空间 `genericPoints`。
形式化陈述：component_surjective [QuasiSober α] : Function.Surjective (component (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasRightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.HasRightInverse f → Function.Surjective f
· 使用引理 `genericPoints.component_ofComponent`：component_ofComponent [QuasiSober α
] (x : irreducibleComponents α) : component (ofComponent x) = x
-/
lemma component_surjective [QuasiSober α] : Function.Surjective (component (α := α)) :=
  Function.HasRightInverse.surjective ⟨ofComponent, component_ofComponent⟩
/-
**genericPoints.finite** 是 Mathlib 中的一个引理，位于命名空间 `genericPoints`。
形式化陈述：finite [T0Space α] (h : (irreducibleComponents α).Finite) : (genericPoints
 α).Finite
参数：h : (irreducibleComponents α).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_injective`：Finite.of_injective {α β : Sort*} [Finite β] (f : α
 -> β) (H : Injective f) : Finite α
· 使用引理 `genericPoints.component_injective`：component_injective [T0Space α] : Fun
ction.Injective (component (α
-/
lemma finite [T0Space α] (h : (irreducibleComponents α).Finite) : (genericPoints α).Finite :=
  @Finite.of_injective _ _ h _ component_injective

/-- In a sober space, the generic points corresponds bijectively to irreducible components -/
@[simps]
noncomputable
/-
**genericPoints.equiv** 是 Mathlib 中的一个定义，位于命名空间 `genericPoints`。
形式化陈述：equiv [T0Space α] [QuasiSober α] : genericPoints α ≃ irreducibleComponents
 α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `genericPoints.ofComponent_component`：ofComponent_component [T0Space α] [
QuasiSober α] (x : genericPoints α) : ofComponent (component x) = x
· 使用引理 `genericPoints.component_ofComponent`：component_ofComponent [QuasiSober α
] (x : irreducibleComponents α) : component (ofComponent x) = x
-/
def equiv [T0Space α] [QuasiSober α] : genericPoints α ≃ irreducibleComponents α :=
  ⟨component, ofComponent, ofComponent_component, component_ofComponent⟩
/-
**genericPoints.closure** 是 Mathlib 中的一个引理，位于命名空间 `genericPoints`。
形式化陈述：closure [QuasiSober α] : closure (genericPoints α) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.subset_def`：subset_def : (s subseteq t) = forall x, x in s -> x in t
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `irreducibleComponent_mem_irreducibleComponents`：irreducibleComponent_mem
_irreducibleComponents (x : X) : irreducibleComponent x in irreducibleComponents
 X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `genericPoints.isGenericPoint_ofComponent`：isGenericPoint_ofComponent [Qu
asiSober α] (x : irreducibleComponents α) : IsGenericPoint (ofComponent x).1 x
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mem_irreducibleComponent`：mem_irreducibleComponent {x : X} : x in irredu
cibleComponent x
-/
lemma closure [QuasiSober α] : closure (genericPoints α) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun x ↦ Set.subset_def.mp ?_ x mem_irreducibleComponent
  refine (isGenericPoint_ofComponent
    ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩).symm.trans_subset (closure_mono ?_)
  exact Set.singleton_subset_iff.mpr (ofComponent _).2

end genericPoints

/-
**genericPoints_eq_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：genericPoints_eq_singleton [QuasiSober α] [IrreducibleSpace α] [T0Space α]
 : genericPoints α = {genericPoint α}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `genericPoints.eq_1`：∀ (α : Type u_1) [inst : TopologicalSpace α], generi
cPoints α = {x | closure {x} ∈ irreducibleComponents α}
· 使用定理 `irreducibleComponents_eq_singleton`：irreducibleComponents_eq_singleton [
IrreducibleSpace X] : irreducibleComponents X = {univ}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGenericPoint.eq`：∀ {α : Type u_1} [inst : TopologicalSpace α] {x y : α
} {S : Set α} [T0Space α],   IsGenericPoint x S → IsGenericPoint y S → x = y
· 使用定理 `genericPoint_spec`：genericPoint_spec [QuasiSober α] [IrreducibleSpace α]
 : IsGenericPoint (genericPoint α) univ
-/
lemma genericPoints_eq_singleton [QuasiSober α] [IrreducibleSpace α] [T0Space α] :
    genericPoints α = {genericPoint α} := by
  ext x
  rw [genericPoints, irreducibleComponents_eq_singleton]
  exact ⟨((genericPoint_spec α).eq · |>.symm), (· ▸ genericPoint_spec α)⟩

end genericPoints

