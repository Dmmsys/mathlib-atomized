/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet
-/
module

public import Mathlib.Order.Ideal

/-!
# Order filters

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more structure,
such as a bottom element, a top element, or a join-semilattice structure.

- `Order.PFilter P`: The type of nonempty, downward directed, upward closed subsets of `P`.
               This is dual to `Order.Ideal`, so it simply wraps `Order.Ideal Pᵒᵈ`.
- `Order.IsPFilter P`: a predicate for when a `Set P` is a filter.

Note the relation between `Order/Filter` and `Order/PFilter`: for any type `α`,
`Filter α` represents the same mathematical object as `PFilter (Set α)`.

## References

- <https://en.wikipedia.org/wiki/Filter_(mathematics)>

## Tags

pfilter, filter, ideal, dual

-/

@[expose] public section

open OrderDual

namespace Order

/-- A filter on a preorder `P` is a subset of `P` that is
  - nonempty
  - downward directed
  - upward closed. -/
/-
**Order.PFilter** 是 Mathlib 中的一个归纳类型，位于命名空间 `Order`。
形式化陈述：(P : Type u_1) → [Preorder P] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filter on a preorder `P` is a subset of `P` that is
  - nonempty
  - downward directed
  - upward closed.
-/
structure PFilter (P : Type*) [Preorder P] where
  dual : Ideal Pᵒᵈ

variable {P : Type*}

/-- A predicate for when a subset of `P` is a filter. -/
/-
**Order.IsPFilter** 是 Mathlib 中的一个定义，位于命名空间 `Order`。
形式化陈述：IsPFilter [Preorder P] (F : Set P) : Prop
参数：F : Set P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate for when a subset of `P` is a filter.
-/
def IsPFilter [Preorder P] (F : Set P) : Prop :=
  IsIdeal (OrderDual.ofDual ⁻¹' F)
/-
**Order.IsPFilter.of_def** 是 Mathlib 中的一个定理，位于命名空间 `Order.IsPFilter`。
形式化陈述：∀ {P : Type u_1} [inst : Preorder P] {F : Set P},   F.Nonempty → DirectedO
n (fun x1 x2 => x1 ≥ x2) F → (∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) → Order.IsPFil
ter F
参数：fun x1 x2 => x1 ≥ x2；∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsPFilter.of_def [Preorder P] {F : Set P} (nonempty : F.Nonempty)
    (directed : DirectedOn (· ≥ ·) F) (mem_of_le : ∀ {x y : P}, x ≤ y → x ∈ F → y ∈ F) :
    IsPFilter F :=
  ⟨fun _ _ _ _ => mem_of_le ‹_› ‹_›, nonempty, directed⟩

/-- Create an element of type `Order.PFilter` from a set satisfying the predicate
`Order.IsPFilter`. -/
/-
**Order.IsPFilter.toPFilter** 是 Mathlib 中的一个定义，位于命名空间 `Order.IsPFilter`。
形式化陈述：{P : Type u_1} → [inst : Preorder P] → {F : Set P} → Order.IsPFilter F → O
rder.PFilter P
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create an element of type `Order.PFilter` from a set satisfying the predicate
`Order.IsPFilter`.
-/
def IsPFilter.toPFilter [Preorder P] {F : Set P} (h : IsPFilter F) : PFilter P :=
  ⟨h.toIdeal⟩

namespace PFilter

section Preorder

variable [Preorder P] {x y : P} (F s t : PFilter P)

/-
**Order.PFilter.** 是 Mathlib 中的一个实例，位于命名空间 `Order.PFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited P] : Inhabited (PFilter P) := ⟨⟨default⟩⟩

/-- A filter on `P` is a subset of `P`. -/
/-
**Order.PFilter.** 是 Mathlib 中的一个实例，位于命名空间 `Order.PFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filter on `P` is a subset of `P`.
-/
instance : SetLike (PFilter P) P where
  coe F := toDual ⁻¹' F.dual.carrier
  coe_injective := fun ⟨_⟩ ⟨_⟩ h => congr_arg mk <| Ideal.ext h
/-
**Order.PFilter.** 是 Mathlib 中的一个实例，位于命名空间 `Order.PFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (PFilter P) := .ofSetLike (PFilter P) P
/-
**Order.PFilter.isPFilter** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：isPFilter : IsPFilter (F : Set P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.isIdeal`：∀ {P : Type u_1} [inst : LE P] (s : Order.Ideal P),
 Order.IsIdeal ↑s
-/
theorem isPFilter : IsPFilter (F : Set P) := F.dual.isIdeal
/-
**Order.PFilter.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：∀ {P : Type u_1} [inst : Preorder P] (F : Order.PFilter P), (↑F).Nonempty
参数：F : Order.PFilter P；↑F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.nonempty`：∀ {P : Type u_1} [inst : LE P] (s : Order.Ideal P)
, (↑s).Nonempty
-/
protected theorem nonempty : (F : Set P).Nonempty := F.dual.nonempty
/-
**Order.PFilter.directed** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：directed : DirectedOn (· >= ·) (F : Set P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.directed`：∀ {P : Type u_1} [inst : LE P] (s : Order.Ideal P)
, DirectedOn (fun x1 x2 => x1 ≤ x2) ↑s
-/
theorem directed : DirectedOn (· ≥ ·) (F : Set P) := F.dual.directed
/-
**Order.PFilter.mem_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：mem_of_le {F : PFilter P} : x <= y -> x in F -> y in F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.lower`：∀ {P : Type u_1} [inst : LE P] (s : Order.Ideal P), I
sLowerSet ↑s
-/
theorem mem_of_le {F : PFilter P} : x ≤ y → x ∈ F → y ∈ F := fun h => F.dual.lower h

/-- Two filters are equal when their underlying sets are equal. -/
@[ext]
/-
**Order.PFilter.ext** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：ext (h : (s : Set P) = t) : s = t
参数：h : (s : Set P) = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q

--- 原说明 ---
Two filters are equal when their underlying sets are equal.
-/
theorem ext (h : (s : Set P) = t) : s = t := SetLike.ext' h

@[trans]
/-
**Order.PFilter.mem_of_mem_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：mem_of_mem_of_le {F G : PFilter P} (hx : x in F) (hle : F <= G) : x in G
参数：hx : x in F；hle : F <= G。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_of_mem_of_le {F G : PFilter P} (hx : x ∈ F) (hle : F ≤ G) : x ∈ G :=
  hle hx

/-- The smallest filter containing a given element. -/
/-
**Order.PFilter.principal** 是 Mathlib 中的一个定义，位于命名空间 `Order.PFilter`。
形式化陈述：principal (p : P) : PFilter P
参数：p : P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The smallest filter containing a given element.
-/
def principal (p : P) : PFilter P :=
  ⟨Ideal.principal (toDual p)⟩

@[simp]
/-
**Order.PFilter.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：mem_mk (x : P) (I : Ideal Pᵒᵈ) : x in (⟨I⟩ : PFilter P) ↔ toDual x in I
参数：x : P；I : Ideal Pᵒᵈ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk (x : P) (I : Ideal Pᵒᵈ) : x ∈ (⟨I⟩ : PFilter P) ↔ toDual x ∈ I :=
  Iff.rfl

@[simp]
/-
**Order.PFilter.principal_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：principal_le_iff {F : PFilter P} : principal x <= F ↔ x in F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.principal_le_iff`：principal_le_iff : principal x <= I ↔ x in
 I
-/
theorem principal_le_iff {F : PFilter P} : principal x ≤ F ↔ x ∈ F :=
  Ideal.principal_le_iff (x := toDual x)
/-
**Order.PFilter.mem_principal** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：∀ {P : Type u_1} [inst : Preorder P] {x y : P}, x ∈ Order.PFilter.principa
l y ↔ y ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_principal : x ∈ principal y ↔ y ≤ x := Iff.rfl
/-
**Order.PFilter.principal_le_principal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFil
ter`。
形式化陈述：principal_le_principal_iff {p q : P} : principal q <= principal p ↔ p <= q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem principal_le_principal_iff {p q : P} : principal q ≤ principal p ↔ p ≤ q := by simp

-- defeq abuse
/-
**Order.PFilter.antitone_principal** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：antitone_principal : Antitone (principal : P -> PFilter P)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.PFilter.principal_le_principal_iff`：principal_le_principal_iff {p 
q : P} : principal q <= principal p ↔ p <= q
-/
theorem antitone_principal : Antitone (principal : P → PFilter P) := fun _ _ =>
  principal_le_principal_iff.2

end Preorder

section OrderTop

variable [Preorder P] [OrderTop P] {F : PFilter P}

/-- A specific witness of `pfilter.nonempty` when `P` has a top element. -/
/-
**Order.PFilter.top_mem** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：∀ {P : Type u_1} [inst : Preorder P] [inst_1 : OrderTop P] {F : Order.PFil
ter P}, ⊤ ∈ F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.bot_mem`：bot_mem (s : Ideal P) : ⊥ in s

--- 原说明 ---
A specific witness of `pfilter.nonempty` when `P` has a top element.
-/
@[simp] theorem top_mem : ⊤ ∈ F := Ideal.bot_mem _

/-- There is a bottom filter when `P` has a top element. -/
/-
**Order.PFilter.** 是 Mathlib 中的一个实例，位于命名空间 `Order.PFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a bottom filter when `P` has a top element.
-/
instance : OrderBot (PFilter P) where
  bot := ⟨⊥⟩
  bot_le F := (bot_le : ⊥ ≤ F.dual)

end OrderTop

/-- There is a top filter when `P` has a bottom element. -/
/-
**Order.PFilter.** 是 Mathlib 中的一个实例，位于命名空间 `Order.PFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a top filter when `P` has a bottom element.
-/
instance {P} [Preorder P] [OrderBot P] : OrderTop (PFilter P) where
  top := ⟨⊤⟩
  le_top F := (le_top : F.dual ≤ ⊤)

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {F : PFilter P}

/-- A specific witness of `pfilter.directed` when `P` has meets. -/
/-
**Order.PFilter.inf_mem** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：inf_mem (hx : x in F) (hy : y in F) : x ⊓ y in F
参数：hx : x in F；hy : y in F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.sup_mem`：sup_mem (hx : x in s) (hy : y in s) : x ⊔ y in s

--- 原说明 ---
A specific witness of `pfilter.directed` when `P` has meets.
-/
theorem inf_mem (hx : x ∈ F) (hy : y ∈ F) : x ⊓ y ∈ F :=
  Ideal.sup_mem hx hy

@[simp]
/-
**Order.PFilter.inf_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：inf_mem_iff : x ⊓ y in F ↔ x in F ∧ y in F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.Ideal.sup_mem_iff`：sup_mem_iff : x ⊔ y in I ↔ x in I ∧ y in I
-/
theorem inf_mem_iff : x ⊓ y ∈ F ↔ x ∈ F ∧ y ∈ F :=
  Ideal.sup_mem_iff

end SemilatticeInf

section CompleteSemilatticeInf

variable [CompleteSemilatticeInf P]

/-
**Order.PFilter.sInf_gc** 是 Mathlib 中的一个定理，位于命名空间 `Order.PFilter`。
形式化陈述：sInf_gc : GaloisConnection (fun x => toDual (principal x)) fun F => sInf (
ofDual F : PFilter P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sInf_gc :
    GaloisConnection (fun x => toDual (principal x)) fun F => sInf (ofDual F : PFilter P) :=
  fun x F => by simp only [le_sInf_iff, SetLike.mem_coe, toDual_le, SetLike.le_def, mem_principal]

/-- If a poset `P` admits arbitrary `Inf`s, then `principal` and `Inf` form a Galois coinsertion. -/
/-
**Order.PFilter.infGi** 是 Mathlib 中的一个定义，位于命名空间 `Order.PFilter`。
形式化陈述：infGi : GaloisCoinsertion (fun x => toDual (principal x)) fun F => sInf (o
fDual F : PFilter P)
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Order.PFilter.sInf_gc`：sInf_gc : GaloisConnection (fun x => toDual (prin
cipal x)) fun F => sInf (ofDual F : PFilter P)

--- 原说明 ---
If a poset `P` admits arbitrary `Inf`s, then `principal` and `Inf` form a Galois
 coinsertion.
-/
def infGi :
    GaloisCoinsertion (fun x => toDual (principal x)) fun F => sInf (ofDual F : PFilter P) :=
  sInf_gc.toGaloisCoinsertion fun _ => sInf_le <| mem_principal.2 le_rfl

end CompleteSemilatticeInf

end PFilter

end Order

