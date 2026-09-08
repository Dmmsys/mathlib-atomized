/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.SetNotation

/-!
# Definition of complete lattices

This file contains the definition of complete lattices with suprema/infima of arbitrary sets.

## Main definitions

* `sSup` and `sInf` are the supremum and the infimum of a set;
* `iSup (f : ι → α)` and `iInf (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `sSup` and `sInf` of the range of this function;
* class `CompleteLattice`: a bounded lattice such that `sSup s` is always the least upper boundary
  of `s` and `sInf s` is always the greatest lower boundary of `s`;
* class `CompleteLinearOrder`: a linear ordered complete lattice.

## Naming conventions

In lemma names,
* `sSup` is called `sSup`
* `sInf` is called `sInf`
* `⨆ i, s i` is called `iSup`
* `⨅ i, s i` is called `iInf`
* `⨆ i j, s i j` is called `iSup₂`. This is an `iSup` inside an `iSup`.
* `⨅ i j, s i j` is called `iInf₂`. This is an `iInf` inside an `iInf`.
* `⨆ i ∈ s, t i` is called `biSup` for "bounded `iSup`". This is the special case of `iSup₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `biInf` for "bounded `iInf`". This is the special case of `iInf₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `iSup f`, the supremum of the range of `f`;
* `⨅ i, f i` : `iInf f`, the infimum of the range of `f`.
-/

@[expose] public section

open Function OrderDual Set

variable {α β γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

@[to_dual]
/-
**OrderDual.supSet** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.supSet (α) [h : InfSet α] : SupSet αᵒᵈ
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.supSet (α) [h : InfSet α] : SupSet αᵒᵈ :=
  ⟨fun s ↦ h.sInf s⟩

/-- Note that we rarely use `CompleteSemilatticeSup`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
/-
**CompleteSemilatticeSup** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_8 → Type u_8
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that we rarely use `CompleteSemilatticeSup`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to
 start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeSup (α : Type*) extends PartialOrder α, SupSet α where
  /-- Every set has a least upper bound. -/
  isLUB_sSup : ∀ s : Set α, IsLUB s (sSup s)

/-- Note that we rarely use `CompleteSemilatticeInf`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
@[to_dual]
/-
**CompleteSemilatticeInf** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_8 → Type u_8
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that we rarely use `CompleteSemilatticeInf`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to
 start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeInf (α : Type*) extends PartialOrder α, InfSet α where
  /-- Every set has a greatest lower bound. -/
  isGLB_sInf : ∀ s : Set α, IsGLB s (sInf s)

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b l : α} {f : ι → α}

@[to_dual]
/-
**isLUB_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSemilatticeSup.isLUB_sSup`：∀ {α : Type u_8} [self : CompleteSemi
latticeSup α] (s : Set α), IsLUB s (sSup s)
-/
theorem isLUB_sSup (s : Set α) : IsLUB s (sSup s) :=
  CompleteSemilatticeSup.isLUB_sSup _

@[to_dual sInf_le]
/-
**le_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sSup (h : a in s) : a <= sSup s
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem le_sSup (h : a ∈ s) : a ≤ sSup s :=
  (isLUB_sSup s).1 h

@[to_dual le_sInf]
/-
**sSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_le (h : forall b in s, b <= a) : sSup s <= a
参数：h : forall b in s, b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem sSup_le (h : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  (isLUB_sSup s).2 h

@[to_dual]
/-
**isLUB_iff_sSup_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLUB_iff_sSup_eq : IsLUB s a ↔ sSup s = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
lemma isLUB_iff_sSup_eq : IsLUB s a ↔ sSup s = a :=
  ⟨(isLUB_sSup s).unique, by rintro rfl; exact isLUB_sSup _⟩

@[to_dual]
alias ⟨IsLUB.sSup_eq, _⟩ := isLUB_iff_sSup_eq

@[to_dual]
/-
**sSup_mem_upperBounds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_mem_upperBounds : sSup s in upperBounds s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem sSup_mem_upperBounds : sSup s ∈ upperBounds s :=
  (isLUB_le_iff <| isLUB_sSup s).mp <| refl _

@[to_dual sInf_le_of_le]
/-
**le_sSup_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sSup_of_le (hb : b in s) (h : a <= b) : a <= sSup s
参数：hb : b in s；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem le_sSup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_sSup hb)

@[to_dual (attr := gcongr)]
/-
**sSup_le_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.mono`：IsLUB.mono (ha : IsLUB s a) (hb : IsLUB t b) (hst : s subset
eq t) : a <= b
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem sSup_le_sSup (h : s ⊆ t) : sSup s ≤ sSup t :=
  (isLUB_sSup s).mono (isLUB_sSup t) h

@[to_dual (attr := simp) le_sInf_iff]
/-
**sSup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_le_iff : sSup s <= a ↔ forall b in s, b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem sSup_le_iff : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_sSup s)

@[to_dual sInf_le_iff]
/-
**le_sSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sSup_iff : a <= sSup s ↔ forall b in upperBounds s, a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem le_sSup_iff : a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h _ hb => le_trans h (sSup_le hb), fun hb => hb _ fun _ => le_sSup⟩

@[to_dual iInf_le_iff]
/-
**le_iSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall i, s i <= b) ->
 a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_iSup_iff {s : ι → α} : a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  simp [iSup, le_sSup_iff, upperBounds]

@[to_dual lt_sInf_iff]
/-
**sSup_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_lt_iff : sSup s < l ↔ exists b < l, b in upperBounds s where mp hsl
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_mem_upperBounds`：sSup_mem_upperBounds : sSup s in upperBounds s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sSup_le_iff`：sSup_le_iff : sSup s <= a ↔ forall b in s, b <= a
-/
theorem sSup_lt_iff : sSup s < l ↔ ∃ b < l, b ∈ upperBounds s where
  mp hsl := ⟨sSup s, hsl, sSup_mem_upperBounds⟩
  mpr := fun ⟨_, hbl, hbs⟩ ↦ sSup_le_iff.mpr hbs |>.trans_lt hbl

@[to_dual lt_iInf_iff]
/-
**iSup_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_lt_iff : iSup f < l ↔ exists b < l, forall i, f i <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `sSup_lt_iff`：sSup_lt_iff : sSup s < l ↔ exists b < l, b in upperBounds s
 where mp hsl
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem iSup_lt_iff : iSup f < l ↔ ∃ b < l, ∀ i, f i ≤ b :=
  sSup_lt_iff.trans <| exists_congr fun _ ↦ and_congr_right fun _ ↦ forall_mem_range

end

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [CompleteSemilatticeInf α] : CompleteSemilatticeSup αᵒᵈ where
  isLUB_sSup := isGLB_sInf (α := α)

/-- A complete lattice is a bounded lattice which has suprema and infima for every subset. -/
/-
**CompleteLattice** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：CompleteLattice (α : Type*) extends Lattice α, CompleteSemilatticeSup α, C
ompleteSemilatticeInf α, BoundedOrder α  attribute [to_dual existing] CompleteLa
ttice.toCompleteSemilatticeInf CompleteLattice.toInfSet attribute [to_dual self 
(reorder
参数：α : Type*。
继承自：Lattice α, CompleteSemilatticeSup α, CompleteSemilatticeInf α, BoundedOrder 
α  attribute [to_dual existing] CompleteLattice.toCompleteSemilatticeInf Complet
eLattice.toInfSet attribute [to_dual self (reorder。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete lattice is a bounded lattice which has suprema and infima for every s
ubset.
-/
class CompleteLattice (α : Type*) extends Lattice α, CompleteSemilatticeSup α,
    CompleteSemilatticeInf α, BoundedOrder α

attribute [to_dual existing] CompleteLattice.toCompleteSemilatticeInf CompleteLattice.toInfSet
attribute [to_dual self (reorder := toSupSet toInfSet, isLUB_sSup isGLB_sInf)] CompleteLattice.mk

-- Shortcut instance to ensure that the path
-- `CompleteLattice α → CompletePartialOrder α → PartialOrder α` isn't taken,
-- as it tricks `#min_imports` into believing `Order.CompletePartialOrder` is a necessary import.
-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CompleteLattice.toPartialOrder' [CompleteLattice α] : PartialOrder α :=
  inferInstance

/-- Create a `CompleteLattice` from a `PartialOrder` and `InfSet`
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `CompleteLattice`
instance as
```
instance : CompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sSup, bot, top
  __ := completeLatticeOfInf my_T _
```
-/
@[instance_reducible]
/-
**completeLatticeOfInf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completeLatticeOfInf (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α] (is
GLB_sInf : forall s : Set α, IsGLB s (sInf s)) : CompleteLattice α where __
参数：α : Type*；isGLB_sInf : forall s : Set α, IsGLB s (sInf s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `CompleteLattice` from a `PartialOrder` and `InfSet`
that returns the greatest lower bound of a set. Usually this constructor provide
s
poor definitional equalities.  If other fields are known explicitly, they should
 be
provided; for example, if `inf` is known explicitly, construct the `CompleteLatt
ice`
instance as
```
instance : CompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sSup, bot, top
  __ := completeLatticeOfInf my_T _
```
-/
def completeLatticeOfInf (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α]
    (isGLB_sInf : ∀ s : Set α, IsGLB s (sInf s)) : CompleteLattice α where
  __ := H1; __ := H2
  bot := sInf univ
  bot_le _ := (isGLB_sInf univ).1 trivial
  top := sInf ∅
  le_top a := (isGLB_sInf ∅).2 <| by simp
  sup a b := sInf { x : α | a ≤ x ∧ b ≤ x }
  inf a b := sInf {a, b}
  le_inf a b c hab hac := by
    apply (isGLB_sInf _).2
    simp [*]
  inf_le_right _ _ := (isGLB_sInf _).1 <| mem_insert_of_mem _ <| mem_singleton _
  inf_le_left _ _ := (isGLB_sInf _).1 <| mem_insert _ _
  sup_le a b c hac hbc := (isGLB_sInf _).1 <| by simp [*]
  le_sup_left _ _ := (isGLB_sInf _).2 fun _ => And.left
  le_sup_right _ _ := (isGLB_sInf _).2 fun _ => And.right
  sSup s := sInf (upperBounds s)
  isGLB_sInf := isGLB_sInf
  isLUB_sSup s := isGLB_upperBounds.mp (isGLB_sInf _)

/-- Any `CompleteSemilatticeInf` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfInf`.
-/
@[instance_reducible]
/-
**completeLatticeOfCompleteSemilatticeInf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completeLatticeOfCompleteSemilatticeInf (α : Type*) [CompleteSemilatticeIn
f α] : CompleteLattice α
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] (s : Set 
α), IsGLB s (sInf s)

--- 原说明 ---
Any `CompleteSemilatticeInf` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfInf`.
-/
def completeLatticeOfCompleteSemilatticeInf (α : Type*) [CompleteSemilatticeInf α] :
    CompleteLattice α :=
  completeLatticeOfInf α fun s => isGLB_sInf s

/-- Create a `CompleteLattice` from a `PartialOrder` and `SupSet`
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `CompleteLattice`
instance as
```
instance : CompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sInf, bot, top
  __ := completeLatticeOfSup my_T _
```
-/
@[instance_reducible]
/-
**completeLatticeOfSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completeLatticeOfSup (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α] (is
LUB_sSup : forall s : Set α, IsLUB s (sSup s)) : CompleteLattice α where __
参数：α : Type*；isLUB_sSup : forall s : Set α, IsLUB s (sSup s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a `CompleteLattice` from a `PartialOrder` and `SupSet`
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should
 be
provided; for example, if `inf` is known explicitly, construct the `CompleteLatt
ice`
instance as
```
instance : CompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sInf, bot, top
  __ := completeLatticeOfSup my_T _
```
-/
def completeLatticeOfSup (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (isLUB_sSup : ∀ s : Set α, IsLUB s (sSup s)) : CompleteLattice α where
  __ := H1; __ := H2
  top := sSup univ
  le_top _ := (isLUB_sSup univ).1 trivial
  bot := sSup ∅
  bot_le x := (isLUB_sSup ∅).2 <| by simp
  sup a b := sSup {a, b}
  sup_le a b c hac hbc := (isLUB_sSup _).2 (by simp [*])
  le_sup_left _ _ := (isLUB_sSup _).1 <| mem_insert _ _
  le_sup_right _ _ := (isLUB_sSup _).1 <| mem_insert_of_mem _ <| mem_singleton _
  inf a b := sSup { x | x ≤ a ∧ x ≤ b }
  le_inf a b c hab hac := (isLUB_sSup _).1 <| by simp [*]
  inf_le_left _ _ := (isLUB_sSup _).2 fun _ => And.left
  inf_le_right _ _ := (isLUB_sSup _).2 fun _ => And.right
  sInf s := sSup (lowerBounds s)
  isLUB_sSup := isLUB_sSup
  isGLB_sInf s := isLUB_lowerBounds.mp (isLUB_sSup _)

/-- Any `CompleteSemilatticeSup` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfSup`.
-/
@[instance_reducible]
/-
**completeLatticeOfCompleteSemilatticeSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completeLatticeOfCompleteSemilatticeSup (α : Type*) [CompleteSemilatticeSu
p α] : CompleteLattice α
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)

--- 原说明 ---
Any `CompleteSemilatticeSup` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfSup`.
-/
def completeLatticeOfCompleteSemilatticeSup (α : Type*) [CompleteSemilatticeSup α] :
    CompleteLattice α :=
  completeLatticeOfSup α fun s => isLUB_sSup s

/-- A complete linear order is a linear order whose lattice structure is complete. -/
-- Note that we do not use `extends LinearOrder α`,
-- and instead construct the forgetful instance manually.
/-
**CompleteLinearOrder** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：CompleteLinearOrder (α : Type*) extends CompleteLattice α, BiheytingAlgebr
a α, Ord α where /-- A linear order is total. -/ le_total (a b : α) : a <= b ∨ b
 <= a /-- In a linearly ordered type, we assume the order relations are all deci
dable. -/ toDecidableLE : DecidableLE α /-- In a linearly ordered type, we assum
e the order relations are all decidable. -/ toDecidableEq : DecidableEq α
参数：α : Type*；a b : α。
继承自：CompleteLattice α, BiheytingAlgebra α, Ord α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class CompleteLinearOrder (α : Type*) extends CompleteLattice α, BiheytingAlgebra α, Ord α where
  /-- A linear order is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLE : DecidableLE α
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ toDecidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  toDecidableLT : DecidableLT α := @decidableLTOfDecidableLE _ _ toDecidableLE
  compare a b := compareOfLessAndEq a b
  /-- Comparison via `compare` is equal to the canonical comparison given decidable `<` and `=`. -/
  compare_eq_compareOfLessAndEq : ∀ a b, compare a b = compareOfLessAndEq a b := by
    compareOfLessAndEq_rfl
/-
**CompleteLinearOrder.toLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CompleteLinearOrder.toLinearOrder [i : CompleteLinearOrder α] : LinearOrde
r α where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteLinearOrder.le_total`：∀ {α : Type u_8} [self : CompleteLinearOrd
er α] (a b : α), a ≤ b ∨ b ≤ a
· 使用定理 `CompleteLinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : Type u_8} [sel
f : CompleteLinearOrder α] (a b : α), compare a b = compareOfLessAndEq a b
-/
instance CompleteLinearOrder.toLinearOrder [i : CompleteLinearOrder α] : LinearOrder α where
  __ := i
  min_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]
  max_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]

namespace OrderDual

/-
**OrderDual.instCompleteLattice** 是 Mathlib 中的一个定义，位于命名空间 `OrderDual`。
形式化陈述：{α : Type u_1} → [CompleteLattice α] → CompleteLattice αᵒᵈ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompleteLattice [CompleteLattice α] : CompleteLattice αᵒᵈ where
/-
**OrderDual.instCompleteLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：instCompleteLinearOrder [CompleteLinearOrder α] : CompleteLinearOrder αᵒᵈ 
where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompleteLinearOrder [CompleteLinearOrder α] : CompleteLinearOrder αᵒᵈ where
  __ := instCompleteLattice
  __ := instBiheytingAlgebra
  __ := instLinearOrder α

end OrderDual

open OrderDual

section

section OrderDual

@[to_dual (attr := simp)]
/-
**toDual_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_sSup [SupSet α] (s : Set α) : toDual (sSup s) = sInf (ofDual ⁻¹' s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_sSup [SupSet α] (s : Set α) : toDual (sSup s) = sInf (ofDual ⁻¹' s) :=
  rfl

@[to_dual (attr := simp)]
/-
**ofDual_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_sSup [InfSet α] (s : Set αᵒᵈ) : ofDual (sSup s) = sInf (toDual ⁻¹' 
s)
参数：s : Set αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_sSup [InfSet α] (s : Set αᵒᵈ) : ofDual (sSup s) = sInf (toDual ⁻¹' s) :=
  rfl

@[to_dual (attr := simp)]
/-
**toDual_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDual_iSup [SupSet α] (f : ι -> α) : toDual (⨆ i, f i) = ⨅ i, toDual (f i
)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_iSup [SupSet α] (f : ι → α) : toDual (⨆ i, f i) = ⨅ i, toDual (f i) :=
  rfl

@[to_dual (attr := simp)]
/-
**ofDual_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofDual_iSup [InfSet α] (f : ι -> αᵒᵈ) : ofDual (⨆ i, f i) = ⨅ i, ofDual (f
 i)
参数：f : ι -> αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_iSup [InfSet α] (f : ι → αᵒᵈ) : ofDual (⨆ i, f i) = ⨅ i, ofDual (f i) :=
  rfl

end OrderDual

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s : Set α} {a b l : α} {f : ι → α}

@[to_dual sInf_lt_iff]
/-
**lt_sSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_sSup_iff : b < sSup s ↔ exists a in s, b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_isLUB_iff`：lt_isLUB_iff (h : IsLUB s a) : b < a ↔ exists c in s, b < 
c
· 使用定理 `isLUB_sSup`：isLUB_sSup (s : Set α) : IsLUB s (sSup s)
-/
theorem lt_sSup_iff : b < sSup s ↔ ∃ a ∈ s, b < a :=
  lt_isLUB_iff <| isLUB_sSup s

@[to_dual iInf_lt_iff]
/-
**lt_iSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_iSup_iff : a < iSup f ↔ exists i, a < f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `lt_sSup_iff`：lt_sSup_iff : b < sSup s ↔ exists a in s, b < a
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)
-/
theorem lt_iSup_iff : a < iSup f ↔ ∃ i, a < f i :=
  lt_sSup_iff.trans exists_range_iff

@[to_dual sInf_le_iff_forall_lt]
/-
**le_sSup_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_sSup_iff_forall_lt : l <= sSup s ↔ forall b < l, exists a in s, b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_sSup_iff_forall_lt : l ≤ sSup s ↔ ∀ b < l, ∃ a ∈ s, b < a := by
  grind [sSup_lt_iff, mem_upperBounds, not_le]

@[to_dual iInf_le_iff_forall_lt]
/-
**le_iSup_iff_forall_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iSup_iff_forall_lt : l <= iSup f ↔ forall b < l, exists i, b < f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `le_sSup_iff_forall_lt`：le_sSup_iff_forall_lt : l <= sSup s ↔ forall b < 
l, exists a in s, b < a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)
-/
theorem le_iSup_iff_forall_lt : l ≤ iSup f ↔ ∀ b < l, ∃ i, b < f i :=
  le_sSup_iff_forall_lt.trans <| forall₂_congr fun _ _ ↦ exists_range_iff

@[to_dual]
/-
**sSup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_eq_top : sSup s = ⊤ ↔ forall b < ⊤, exists a in s, b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `le_sSup_iff_forall_lt`：le_sSup_iff_forall_lt : l <= sSup s ↔ forall b < 
l, exists a in s, b < a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sSup_eq_top : sSup s = ⊤ ↔ ∀ b < ⊤, ∃ a ∈ s, b < a := by
  rw [eq_top_iff, le_sSup_iff_forall_lt]

@[to_dual]
/-
**iSup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_eq_top : iSup f = ⊤ ↔ forall b < ⊤, exists i, b < f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `le_iSup_iff_forall_lt`：le_iSup_iff_forall_lt : l <= iSup f ↔ forall b < 
l, exists i, b < f i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iSup_eq_top : iSup f = ⊤ ↔ ∀ b < ⊤, ∃ i, b < f i := by
  rw [eq_top_iff, le_iSup_iff_forall_lt]

@[to_dual]
/-
**lt_biSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_biSup_iff {s : Set β} {f : β -> α} : a < ⨆ i in s, f i ↔ exists i in s,
 a < f i
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_biSup_iff {s : Set β} {f : β → α} : a < ⨆ i ∈ s, f i ↔ ∃ i ∈ s, a < f i := by
  simp [lt_iSup_iff]

end CompleteLinearOrder

end

namespace Equiv

variable (e : α ≃ β)

/-- Transfer `SupSet` across an `Equiv`. -/
/-
**Equiv.supSet** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [SupSet β] → SupSet α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer `SupSet` across an `Equiv`.
-/
protected abbrev supSet [SupSet β] : SupSet α where
  sSup s := e.symm (⨆ a ∈ s, e a)
/-
**Equiv.supSet_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：supSet_def [SupSet β] (s : Set α) : letI
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma supSet_def [SupSet β] (s : Set α) :
    letI := e.supSet
    sSup s = e.symm (⨆ a ∈ s, e a) := rfl

/-- Transfer `InfSet` across an `Equiv`. -/
/-
**Equiv.infSet** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [InfSet β] → InfSet α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer `InfSet` across an `Equiv`.
-/
protected abbrev infSet [InfSet β] : InfSet α where
  sInf s := e.symm (⨅ a ∈ s, e a)
/-
**Equiv.infSet_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：infSet_def [InfSet β] (s : Set α) : letI
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma infSet_def [InfSet β] (s : Set α) :
    letI := e.infSet
    sInf s = e.symm (⨅ a ∈ s, e a) := rfl

end Equiv

