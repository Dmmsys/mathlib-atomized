/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.Antisymmetrization

/-!
# Comparability and incomparability relations

Two values in a preorder are said to be comparable (`SymmRel`) whenever `a ≤ b` or `b ≤ a`. We
define both the comparability and incomparability relations.

In a linear order, `SymmGen (· ≤ ·) a b` is always true, and `IncompRel (· ≤ ·) a b` is always
false.

## Implementation notes

Although comparability and incomparability are negations of each other, both relations are
convenient in different contexts, and as such, it's useful to keep them distinct. To move from one
to the other, use `not_symmGen_iff` and `not_incompRel_iff_symmGen`.

## Main declarations

* `CompRel`: The comparability relation. `CompRel r a b` means that `a` and `b` is related in
  either direction by `r`. This is deprecated in favor of `Relation.SymmGen`, with naming chosen for
  consistency with `Relation.TransGen` in core and other definitions in `Mathlib.Logic.Relation`.
* `IncompRel`: The incomparability relation. `IncompRel r a b` means that `a` and `b` are related in
  neither direction by `r`.

## Todo

These definitions should be linked to `IsChain` and `IsAntichain`.
-/

@[expose] public section

open Function Relation

variable {α : Type*} {a b c d : α}

/-! ### Comparability -/

section Relation

variable {r : α → α → Prop}

/-- The comparability relation `CompRel r a b` means that either `r a b` or `r b a`. -/
@[deprecated SymmGen (since := "2026-01-25")]
/-
**CompRel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CompRel (r : α -> α -> Prop) (a b : α) : Prop
参数：r : α -> α -> Prop；a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparability relation `CompRel r a b` means that either `r a b` or `r b a`.
-/
def CompRel (r : α → α → Prop) (a b : α) : Prop :=
  r a b ∨ r b a

@[deprecated SymmGen.of_rel (since := "2026-01-25")]
/-
**CompRel.of_rel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.of_rel (h : r a b) : CompRel r a b
参数：h : r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_rel`：of_rel (h : r a b) : SymmGen r a b
-/
theorem CompRel.of_rel (h : r a b) : CompRel r a b :=
  SymmGen.of_rel h

@[deprecated SymmGen.of_rel_symm (since := "2026-01-25")]
/-
**CompRel.of_rel_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.of_rel_symm (h : r b a) : CompRel r a b
参数：h : r b a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_rel_symm`：of_rel_symm (h : r b a) : SymmGen r a b
-/
theorem CompRel.of_rel_symm (h : r b a) : CompRel r a b :=
  SymmGen.of_rel_symm h

@[deprecated symmGen_swap (since := "2026-01-25")]
/-
**compRel_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compRel_swap (r : α -> α -> Prop) : CompRel (swap r) = CompRel r
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.symmGen_swap`：symmGen_swap (r : α -> α -> Prop) : SymmGen (swap
 r) = SymmGen r
-/
theorem compRel_swap (r : α → α → Prop) : CompRel (swap r) = CompRel r :=
  symmGen_swap r

@[deprecated symmGen_swap_apply (since := "2026-01-25")]
/-
**compRel_swap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compRel_swap_apply (r : α -> α -> Prop) : CompRel (swap r) a b ↔ CompRel r
 a b
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.symmGen_swap_apply`：symmGen_swap_apply (r : α -> α -> Prop) : S
ymmGen (swap r) a b ↔ SymmGen r a b
-/
theorem compRel_swap_apply (r : α → α → Prop) : CompRel (swap r) a b ↔ CompRel r a b :=
  symmGen_swap_apply r

@[simp, refl, deprecated SymmGen.refl (since := "2026-01-25")]
/-
**CompRel.refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.refl (r : α -> α -> Prop) [Std.Refl r] (a : α) : CompRel r a a
参数：r : α -> α -> Prop；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.refl`：refl (r : α -> α -> Prop) [Std.Refl r] (a : α) : 
SymmGen r a a
-/
theorem CompRel.refl (r : α → α → Prop) [Std.Refl r] (a : α) : CompRel r a a :=
  SymmGen.refl r a

@[deprecated SymmGen.rfl (since := "2026-01-25")]
/-
**CompRel.rfl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.rfl [Std.Refl r] : CompRel r a a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.rfl`：rfl [Std.Refl r] : SymmGen r a a
-/
theorem CompRel.rfl [Std.Refl r] : CompRel r a a := SymmGen.rfl

@[deprecated SymmGen.instRefl (since := "2026-01-25")]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Refl r] : Std.Refl (CompRel r) :=
  SymmGen.instRefl

@[symm, deprecated SymmGen.symm (since := "2026-01-25")]
/-
**CompRel.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.symm : CompRel r a b -> CompRel r b a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.symm`：symm : SymmGen r a b -> SymmGen r b a
-/
theorem CompRel.symm : CompRel r a b → CompRel r b a :=
  SymmGen.symm

@[deprecated SymmGen.instSymm (since := "2026-01-25")]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm (CompRel r) :=
  SymmGen.instSymm

@[deprecated symmGen_comm (since := "2026-01-25")]
/-
**compRel_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compRel_comm {a b : α} : CompRel r a b ↔ CompRel r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.symmGen_comm`：symmGen_comm {a b : α} : SymmGen r a b ↔ SymmGen 
r b a
-/
theorem compRel_comm {a b : α} : CompRel r a b ↔ CompRel r b a :=
  symmGen_comm

@[deprecated SymmGen.decidableRel (since := "2026-01-25")]
/-
**CompRel.decidableRel** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CompRel.decidableRel [DecidableRel r] : DecidableRel (CompRel r)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance CompRel.decidableRel [DecidableRel r] : DecidableRel (CompRel r) :=
  SymmGen.decidableRel

@[deprecated AntisymmRel.symmGen (since := "2026-01-25")]
/-
**AntisymmRel.compRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.compRel (h : AntisymmRel r a b) : CompRel r a b
参数：h : AntisymmRel r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.symmGen`：AntisymmRel.symmGen (h : AntisymmRel r a b) : SymmG
en r a b
-/
theorem AntisymmRel.compRel (h : AntisymmRel r a b) : CompRel r a b :=
  AntisymmRel.symmGen h

@[simp, deprecated symmGen_of_total (since := "2026-01-25")]
/-
**compRel_of_total** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compRel_of_total [Std.Total r] (a b : α) : CompRel r a b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.symmGen_of_total`：symmGen_of_total [Std.Total r] (a b : α) : Sy
mmGen r a b
-/
theorem compRel_of_total [Std.Total r] (a b : α) : CompRel r a b :=
  symmGen_of_total a b

@[deprecated (since := "2026-01-13")] alias IsTotal.compRel := symmGen_of_total

end Relation

section LE

variable [LE α]

@[deprecated SymmGen.of_le (since := "2026-01-25")]
/-
**CompRel.of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.of_le (h : a <= b) : CompRel (· <= ·) a b
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_le`：of_le {α : Type*} [LE α] {a b : α} (h : a <= b) 
: SymmGen (· <= ·) a b
-/
theorem CompRel.of_le (h : a ≤ b) : CompRel (· ≤ ·) a b := SymmGen.of_le h

@[deprecated SymmGen.of_ge (since := "2026-01-25")]
/-
**CompRel.of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.of_ge (h : b <= a) : CompRel (· <= ·) a b
参数：h : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_ge`：of_ge {α : Type*} [LE α] {a b : α} (h : b <= a) 
: SymmGen (· <= ·) a b
-/
theorem CompRel.of_ge (h : b ≤ a) : CompRel (· ≤ ·) a b := SymmGen.of_ge h

alias LE.le.compRel := CompRel.of_le
alias LE.le.compRel_symm := CompRel.of_ge

end LE

section Preorder

variable [Preorder α]

@[deprecated SymmGen.of_lt (since := "2026-01-25")]
/-
**CompRel.of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.of_lt (h : a < b) : CompRel (· <= ·) a b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_lt`：Relation.SymmGen.of_lt (h : a < b) : SymmGen (· 
<= ·) a b
-/
theorem CompRel.of_lt (h : a < b) : CompRel (· ≤ ·) a b := SymmGen.of_lt h

@[deprecated SymmGen.of_gt (since := "2026-01-25")]
/-
**CompRel.of_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.of_gt (h : b < a) : CompRel (· <= ·) a b
参数：h : b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_gt`：Relation.SymmGen.of_gt (h : b < a) : SymmGen (· 
<= ·) a b
-/
theorem CompRel.of_gt (h : b < a) : CompRel (· ≤ ·) a b := SymmGen.of_gt h

alias LT.lt.compRel := CompRel.of_lt
alias LT.lt.compRel_symm := CompRel.of_gt

@[trans, deprecated SymmGen.of_symmGen_of_antisymmRel (since := "2026-01-25")]
/-
**CompRel.of_compRel_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.of_compRel_of_antisymmRel (h₁ : CompRel (· <= ·) a b) (h₂ : Antisy
mmRel (· <= ·) b c) : CompRel (· <= ·) a c
参数：h₁ : CompRel (· <= ·) a b；h₂ : AntisymmRel (· <= ·) b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_symmGen_of_antisymmRel`：Relation.SymmGen.of_symmGen_
of_antisymmRel (h₁ : SymmGen (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) b c) : Sym
mGen (· <= ·) a c
-/
theorem CompRel.of_compRel_of_antisymmRel
    (h₁ : CompRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) b c) : CompRel (· ≤ ·) a c :=
  SymmGen.of_symmGen_of_antisymmRel h₁ h₂

alias CompRel.trans_antisymmRel := CompRel.of_compRel_of_antisymmRel

@[deprecated instTransSymmGenLeAntisymmRel (since := "2026-01-25")]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans α α α (CompRel (· ≤ ·)) (AntisymmRel (· ≤ ·)) (CompRel (· ≤ ·)) :=
  instTransSymmGenLeAntisymmRel

@[trans, deprecated SymmGen.of_antisymmRel_of_symmGen (since := "2026-01-25")]
/-
**CompRel.of_antisymmRel_of_compRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompRel.of_antisymmRel_of_compRel (h₁ : AntisymmRel (· <= ·) a b) (h₂ : Co
mpRel (· <= ·) b c) : CompRel (· <= ·) a c
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : CompRel (· <= ·) b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_antisymmRel_of_symmGen`：Relation.SymmGen.of_antisymm
Rel_of_symmGen (h₁ : AntisymmRel (· <= ·) a b) (h₂ : SymmGen (· <= ·) b c) : Sym
mGen (· <= ·) a c
-/
theorem CompRel.of_antisymmRel_of_compRel
    (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : CompRel (· ≤ ·) b c) : CompRel (· ≤ ·) a c :=
  SymmGen.of_antisymmRel_of_symmGen h₁ h₂

alias AntisymmRel.trans_compRel := CompRel.of_antisymmRel_of_compRel
@[deprecated instTransAntisymmRelLeSymmGen (since := "2026-01-25")]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans α α α (AntisymmRel (· ≤ ·)) (CompRel (· ≤ ·)) (CompRel (· ≤ ·)) :=
  instTransAntisymmRelLeSymmGen

@[deprecated AntisymmRel.symmGen_congr (since := "2026-01-25")]
/-
**AntisymmRel.compRel_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.compRel_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRe
l (· <= ·) c d) : CompRel (· <= ·) a c ↔ CompRel (· <= ·) b d
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : AntisymmRel (· <= ·) c d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.symmGen_congr`：AntisymmRel.symmGen_congr (h₁ : AntisymmRel (
· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) : SymmGen (· <= ·) a c ↔ SymmGen (·
 <= ·) b d wher…
-/
theorem AntisymmRel.compRel_congr (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    CompRel (· ≤ ·) a c ↔ CompRel (· ≤ ·) b d :=
  AntisymmRel.symmGen_congr h₁ h₂

@[deprecated AntisymmRel.symmGen_congr_left (since := "2026-01-25")]
/-
**AntisymmRel.compRel_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.compRel_congr_left (h : AntisymmRel (· <= ·) a b) : CompRel (·
 <= ·) a c ↔ CompRel (· <= ·) b c
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.symmGen_congr_left`：AntisymmRel.symmGen_congr_left (h : Anti
symmRel (· <= ·) a b) : SymmGen (· <= ·) a c ↔ SymmGen (· <= ·) b c
-/
theorem AntisymmRel.compRel_congr_left (h : AntisymmRel (· ≤ ·) a b) :
    CompRel (· ≤ ·) a c ↔ CompRel (· ≤ ·) b c :=
  AntisymmRel.symmGen_congr_left h

@[deprecated AntisymmRel.symmGen_congr_right (since := "2026-01-25")]
/-
**AntisymmRel.compRel_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.compRel_congr_right (h : AntisymmRel (· <= ·) b c) : CompRel (
· <= ·) a b ↔ CompRel (· <= ·) a c
参数：h : AntisymmRel (· <= ·) b c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.symmGen_congr_right`：AntisymmRel.symmGen_congr_right (h : An
tisymmRel (· <= ·) b c) : SymmGen (· <= ·) a b ↔ SymmGen (· <= ·) a c
-/
theorem AntisymmRel.compRel_congr_right (h : AntisymmRel (· ≤ ·) b c) :
    CompRel (· ≤ ·) a b ↔ CompRel (· ≤ ·) a c :=
  AntisymmRel.symmGen_congr_right h

end Preorder

/-- A partial order where any two elements are comparable is a linear order. -/
@[instance_reducible]
/-
**Relation.linearOrderOfSymmGen** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Relation.linearOrderOfSymmGen [PartialOrder α] [decLE : DecidableLE α] [de
cLT : DecidableLT α] [decEq : DecidableEq α] (h : forall a b : α, Relation.SymmG
en (· <= ·) a b) : LinearOrder α where le_total
参数：h : forall a b : α, Relation.SymmGen (· <= ·) a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial order where any two elements are comparable is a linear order.
-/
def Relation.linearOrderOfSymmGen [PartialOrder α]
    [decLE : DecidableLE α] [decLT : DecidableLT α] [decEq : DecidableEq α]
    (h : ∀ a b : α, Relation.SymmGen (· ≤ ·) a b) : LinearOrder α where
  le_total := h
  toDecidableLE := decLE
  toDecidableEq := decEq
  toDecidableLT := decLT

/-- A partial order where any two elements are comparable is a linear order. -/
@[deprecated linearOrderOfSymmGen (since := "2026-01-25"), instance_reducible]
/-
**linearOrderOfComprel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：linearOrderOfComprel [PartialOrder α] [decLE : DecidableLE α] [decLT : Dec
idableLT α] [decEq : DecidableEq α] (h : forall a b : α, CompRel (· <= ·) a b) :
 LinearOrder α
参数：h : forall a b : α, CompRel (· <= ·) a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial order where any two elements are comparable is a linear order.
-/
def linearOrderOfComprel [PartialOrder α]
    [decLE : DecidableLE α] [decLT : DecidableLT α] [decEq : DecidableEq α]
    (h : ∀ a b : α, CompRel (· ≤ ·) a b) : LinearOrder α :=
  linearOrderOfSymmGen h

/-! ### Incomparability relation -/

section Relation

variable (r : α → α → Prop)

/-- The incomparability relation `IncompRel r a b` means `¬ r a b` and `¬ r b a`. -/
/-
**IncompRel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IncompRel (a b : α) : Prop
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The incomparability relation `IncompRel r a b` means `¬ r a b` and `¬ r b a`.
-/
def IncompRel (a b : α) : Prop :=
  ¬ r a b ∧ ¬ r b a

@[simp]
/-
**antisymmRel_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymmRel_compl : AntisymmRel rᶜ = IncompRel r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem antisymmRel_compl : AntisymmRel rᶜ = IncompRel r :=
  rfl
/-
**antisymmRel_compl_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antisymmRel_compl_apply : AntisymmRel rᶜ a b ↔ IncompRel r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem antisymmRel_compl_apply : AntisymmRel rᶜ a b ↔ IncompRel r a b :=
  .rfl

@[simp]
/-
**incompRel_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：incompRel_compl : IncompRel rᶜ = AntisymmRel r
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
theorem incompRel_compl : IncompRel rᶜ = AntisymmRel r := by
  simp [← antisymmRel_compl, compl]

@[simp]
/-
**incompRel_compl_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：incompRel_compl_apply : IncompRel rᶜ a b ↔ AntisymmRel r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `incompRel_compl`：incompRel_compl : IncompRel rᶜ = AntisymmRel r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem incompRel_compl_apply : IncompRel rᶜ a b ↔ AntisymmRel r a b := by
  simp
/-
**incompRel_swap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：incompRel_swap : IncompRel (swap r) = IncompRel r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antisymmRel_swap`：antisymmRel_swap : AntisymmRel (swap r) = AntisymmRel 
r
-/
theorem incompRel_swap : IncompRel (swap r) = IncompRel r :=
  antisymmRel_swap rᶜ
/-
**incompRel_swap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：incompRel_swap_apply : IncompRel (swap r) a b ↔ IncompRel r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antisymmRel_swap_apply`：antisymmRel_swap_apply : AntisymmRel (swap r) a 
b ↔ AntisymmRel r a b
-/
theorem incompRel_swap_apply : IncompRel (swap r) a b ↔ IncompRel r a b :=
  antisymmRel_swap_apply rᶜ

@[simp, refl]
/-
**IncompRel.refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IncompRel.refl [Std.Irrefl r] (a : α) : IncompRel r a a
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.refl`：AntisymmRel.refl [Std.Refl r] (a : α) : AntisymmRel r 
a a
-/
theorem IncompRel.refl [Std.Irrefl r] (a : α) : IncompRel r a a :=
  AntisymmRel.refl rᶜ a

variable {r}
/-
**IncompRel.rfl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IncompRel.rfl [Std.Irrefl r] {a : α} : IncompRel r a a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IncompRel.refl`：IncompRel.refl [Std.Irrefl r] (a : α) : IncompRel r a a
-/
theorem IncompRel.rfl [Std.Irrefl r] {a : α} : IncompRel r a a := .refl ..
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Irrefl r] : Std.Refl (IncompRel r) where
  refl := .refl r

@[symm]
/-
**IncompRel.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IncompRel.symm : IncompRel r a b -> IncompRel r b a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem IncompRel.symm : IncompRel r a b → IncompRel r b a :=
  And.symm
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm (IncompRel r) where
  symm _ _ := IncompRel.symm
/-
**incompRel_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：incompRel_comm {a b : α} : IncompRel r a b ↔ IncompRel r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comm`：comm [Std.Symm r] {a b : α} : r a b ↔ r b a
· 使用定理 `instSymmIncompRel`：∀ {α : Type u_1} {r : α → α → Prop}, Std.Symm (Incomp
Rel r)
-/
theorem incompRel_comm {a b : α} : IncompRel r a b ↔ IncompRel r b a :=
  comm
/-
**IncompRel.decidableRel** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IncompRel.decidableRel [DecidableRel r] : DecidableRel (IncompRel r)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IncompRel.decidableRel [DecidableRel r] : DecidableRel (IncompRel r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (¬ _ ∧ ¬ _))
/-
**IncompRel.not_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IncompRel.not_antisymmRel (h : IncompRel r a b) : ¬ AntisymmRel r a b
参数：h : IncompRel r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IncompRel.not_antisymmRel (h : IncompRel r a b) : ¬ AntisymmRel r a b :=
  fun h' ↦ h.1 h'.1
/-
**AntisymmRel.not_incompRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.not_incompRel (h : AntisymmRel r a b) : ¬ IncompRel r a b
参数：h : AntisymmRel r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem AntisymmRel.not_incompRel (h : AntisymmRel r a b) : ¬ IncompRel r a b :=
  fun h' ↦ h'.1 h.1
/-
**not_symmGen_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_symmGen_iff : ¬ Relation.SymmGen r a b ↔ IncompRel r a b
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
theorem not_symmGen_iff : ¬ Relation.SymmGen r a b ↔ IncompRel r a b := by
  simp [Relation.SymmGen, IncompRel]

@[deprecated not_symmGen_iff (since := "2026-01-25")]
/-
**not_compRel_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_compRel_iff : ¬ CompRel r a b ↔ IncompRel r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_symmGen_iff`：not_symmGen_iff : ¬ Relation.SymmGen r a b ↔ IncompRel 
r a b
-/
theorem not_compRel_iff : ¬ CompRel r a b ↔ IncompRel r a b :=
  not_symmGen_iff
/-
**not_incompRel_iff_symmGen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_incompRel_iff_symmGen : ¬ IncompRel r a b ↔ Relation.SymmGen r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_symmGen_iff`：not_symmGen_iff : ¬ Relation.SymmGen r a b ↔ IncompRel 
r a b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_incompRel_iff_symmGen : ¬ IncompRel r a b ↔ Relation.SymmGen r a b := by
  rw [← not_symmGen_iff, not_not]

@[deprecated not_incompRel_iff_symmGen (since := "2026-01-25")]
/-
**not_incompRel_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_incompRel_iff : ¬ IncompRel r a b ↔ CompRel r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_incompRel_iff_symmGen`：not_incompRel_iff_symmGen : ¬ IncompRel r a b
 ↔ Relation.SymmGen r a b
-/
theorem not_incompRel_iff : ¬ IncompRel r a b ↔ CompRel r a b :=
  not_incompRel_iff_symmGen

@[simp]
/-
**not_incompRel_of_total** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_incompRel_of_total [Std.Total r] (a b : α) : ¬ IncompRel r a b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_incompRel_iff_symmGen`：not_incompRel_iff_symmGen : ¬ IncompRel r a b
 ↔ Relation.SymmGen r a b
· 使用定理 `Relation.symmGen_of_total`：symmGen_of_total [Std.Total r] (a b : α) : Sy
mmGen r a b
-/
theorem not_incompRel_of_total [Std.Total r] (a b : α) : ¬ IncompRel r a b := by
  rw [not_incompRel_iff_symmGen]
  exact symmGen_of_total a b

@[deprecated (since := "2026-01-13")] alias IsTotal.not_incompRel := not_incompRel_of_total
/-
**IncompRel.ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IncompRel.ne [Std.Refl r] {a b : α} (h : IncompRel r a b) : a != b
参数：h : IncompRel r a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `refl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
-/
theorem IncompRel.ne [Std.Refl r] {a b : α} (h : IncompRel r a b) : a ≠ b := by
  rintro rfl
  exact h.1 <| refl_of r a

end Relation

section LE

variable [LE α]

/-
**IncompRel.not_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IncompRel.not_le (h : IncompRel (· <= ·) a b) : ¬ a <= b
参数：h : IncompRel (· <= ·) a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IncompRel.not_le (h : IncompRel (· ≤ ·) a b) : ¬ a ≤ b := h.1
/-
**IncompRel.not_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IncompRel.not_ge (h : IncompRel (· <= ·) a b) : ¬ b <= a
参数：h : IncompRel (· <= ·) a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IncompRel.not_ge (h : IncompRel (· ≤ ·) a b) : ¬ b ≤ a := h.2
/-
**LE.le.not_incompRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LE.le.not_incompRel (h : a <= b) : ¬ IncompRel (· <= ·) a b
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IncompRel.not_le`：IncompRel.not_le (h : IncompRel (· <= ·) a b) : ¬ a <=
 b
-/
theorem LE.le.not_incompRel (h : a ≤ b) : ¬ IncompRel (· ≤ ·) a b := fun h' ↦ h'.not_le h

end LE

section Preorder

variable [Preorder α]

/-
**IncompRel.not_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IncompRel.not_lt (h : IncompRel (· <= ·) a b) : ¬ a < b
参数：h : IncompRel (· <= ·) a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IncompRel.not_le`：IncompRel.not_le (h : IncompRel (· <= ·) a b) : ¬ a <=
 b
-/
theorem IncompRel.not_lt (h : IncompRel (· ≤ ·) a b) : ¬ a < b := mt le_of_lt h.not_le
/-
**IncompRel.not_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IncompRel.not_gt (h : IncompRel (· <= ·) a b) : ¬ b < a
参数：h : IncompRel (· <= ·) a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IncompRel.not_ge`：IncompRel.not_ge (h : IncompRel (· <= ·) a b) : ¬ b <=
 a
-/
theorem IncompRel.not_gt (h : IncompRel (· ≤ ·) a b) : ¬ b < a := mt le_of_lt h.not_ge
/-
**LT.lt.not_incompRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LT.lt.not_incompRel (h : a < b) : ¬ IncompRel (· <= ·) a b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IncompRel.not_lt`：IncompRel.not_lt (h : IncompRel (· <= ·) a b) : ¬ a < 
b
-/
theorem LT.lt.not_incompRel (h : a < b) : ¬ IncompRel (· ≤ ·) a b := fun h' ↦ h'.not_lt h
/-
**not_le_iff_lt_or_incompRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_le_iff_lt_or_incompRel : ¬ b <= a ↔ a < b ∨ IncompRel (· <= ·) a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `IncompRel.eq_1`：∀ {α : Type u_1} (r : α → α → Prop) (a b : α), IncompRel
 r a b = (¬r a b ∧ ¬r b a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
-/
theorem not_le_iff_lt_or_incompRel : ¬ b ≤ a ↔ a < b ∨ IncompRel (· ≤ ·) a b := by
  rw [lt_iff_le_not_ge, IncompRel]
  tauto

/-- Exactly one of the following is true. -/
/-
**lt_or_antisymmRel_or_gt_or_incompRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_or_antisymmRel_or_gt_or_incompRel (a b : α) : a < b ∨ AntisymmRel (· <=
 ·) a b ∨ b < a ∨ IncompRel (· <= ·) a b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.not_and_iff_not_or_not'`：∀ {b a : Prop} [Decidable b], ¬(a ∧ b
) ↔ ¬a ∨ ¬b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p

--- 原说明 ---
Exactly one of the following is true.
-/
theorem lt_or_antisymmRel_or_gt_or_incompRel (a b : α) :
    a < b ∨ AntisymmRel (· ≤ ·) a b ∨ b < a ∨ IncompRel (· ≤ ·) a b := by
  simp_rw [lt_iff_le_not_ge]
  tauto

@[trans]
/-
**incompRel_of_incompRel_of_antisymmRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：incompRel_of_incompRel_of_antisymmRel (h₁ : IncompRel (· <= ·) a b) (h₂ : 
AntisymmRel (· <= ·) b c) : IncompRel (· <= ·) a c
参数：h₁ : IncompRel (· <= ·) a b；h₂ : AntisymmRel (· <= ·) b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IncompRel.not_le`：IncompRel.not_le (h : IncompRel (· <= ·) a b) : ¬ a <=
 b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AntisymmRel.ge`：AntisymmRel.ge (h : AntisymmRel (· <= ·) a b) : b <= a
· 使用定理 `IncompRel.not_ge`：IncompRel.not_ge (h : IncompRel (· <= ·) a b) : ¬ b <=
 a
· 使用定理 `AntisymmRel.le`：AntisymmRel.le (h : AntisymmRel (· <= ·) a b) : a <= b
-/
theorem incompRel_of_incompRel_of_antisymmRel
    (h₁ : IncompRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) b c) : IncompRel (· ≤ ·) a c :=
  ⟨fun h ↦ h₁.not_le (h.trans h₂.ge), fun h ↦ h₁.not_ge (h₂.le.trans h)⟩

alias IncompRel.trans_antisymmRel := incompRel_of_incompRel_of_antisymmRel
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans α α α (IncompRel (· ≤ ·)) (AntisymmRel (· ≤ ·)) (IncompRel (· ≤ ·)) where
  trans := incompRel_of_incompRel_of_antisymmRel

@[trans]
/-
**incompRel_of_antisymmRel_of_incompRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：incompRel_of_antisymmRel_of_incompRel (h₁ : AntisymmRel (· <= ·) a b) (h₂ 
: IncompRel (· <= ·) b c) : IncompRel (· <= ·) a c
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : IncompRel (· <= ·) b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IncompRel.symm`：IncompRel.symm : IncompRel r a b -> IncompRel r b a
· 使用定理 `IncompRel.trans_antisymmRel`：∀ {α : Type u_1} {a b c : α} [inst : Preord
er α],   IncompRel (fun x1 x2 => x1 ≤ x2) a b → AntisymmRel (fun x1 x2 => x1 ≤ x
2) b c → IncompRe…
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem incompRel_of_antisymmRel_of_incompRel
    (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : IncompRel (· ≤ ·) b c) : IncompRel (· ≤ ·) a c :=
  (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_incompRel := incompRel_of_antisymmRel_of_incompRel
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Trans α α α (AntisymmRel (· ≤ ·)) (IncompRel (· ≤ ·)) (IncompRel (· ≤ ·)) where
  trans := incompRel_of_antisymmRel_of_incompRel
/-
**AntisymmRel.incompRel_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.incompRel_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : Antisymm
Rel (· <= ·) c d) : IncompRel (· <= ·) a c ↔ IncompRel (· <= ·) b d where mp h
参数：h₁ : AntisymmRel (· <= ·) a b；h₂ : AntisymmRel (· <= ·) c d。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IncompRel.trans_antisymmRel`：∀ {α : Type u_1} {a b c : α} [inst : Preord
er α],   IncompRel (fun x1 x2 => x1 ≤ x2) a b → AntisymmRel (fun x1 x2 => x1 ≤ x
2) b c → IncompRe…
· 使用定理 `AntisymmRel.trans_incompRel`：∀ {α : Type u_1} {a b c : α} [inst : Preord
er α],   AntisymmRel (fun x1 x2 => x1 ≤ x2) a b → IncompRel (fun x1 x2 => x1 ≤ x
2) b c → IncompRe…
· 使用定理 `AntisymmRel.symm`：AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r 
b a
-/
theorem AntisymmRel.incompRel_congr (h₁ : AntisymmRel (· ≤ ·) a b) (h₂ : AntisymmRel (· ≤ ·) c d) :
    IncompRel (· ≤ ·) a c ↔ IncompRel (· ≤ ·) b d where
  mp h := (h₁.symm.trans_incompRel h).trans_antisymmRel h₂
  mpr h := (h₁.trans_incompRel h).trans_antisymmRel h₂.symm
/-
**AntisymmRel.incompRel_congr_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.incompRel_congr_left (h : AntisymmRel (· <= ·) a b) : IncompRe
l (· <= ·) a c ↔ IncompRel (· <= ·) b c
参数：h : AntisymmRel (· <= ·) a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.incompRel_congr`：AntisymmRel.incompRel_congr (h₁ : AntisymmR
el (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) : IncompRel (· <= ·) a c ↔ Inco
mpRel (· <= ·) b …
· 使用引理 `AntisymmRel.rfl`：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a 
a
-/
theorem AntisymmRel.incompRel_congr_left (h : AntisymmRel (· ≤ ·) a b) :
    IncompRel (· ≤ ·) a c ↔ IncompRel (· ≤ ·) b c :=
  h.incompRel_congr AntisymmRel.rfl
/-
**AntisymmRel.incompRel_congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntisymmRel.incompRel_congr_right (h : AntisymmRel (· <= ·) b c) : IncompR
el (· <= ·) a b ↔ IncompRel (· <= ·) a c
参数：h : AntisymmRel (· <= ·) b c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntisymmRel.incompRel_congr`：AntisymmRel.incompRel_congr (h₁ : AntisymmR
el (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) : IncompRel (· <= ·) a c ↔ Inco
mpRel (· <= ·) b …
· 使用引理 `AntisymmRel.rfl`：AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a 
a
-/
theorem AntisymmRel.incompRel_congr_right (h : AntisymmRel (· ≤ ·) b c) :
    IncompRel (· ≤ ·) a b ↔ IncompRel (· ≤ ·) a c :=
  AntisymmRel.rfl.incompRel_congr h

end Preorder

/-- Exactly one of the following is true. -/
/-
**lt_or_eq_or_gt_or_incompRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_or_eq_or_gt_or_incompRel [PartialOrder α] (a b : α) : a < b ∨ a = b ∨ b
 < a ∨ IncompRel (· <= ·) a b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lt_or_antisymmRel_or_gt_or_incompRel`：lt_or_antisymmRel_or_gt_or_incompR
el (a b : α) : a < b ∨ AntisymmRel (· <= ·) a b ∨ b < a ∨ IncompRel (· <= ·) a b

--- 原说明 ---
Exactly one of the following is true.
-/
theorem lt_or_eq_or_gt_or_incompRel [PartialOrder α] (a b : α) :
    a < b ∨ a = b ∨ b < a ∨ IncompRel (· ≤ ·) a b := by
  simpa using lt_or_antisymmRel_or_gt_or_incompRel a b
