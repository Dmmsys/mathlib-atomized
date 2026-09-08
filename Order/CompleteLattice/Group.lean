/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.OrderDual
public import Mathlib.Order.CompleteLattice.Basic

/-! # Complete lattices and groups -/

public section

variable {α : Type*} {ι : Sort*} {κ : ι → Sort*}
  [CompleteLattice α] [Mul α] [MulLeftMono α] [MulRightMono α]

@[to_additive]
/-
**iSup_mul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iSup_mul_le (u v : ι -> α) : ⨆ i, u i * v i <= (⨆ i, u i) * ⨆ i, v i
参数：u v : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma iSup_mul_le (u v : ι → α) :
    ⨆ i, u i * v i ≤ (⨆ i, u i) * ⨆ i, v i :=
  iSup_le fun _ ↦ mul_le_mul' (le_iSup ..) (le_iSup ..)

@[to_additive]
/-
**le_iInf_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_iInf_mul (u v : ι -> α) : (⨅ i, u i) * ⨅ i, v i <= ⨅ i, u i * v i
参数：u v : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `iSup_mul_le`：iSup_mul_le (u v : ι -> α) : ⨆ i, u i * v i <= (⨆ i, u i) *
 ⨆ i, v i
-/
lemma le_iInf_mul (u v : ι → α) :
    (⨅ i, u i) * ⨅ i, v i ≤ ⨅ i, u i * v i :=
  iSup_mul_le (α := αᵒᵈ) ..

@[to_additive]
/-
**iSup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSup [SupSet α] (s : ι -> α) : α
参数：s : ι -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iSup₂_mul_le (u v : (i : ι) → κ i → α) :
    ⨆ (i) (j), u i j * v i j ≤ (⨆ (i) (j), u i j) * ⨆ (i) (j), v i j := by
  refine le_trans ?_ (iSup_mul_le ..)
  gcongr
  exact iSup_mul_le ..

@[to_additive]
/-
**le_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f : ι → α} {a 
: α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
参数：∀ (i : ι), a ≤ f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
-/
lemma le_iInf₂_mul (u v : (i : ι) → κ i → α) :
    (⨅ (i) (j), u i j) * ⨅ (i) (j), v i j ≤ ⨅ (i) (j), u i j * v i j :=
  iSup₂_mul_le (α := αᵒᵈ) ..
