/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# `Finset.sup` in a group with zero
-/

public section

namespace Finset
variable {ι M₀ G₀ : Type*}

section MonoidWithZero
variable [MonoidWithZero M₀] {s : Finset ι} {a b : ι → M₀}

/-
**Finset.sup_mul_le_mul_sup_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_mul_le_mul_sup_of_nonneg [SemilatticeSup M₀] [OrderBot M₀] [PosMulMono
 M₀] [MulPosMono M₀] (ha : forall i in s, 0 <= a i) (hb : forall i in s, 0 <= b 
i) : s.sup (a * b) <= s.sup a * s.sup b
参数：ha : forall i in s, 0 <= a i；hb : forall i in s, 0 <= b i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma sup_mul_le_mul_sup_of_nonneg [SemilatticeSup M₀] [OrderBot M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) : s.sup (a * b) ≤ s.sup a * s.sup b :=
  Finset.sup_le fun _i hi ↦
    mul_le_mul (le_sup hi) (le_sup hi) (hb _ hi) ((ha _ hi).trans <| le_sup hi)
/-
**Finset.mul_inf_le_inf_mul_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_inf_le_inf_mul_of_nonneg [SemilatticeInf M₀] [OrderTop M₀] [PosMulMono
 M₀] [MulPosMono M₀] (ha : forall i in s, 0 <= a i) (hb : forall i in s, 0 <= b 
i) : s.inf a * s.inf b <= s.inf (a * b)
参数：ha : forall i in s, 0 <= a i；hb : forall i in s, 0 <= b i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_inf`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, a ≤ f b) 
→ a…
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `Finset.inf_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α]
 [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β},   b ∈ s → s.inf f ≤ f
 b
-/
lemma mul_inf_le_inf_mul_of_nonneg [SemilatticeInf M₀] [OrderTop M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) : s.inf a * s.inf b ≤ s.inf (a * b) :=
  Finset.le_inf fun i hi ↦ mul_le_mul (inf_le hi) (inf_le hi) (Finset.le_inf hb) (ha i hi)
/-
**Finset.sup'_mul_le_mul_sup'_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M₀ : Type u_2} [inst : MonoidWithZero M₀] {s : Finset ι}
 {a b : ι → M₀} [inst_1 : SemilatticeSup M₀]   [PosMulMono M₀] [MulPosMono M₀], 
  (∀ i ∈ s, 0 ≤ a i) → (∀ i ∈ s, 0 ≤ b i) → ∀ (hs : s.Nonempty), s.sup' hs (a * 
b) ≤ s.sup' hs a * s.sup' hs b
参数：∀ i ∈ s, 0 ≤ a i；∀ i ∈ s, 0 ≤ b i；hs : s.Nonempty；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma sup'_mul_le_mul_sup'_of_nonneg [SemilatticeSup M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hs) :
    s.sup' hs (a * b) ≤ s.sup' hs a * s.sup' hs b :=
  sup'_le _ _ fun _i hi ↦
    mul_le_mul (le_sup' _ hi) (le_sup' _ hi) (hb _ hi) ((ha _ hi).trans <| le_sup' _ hi)
/-
**Finset.inf'_mul_le_mul_inf'_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M₀ : Type u_2} [inst : MonoidWithZero M₀] {s : Finset ι}
 {a b : ι → M₀} [inst_1 : SemilatticeInf M₀]   [PosMulMono M₀] [MulPosMono M₀], 
  (∀ i ∈ s, 0 ≤ a i) → (∀ i ∈ s, 0 ≤ b i) → ∀ (hs : s.Nonempty), s.inf' hs a * s
.inf' hs b ≤ s.inf' hs (a * b)
参数：∀ i ∈ s, 0 ≤ a i；∀ i ∈ s, 0 ≤ b i；hs : s.Nonempty；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.le_inf'`：le_inf'_image₂ {g : γ -> δ} {a : δ} (h : (image₂ f s t).
Nonempty) : a <= inf' (image₂ f s t) h g ↔ forall x in s, forall y in t, a <= g 
(f x…
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `Finset.inf'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α
] {s : Finset β} (f : β → α) {b : β} (h : b ∈ s),   s.inf' ⋯ f ≤ f b
-/
lemma inf'_mul_le_mul_inf'_of_nonneg [SemilatticeInf M₀] [PosMulMono M₀] [MulPosMono M₀]
    (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i) (hs) :
    s.inf' hs a * s.inf' hs b ≤ s.inf' hs (a * b) :=
  le_inf' _ _ fun _i hi ↦ mul_le_mul (inf'_le _ hi) (inf'_le _ hi) (le_inf' _ _ hb) (ha _ hi)

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀] [SemilatticeSup G₀] {s : Finset ι} {a : G₀}

/-
**Finset.sup'_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_4} [inst : Group G] [inst_1 : LinearOrder G] 
[MulRightMono G] (s : Finset ι) (f : ι → G)   (a : G) (hs : s.Nonempty), s.sup' 
hs f * a = s.sup' hs fun i => f i * a
参数：s : Finset ι；f : ι → G；a : G；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_sup'`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Typ
e u_5} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   [inst_2 : FunLike
 F α …
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `OrderHomClass.toLatticeHomClass`：∀ {F : Type u_1} (α : Type u_2) (β : Ty
pe u_3) [inst : FunLike F α β] [inst_1 : LinearOrder α] [inst_2 : Lattice β]   [
OrderHomClass F α β],…
· 使用定理 `RelIso.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r ≃r s) r s
-/
lemma sup'_mul₀ [MulPosReflectLT G₀] (ha : 0 ≤ a) (f : ι → G₀) (s : Finset ι) (hs) :
    s.sup' hs f * a = s.sup' hs fun i ↦ f i * a := by
  by_cases! h : 0 = a
  · simp [← h]
  exact map_finset_sup' (OrderIso.mulRight₀ _ (lt_of_le_of_ne ha h)) hs f

set_option linter.docPrime false in
/-
**Finset.mul** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：{α : Type u_2} → [DecidableEq α] → [Mul α] → Mul (Finset α)
参数：Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul₀_sup' [PosMulReflectLT G₀] (ha : 0 ≤ a) (f : ι → G₀) (s : Finset ι) (hs) :
    a * s.sup' hs f = s.sup' hs fun i ↦ a * f i := by
  by_cases! h : 0 = a
  · simp [← h]
  exact map_finset_sup' (OrderIso.mulLeft₀ _ (lt_of_le_of_ne ha h)) hs f
/-
**Finset.sup'_div** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sup'_div₀ [MulPosReflectLT G₀] (ha : 0 ≤ a) (f : ι → G₀) (s : Finset ι) (hs) :
    s.sup' hs f / a = s.sup' hs fun i ↦ f i / a := by
  by_cases! h : 0 = a
  · simp [← h]
  exact map_finset_sup' (OrderIso.divRight₀ _ (lt_of_le_of_ne ha h)) hs f

end GroupWithZero

/-
**Finset.sup_div** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sup_div₀ [LinearOrderedCommGroupWithZero G₀] {a : G₀} (ha : 0 ≤ a)
    (s : Finset ι) (f : ι → G₀) : s.sup f / a = s.sup fun i ↦ f i / a := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [bot_eq_zero]
  rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, sup'_div₀ (ha := ha)]

end Finset

