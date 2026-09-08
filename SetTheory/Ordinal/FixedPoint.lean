/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
module

public import Mathlib.Logic.Small.List
public import Mathlib.SetTheory.Ordinal.Enum
public import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
two forms: as statements about indexed families of normal functions, and as statements about a
single normal function.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

## Main definitions and results

* `nfpFamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `not_bddAbove_fp_family`, `not_bddAbove_fp`: the (common) fixed points of a (family of) normal
  function(s) are unbounded in the ordinals.
* `deriv_add_eq_mul_omega0_add`: a characterization of the derivative of addition.
* `deriv_mul_eq_opow_omega0_mul`: a characterization of the derivative of multiplication.
-/

@[expose] public section


noncomputable section

universe u v

open Function Order

namespace Ordinal

/-! ### Fixed points of type-indexed families of ordinals -/

section

variable {ι : Type*} {f : ι → Ordinal.{u} → Ordinal.{u}}

/-- The next common fixed point, at least `a`, for a family of normal functions.

This is defined for any family of functions, as the supremum of all values reachable by applying
finitely many functions in the family to `a`.

`Ordinal.nfpFamily_fp` shows this is a fixed point, `Ordinal.le_nfpFamily` shows it's at
least `a`, and `Ordinal.nfpFamily_le_fp` shows this is the least ordinal with these properties. -/
/-
**Ordinal.nfpFamily** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：nfpFamily (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a : Ordinal.{u}) : Ordina
l
参数：f : ι -> Ordinal.{u} -> Ordinal.{u}；a : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The next common fixed point, at least `a`, for a family of normal functions.

This is defined for any family of functions, as the supremum of all values reach
able by applying
finitely many functions in the family to `a`.

`Ordinal.nfpFamily_fp` shows this is a fixed point, `Ordinal.le_nfpFamily` shows
 it's at
least `a`, and `Ordinal.nfpFamily_le_fp` shows this is the least ordinal with th
ese properties.
-/
def nfpFamily (f : ι → Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) : Ordinal :=
  ⨆ i, List.foldr f a i
/-
**Ordinal.foldr_le_nfpFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：foldr_le_nfpFamily [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a 
l) : List.foldr f a l <= nfpFamily f a
参数：f : ι -> Ordinal.{u} -> Ordinal.{u}；a l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
-/
theorem foldr_le_nfpFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) (a l) :
    List.foldr f a l ≤ nfpFamily f a :=
  Ordinal.le_iSup _ _
/-
**Ordinal.le_nfpFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_nfpFamily [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) (a) : a <
= nfpFamily f a
参数：f : ι -> Ordinal.{u} -> Ordinal.{u}；a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.foldr_le_nfpFamily`：foldr_le_nfpFamily [Small.{u} ι] (f : ι -> O
rdinal.{u} -> Ordinal.{u}) (a l) : List.foldr f a l <= nfpFamily f a
-/
theorem le_nfpFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) (a) : a ≤ nfpFamily f a :=
  foldr_le_nfpFamily f a []
/-
**Ordinal.lt_nfpFamily_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_nfpFamily_iff [Small.{u} ι] {a b} : a < nfpFamily f b ↔ exists l, a < L
ist.foldr f b l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.lt_iSup_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], a < ⨆ i, f i ↔ ∃ i, a < f i
-/
theorem lt_nfpFamily_iff [Small.{u} ι] {a b} : a < nfpFamily f b ↔ ∃ l, a < List.foldr f b l :=
  Ordinal.lt_iSup_iff
/-
**Ordinal.nfpFamily_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfpFamily_le_iff [Small.{u} ι] {a b} : nfpFamily f a <= b ↔ forall l, List
.foldr f a l <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_le_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], ⨆ i, f i ≤ a ↔ ∀ (i : ι), f i ≤ a
-/
theorem nfpFamily_le_iff [Small.{u} ι] {a b} : nfpFamily f a ≤ b ↔ ∀ l, List.foldr f a l ≤ b :=
  Ordinal.iSup_le_iff
/-
**Ordinal.nfpFamily_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfpFamily_le {a b} : (forall l, List.foldr f a l <= b) -> nfpFamily f a <=
 b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
-/
theorem nfpFamily_le {a b} : (∀ l, List.foldr f a l ≤ b) → nfpFamily f a ≤ b :=
  Ordinal.iSup_le
/-
**Ordinal.nfpFamily_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfpFamily_monotone [Small.{u} ι] (hf : forall i, Monotone (f i)) : Monoton
e (nfpFamily f)
参数：hf : forall i, Monotone (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nfpFamily_le`：nfpFamily_le {a b} : (forall l, List.foldr f a l <
= b) -> nfpFamily f a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `List.foldr_monotone`：foldr_monotone [Preorder β] {f : α -> β -> β} (H : 
forall a, Monotone (f a)) (l : List α) : Monotone fun b => l.foldr f b
· 使用定理 `Ordinal.foldr_le_nfpFamily`：foldr_le_nfpFamily [Small.{u} ι] (f : ι -> O
rdinal.{u} -> Ordinal.{u}) (a l) : List.foldr f a l <= nfpFamily f a
-/
theorem nfpFamily_monotone [Small.{u} ι] (hf : ∀ i, Monotone (f i)) : Monotone (nfpFamily f) :=
  fun _ _ h ↦ nfpFamily_le <| fun l ↦ (List.foldr_monotone hf l h).trans (foldr_le_nfpFamily _ _ l)
/-
**Ordinal.apply_lt_nfpFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：apply_lt_nfpFamily [Small.{u} ι] (H : forall i, IsNormal (f i)) {a b} (hb 
: b < nfpFamily f a) (i) : f i b < nfpFamily f a
参数：H : forall i, IsNormal (f i)；hb : b < nfpFamily f a；i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_nfpFamily_iff`：lt_nfpFamily_iff [Small.{u} ι] {a b} : a < nfp
Family f b ↔ exists l, a < List.foldr f b l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
-/
theorem apply_lt_nfpFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b}
    (hb : b < nfpFamily f a) (i) : f i b < nfpFamily f a :=
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 hb
  lt_nfpFamily_iff.2 ⟨i::l, (H i).strictMono hl⟩
/-
**Ordinal.apply_lt_nfpFamily_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：apply_lt_nfpFamily_iff [Nonempty ι] [Small.{u} ι] (H : forall i, IsNormal 
(f i)) {a b} : (forall i, f i b < nfpFamily f a) ↔ b < nfpFamily f a
参数：H : forall i, IsNormal (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.lt_nfpFamily_iff`：lt_nfpFamily_iff [Small.{u} ι] {a b} : a < nfp
Family f b ↔ exists l, a < List.foldr f b l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.apply_lt_nfpFamily`：apply_lt_nfpFamily [Small.{u} ι] (H : forall
 i, IsNormal (f i)) {a b} (hb : b < nfpFamily f a) (i) : f i b < nfpFamily f a
-/
theorem apply_lt_nfpFamily_iff [Nonempty ι] [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b < nfpFamily f a) ↔ b < nfpFamily f a := by
  refine ⟨fun h ↦ ?_, apply_lt_nfpFamily H⟩
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 (h (Classical.arbitrary ι))
  exact lt_nfpFamily_iff.2 <| ⟨l, (H _).strictMono.le_apply.trans_lt hl⟩
/-
**Ordinal.nfpFamily_le_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfpFamily_le_apply [Nonempty ι] [Small.{u} ι] (H : forall i, IsNormal (f i
)) {a b} : (exists i, nfpFamily f a <= f i b) ↔ nfpFamily f a <= b
参数：H : forall i, IsNormal (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ordinal.apply_lt_nfpFamily_iff`：apply_lt_nfpFamily_iff [Nonempty ι] [Sma
ll.{u} ι] (H : forall i, IsNormal (f i)) {a b} : (forall i, f i b < nfpFamily f 
a) ↔ b < nfpFamily f…
-/
theorem nfpFamily_le_apply [Nonempty ι] [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∃ i, nfpFamily f a ≤ f i b) ↔ nfpFamily f a ≤ b := by
  contrapose!; exact apply_lt_nfpFamily_iff H
/-
**Ordinal.nfpFamily_le_fp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfpFamily_le_fp (H : forall i, Monotone (f i)) {a b} (ab : a <= b) (h : fo
rall i, f i b <= b) : nfpFamily f a <= b
参数：H : forall i, Monotone (f i)；ab : a <= b；h : forall i, f i b <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem nfpFamily_le_fp (H : ∀ i, Monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
    nfpFamily f a ≤ b := by
  apply Ordinal.iSup_le fun l ↦ ?_
  induction l generalizing a with
  | nil => exact ab
  | cons i l IH => exact (H i (IH ab)).trans (h i)
/-
**Ordinal.nfpFamily_fp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (a) : f i (nfpFamily f
 a) = nfpFamily f a
参数：H : IsNormal (f i)；a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.nfpFamily.eq_1`：∀ {ι : Type u_1} (f : ι → Ordinal.{u} → Ordinal.
{u}) (a : Ordinal.{u}), Ordinal.nfpFamily f a = ⨆ i, List.foldr f a i
· 使用定理 `Order.IsNormal.map_iSup`：map_iSup {ι} [Nonempty ι] {g : ι -> α} (hf : Is
Normal f) (hg : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
-/
theorem nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (a) :
    f i (nfpFamily f a) = nfpFamily f a := by
  rw [nfpFamily, H.map_iSup bddAbove_of_small]
  apply le_antisymm <;> refine Ordinal.iSup_le fun l => ?_
  · exact Ordinal.le_iSup _ (i::l)
  · exact H.strictMono.le_apply.trans (Ordinal.le_iSup _ _)
/-
**Ordinal.apply_le_nfpFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：apply_le_nfpFamily [Small.{u} ι] [hι : Nonempty ι] (H : forall i, IsNormal
 (f i)) {a b} : (forall i, f i b <= nfpFamily f a) ↔ b <= nfpFamily f a
参数：H : forall i, IsNormal (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.nfpFamily_fp`：nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)
) (a) : f i (nfpFamily f a) = nfpFamily f a
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f
-/
theorem apply_le_nfpFamily [Small.{u} ι] [hι : Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b ≤ nfpFamily f a) ↔ b ≤ nfpFamily f a := by
  refine ⟨fun h => ?_, fun h i => ?_⟩
  · obtain ⟨i⟩ := hι
    exact (H i).strictMono.le_apply.trans (h i)
  · rw [← nfpFamily_fp (H i)]
    exact (H i).monotone h
/-
**Ordinal.nfpFamily_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfpFamily_eq_self [Small.{u} ι] {a} (h : forall i, f i a = a) : nfpFamily 
f a = a
参数：h : forall i, f i a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldr_fixed'`：∀ {α : Type u} {β : Type v} {f : α → β → β} {b : β}, 
(∀ (a : α), f a b = b) → ∀ (l : List α), List.foldr f b l = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ordinal.le_nfpFamily`：le_nfpFamily [Small.{u} ι] (f : ι -> Ordinal.{u} -
> Ordinal.{u}) (a) : a <= nfpFamily f a
-/
theorem nfpFamily_eq_self [Small.{u} ι] {a} (h : ∀ i, f i a = a) : nfpFamily f a = a := by
  apply (Ordinal.iSup_le ?_).antisymm (le_nfpFamily f a)
  intro l
  rw [List.foldr_fixed' h l]

-- Todo: This is actually a special case of the fact the intersection of club sets is a club set.
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
/-
**Ordinal.not_bddAbove_fp_family** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：not_bddAbove_fp_family [Small.{u} ι] (H : forall i, IsNormal (f i)) : ¬ Bd
dAbove (⋂ i, Function.fixedPoints (f i))
参数：H : forall i, IsNormal (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_bddAbove_iff`：not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set 
α} : ¬BddAbove s ↔ forall x, exists y in s, x < y
· 使用定理 `Ordinal.nfpFamily_fp`：nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)
) (a) : f i (nfpFamily f a) = nfpFamily f a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.le_nfpFamily`：le_nfpFamily [Small.{u} ι] (f : ι -> Ordinal.{u} -
> Ordinal.{u}) (a) : a <= nfpFamily f a

--- 原说明 ---
A generalization of the fixed point lemma for normal functions: any family of no
rmal functions
    has an unbounded set of common fixed points.
-/
theorem not_bddAbove_fp_family [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    ¬ BddAbove (⋂ i, Function.fixedPoints (f i)) := by
  rw [not_bddAbove_iff]
  refine fun a ↦ ⟨nfpFamily f (succ a), ?_, (lt_succ a).trans_le (le_nfpFamily f _)⟩
  rintro _ ⟨i, rfl⟩
  exact nfpFamily_fp (H i) _

/-- The derivative of a family of normal functions is the sequence of their common fixed points.

This is defined for all functions such that `Ordinal.derivFamily_zero`,
`Ordinal.derivFamily_succ`, and `Ordinal.derivFamily_limit` are satisfied. -/
/-
**Ordinal.derivFamily** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：derivFamily (f : ι -> Ordinal.{u} -> Ordinal.{u}) (o : Ordinal.{u}) : Ordi
nal.{u}
参数：f : ι -> Ordinal.{u} -> Ordinal.{u}；o : Ordinal.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of a family of normal functions is the sequence of their common f
ixed points.

This is defined for all functions such that `Ordinal.derivFamily_zero`,
`Ordinal.derivFamily_succ`, and `Ordinal.derivFamily_limit` are satisfied.
-/
def derivFamily (f : ι → Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  limitRecOn o (nfpFamily f 0) (fun _ IH => nfpFamily f (succ IH))
    fun a _ g => ⨆ b : Set.Iio a, g _ b.2

@[simp]
/-
**Ordinal.derivFamily_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：derivFamily_zero (f : ι -> Ordinal -> Ordinal) : derivFamily f 0 = nfpFami
ly f 0
参数：f : ι -> Ordinal -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.limitRecOn_zero`：limitRecOn_zero {motive} (H₁ H₂ H₃) : @limitRec
On motive 0 H₁ H₂ H₃ = H₁
-/
theorem derivFamily_zero (f : ι → Ordinal → Ordinal) :
    derivFamily f 0 = nfpFamily f 0 :=
  limitRecOn_zero ..

@[simp]
/-
**Ordinal.derivFamily_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：derivFamily_add_one (f : ι -> Ordinal -> Ordinal) (o) : derivFamily f (o +
 1) = nfpFamily f (derivFamily f o + 1)
参数：f : ι -> Ordinal -> Ordinal；o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.limitRecOn_add_one`：limitRecOn_add_one {motive} (o H₁ H₂ H₃) : @
limitRecOn motive (o + 1) H₁ H₂ H₃ = H₂ o (@limitRecOn motive o H₁ H₂ H₃)
-/
theorem derivFamily_add_one (f : ι → Ordinal → Ordinal) (o) :
    derivFamily f (o + 1) = nfpFamily f (derivFamily f o + 1) :=
  limitRecOn_add_one ..

-- TODO: deprecate
/-
**Ordinal.derivFamily_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：derivFamily_succ (f : ι -> Ordinal -> Ordinal) (o) : derivFamily f (succ o
) = nfpFamily f (succ (derivFamily f o))
参数：f : ι -> Ordinal -> Ordinal；o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.derivFamily_add_one`：derivFamily_add_one (f : ι -> Ordinal -> Or
dinal) (o) : derivFamily f (o + 1) = nfpFamily f (derivFamily f o + 1)
-/
theorem derivFamily_succ (f : ι → Ordinal → Ordinal) (o) :
    derivFamily f (succ o) = nfpFamily f (succ (derivFamily f o)) :=
  derivFamily_add_one f o
/-
**Ordinal.derivFamily_limit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：derivFamily_limit (f : ι -> Ordinal -> Ordinal) {o} : IsSuccLimit o -> der
ivFamily f o = ⨆ b : Set.Iio o, derivFamily f b
参数：f : ι -> Ordinal -> Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.limitRecOn_limit`：limitRecOn_limit {motive} (o H₁ H₂ H₃ h) : @li
mitRecOn motive o H₁ H₂ H₃ = H₃ o h fun x _h => @limitRecOn motive x H₁ H₂ H₃
-/
theorem derivFamily_limit (f : ι → Ordinal → Ordinal) {o} :
    IsSuccLimit o → derivFamily f o = ⨆ b : Set.Iio o, derivFamily f b :=
  limitRecOn_limit _ _ _ _
/-
**Ordinal.isNormal_derivFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_derivFamily [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u}) :
 IsNormal (derivFamily f)
参数：f : ι -> Ordinal.{u} -> Ordinal.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.of_succ_lt`：of_succ_lt (hs : forall a, f a < f (succ a)) 
(hl : forall {a}, IsSuccLimit a -> IsLUB (f '' Iio a) (f a)) : IsNormal f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.derivFamily_succ`：derivFamily_succ (f : ι -> Ordinal -> Ordinal)
 (o) : derivFamily f (succ o) = nfpFamily f (succ (derivFamily f o))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Ordinal.le_nfpFamily`：le_nfpFamily [Small.{u} ι] (f : ι -> Ordinal.{u} -
> Ordinal.{u}) (a) : a <= nfpFamily f a
· 使用定理 `Ordinal.derivFamily_limit`：derivFamily_limit (f : ι -> Ordinal -> Ordina
l) {o} : IsSuccLimit o -> derivFamily f o = ⨆ b : Set.Iio o, derivFamily f b
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Order.IsSuccLimit.nonempty_Iio`：∀ {α : Type u_1} {a : α} [inst : Preorde
r α], Order.IsSuccLimit a → (Set.Iio a).Nonempty
· 使用定理 `isLUB_ciSup`：isLUB_ciSup [Nonempty ι] {f : ι -> α} (H : BddAbove (range 
f)) : IsLUB (range f) (⨆ i, f i)
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
-/
theorem isNormal_derivFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) :
    IsNormal (derivFamily f) := by
  refine IsNormal.of_succ_lt (fun o ↦ ?_) @fun o h ↦ ?_
  · rw [derivFamily_succ, ← succ_le_iff]
    exact le_nfpFamily _ _
  · rw [derivFamily_limit _ h, Set.image_eq_range]
    have := h.nonempty_Iio.to_subtype
    exact isLUB_ciSup bddAbove_of_small
/-
**Ordinal.derivFamily_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：derivFamily_strictMono [Small.{u} ι] (f : ι -> Ordinal.{u} -> Ordinal.{u})
 : StrictMono (derivFamily f)
参数：f : ι -> Ordinal.{u} -> Ordinal.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_derivFamily`：isNormal_derivFamily [Small.{u} ι] (f : ι 
-> Ordinal.{u} -> Ordinal.{u}) : IsNormal (derivFamily f)
-/
theorem derivFamily_strictMono [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) :
    StrictMono (derivFamily f) :=
  (isNormal_derivFamily f).strictMono
/-
**Ordinal.derivFamily_fp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：derivFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (o : Ordinal) : f i 
(derivFamily f o) = derivFamily f o
参数：H : IsNormal (f i)；o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.derivFamily_zero`：derivFamily_zero (f : ι -> Ordinal -> Ordinal)
 : derivFamily f 0 = nfpFamily f 0
· 使用定理 `Ordinal.nfpFamily_fp`：nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)
) (a) : f i (nfpFamily f a) = nfpFamily f a
· 使用定理 `Ordinal.derivFamily_add_one`：derivFamily_add_one (f : ι -> Ordinal -> Or
dinal) (o) : derivFamily f (o + 1) = nfpFamily f (derivFamily f o + 1)
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Order.IsSuccLimit.nonempty_Iio`：∀ {α : Type u_1} {a : α} [inst : Preorde
r α], Order.IsSuccLimit a → (Set.Iio a).Nonempty
· 使用定理 `Ordinal.derivFamily_limit`：derivFamily_limit (f : ι -> Ordinal -> Ordina
l) {o} : IsSuccLimit o -> derivFamily f o = ⨆ b : Set.Iio o, derivFamily f b
· 使用定理 `Order.IsNormal.map_iSup`：map_iSup {ι} [Nonempty ι] {g : ι -> α} (hf : Is
Normal f) (hg : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Ordinal.iSup_le_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], ⨆ i, f i ≤ a ↔ ∀ (i : ι), f i ≤ a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem derivFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (o : Ordinal) :
    f i (derivFamily f o) = derivFamily f o := by
  induction o using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_fp H 0
  | add_one =>
    rw [derivFamily_add_one]
    exact nfpFamily_fp H _
  | limit o l IH =>
    have := l.nonempty_Iio.to_subtype
    rw [derivFamily_limit _ l, H.map_iSup bddAbove_of_small]
    refine eq_of_forall_ge_iff fun c => ?_
    rw [Ordinal.iSup_le_iff, Ordinal.iSup_le_iff]
    refine forall_congr' fun a ↦ ?_
    rw [IH _ a.2]
/-
**Ordinal.le_iff_derivFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_iff_derivFamily [Small.{u} ι] (H : forall i, IsNormal (f i)) {a} : (for
all i, f i a <= a) ↔ exists o, derivFamily f o = a
参数：H : forall i, IsNormal (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.derivFamily_zero`：derivFamily_zero (f : ι -> Ordinal -> Ordinal)
 : derivFamily f 0 = nfpFamily f 0
· 使用定理 `Ordinal.nfpFamily_le_fp`：nfpFamily_le_fp (H : forall i, Monotone (f i)) 
{a b} (ab : a <= b) (h : forall i, f i b <= b) : nfpFamily f a <= b
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Ordinal.derivFamily_add_one`：derivFamily_add_one (f : ι -> Ordinal -> Or
dinal) (o) : derivFamily f (o + 1) = nfpFamily f (derivFamily f o + 1)
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Ordinal.iSup_le_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], ⨆ i, f i ≤ a ↔ ∀ (i : ι), f i ≤ a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Ordinal.derivFamily_limit`：derivFamily_limit (f : ι -> Ordinal -> Ordina
l) {o} : IsSuccLimit o -> derivFamily f o = ⨆ b : Set.Iio o, derivFamily f b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_derivFamily`：isNormal_derivFamily [Small.{u} ι] (f : ι 
-> Ordinal.{u} -> Ordinal.{u}) : IsNormal (derivFamily f)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ordinal.derivFamily_fp`：derivFamily_fp [Small.{u} ι] {i} (H : IsNormal (
f i)) (o : Ordinal) : f i (derivFamily f o) = derivFamily f o
-/
theorem le_iff_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a ≤ a) ↔ ∃ o, derivFamily f o = a :=
  ⟨fun ha => by
    suffices ∀ (o), a ≤ derivFamily f o → ∃ o, derivFamily f o = a from
      this a (isNormal_derivFamily _).strictMono.le_apply
    intro o
    induction o using limitRecOn with
    | zero =>
      intro h₁
      refine ⟨0, le_antisymm ?_ h₁⟩
      rw [derivFamily_zero]
      exact nfpFamily_le_fp (fun i => (H i).monotone) zero_le ha
    | add_one o IH =>
      intro h₁
      rcases le_or_gt a (derivFamily f o) with h | h
      · exact IH h
      refine ⟨o + 1, le_antisymm ?_ h₁⟩
      rw [derivFamily_add_one]
      exact nfpFamily_le_fp (fun i => (H i).monotone) (succ_le_of_lt h) ha
    | limit o l IH =>
      intro h₁
      rcases eq_or_lt_of_le h₁ with h | h
      · exact ⟨_, h.symm⟩
      rw [derivFamily_limit _ l, ← not_le, Ordinal.iSup_le_iff, not_forall] at h
      obtain ⟨o', h⟩ := h
      exact IH o' o'.2 (le_of_not_ge h),
    fun ⟨_, e⟩ i => e ▸ (derivFamily_fp (H i) _).le⟩
/-
**Ordinal.fp_iff_derivFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：fp_iff_derivFamily [Small.{u} ι] (H : forall i, IsNormal (f i)) {a} : (for
all i, f i a = a) ↔ exists o, derivFamily f o = a
参数：H : forall i, IsNormal (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.le_iff_derivFamily`：le_iff_derivFamily [Small.{u} ι] (H : forall
 i, IsNormal (f i)) {a} : (forall i, f i a <= a) ↔ exists o, derivFamily f o = a
-/
theorem fp_iff_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a = a) ↔ ∃ o, derivFamily f o = a :=
  Iff.trans ⟨fun h i => le_of_eq (h i), fun h i => (H i).strictMono.le_apply.ge_iff_eq'.1 (h i)⟩
    (le_iff_derivFamily H)
/-
**Ordinal.mem_range_derivFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_range_derivFamily [Small.{u} ι] (H : forall i, IsNormal (f i)) {a} : a
 in Set.range (derivFamily f) ↔ forall i, f i a = a
参数：H : forall i, IsNormal (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ordinal.fp_iff_derivFamily`：fp_iff_derivFamily [Small.{u} ι] (H : forall
 i, IsNormal (f i)) {a} : (forall i, f i a = a) ↔ exists o, derivFamily f o = a
-/
theorem mem_range_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a} :
    a ∈ Set.range (derivFamily f) ↔ ∀ i, f i a = a :=
  (fp_iff_derivFamily H).symm

/-- For a family of normal functions, `Ordinal.derivFamily` enumerates the common fixed points. -/
/-
**Ordinal.derivFamily_eq_enumOrd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：derivFamily_eq_enumOrd [Small.{u} ι] (H : forall i, IsNormal (f i)) : deri
vFamily f = enumOrd (⋂ i, Function.fixedPoints (f i))
参数：H : forall i, IsNormal (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Ordinal.eq_enumOrd`：eq_enumOrd (f : Ordinal -> Ordinal) (hs : ¬ BddAbove
 s) : enumOrd s = f ↔ StrictMono f ∧ range f = s
· 使用定理 `Ordinal.not_bddAbove_fp_family`：not_bddAbove_fp_family [Small.{u} ι] (H 
: forall i, IsNormal (f i)) : ¬ BddAbove (⋂ i, Function.fixedPoints (f i))
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_derivFamily`：isNormal_derivFamily [Small.{u} ι] (f : ι 
-> Ordinal.{u} -> Ordinal.{u}) : IsNormal (derivFamily f)
· 使用定理 `Set.range_eq_iff`：range_eq_iff (f : α -> β) (s : Set β) : range f = s ↔ 
(forall a, f a in s) ∧ forall b in s, exists a, f a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.derivFamily_fp`：derivFamily_fp [Small.{u} ι] {i} (H : IsNormal (
f i)) (o : Ordinal) : f i (derivFamily f o) = derivFamily f o
· 使用定理 `Ordinal.fp_iff_derivFamily`：fp_iff_derivFamily [Small.{u} ι] (H : forall
 i, IsNormal (f i)) {a} : (forall i, f i a = a) ↔ exists o, derivFamily f o = a
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i

--- 原说明 ---
For a family of normal functions, `Ordinal.derivFamily` enumerates the common fi
xed points.
-/
theorem derivFamily_eq_enumOrd [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    derivFamily f = enumOrd (⋂ i, Function.fixedPoints (f i)) := by
  rw [eq_comm, eq_enumOrd _ (not_bddAbove_fp_family H)]
  use (isNormal_derivFamily f).strictMono
  rw [Set.range_eq_iff]
  refine ⟨?_, fun a ha => ?_⟩
  · rintro a S ⟨i, hi⟩
    rw [← hi]
    exact derivFamily_fp (H i) a
  rw [Set.mem_iInter] at ha
  rwa [← fp_iff_derivFamily H]

end

/-! ### Fixed points of a single function -/

section

variable {f : Ordinal.{u} → Ordinal.{u}}

/-- The next fixed point function, the least fixed point of the normal function `f`, at least `a`.

This is defined as `nfpFamily` applied to a family consisting only of `f`. -/
/-
**Ordinal.nfp** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：nfp (f : Ordinal -> Ordinal) : Ordinal -> Ordinal
参数：f : Ordinal -> Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The next fixed point function, the least fixed point of the normal function `f`,
 at least `a`.

This is defined as `nfpFamily` applied to a family consisting only of `f`.
-/
def nfp (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  nfpFamily fun _ : Unit => f
/-
**Ordinal.nfp_eq_nfpFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_eq_nfpFamily (f : Ordinal -> Ordinal) : nfp f = nfpFamily fun _ : Unit
 => f
参数：f : Ordinal -> Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nfp_eq_nfpFamily (f : Ordinal → Ordinal) : nfp f = nfpFamily fun _ : Unit => f :=
  rfl
/-
**Ordinal.iSup_iterate_eq_nfp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iSup_iterate_eq_nfp (f : Ordinal.{u} -> Ordinal.{u}) (a : Ordinal.{u}) : ⨆
 n : Nat, f^[n] a = nfp f a
参数：f : Ordinal.{u} -> Ordinal.{u}；a : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.iSup_le_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], ⨆ i, f i ≤ a ↔ ∀ (i : ι), f i ≤ a
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
· 使用定理 `List.foldr_const`：∀ {α : Type u} {β : Type v} (f : β → β) (b : β) (l : L
ist α), List.foldr (fun x => f) b l = f^[l.length] b
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
-/
theorem iSup_iterate_eq_nfp (f : Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) :
    ⨆ n : ℕ, f^[n] a = nfp f a := by
  apply le_antisymm
  · rw [Ordinal.iSup_le_iff]
    intro n
    rw [← List.length_replicate (n := n) (a := Unit.unit), ← List.foldr_const f a]
    exact Ordinal.le_iSup _ _
  · apply Ordinal.iSup_le
    intro l
    rw [List.foldr_const f a l]
    exact Ordinal.le_iSup _ _
/-
**Ordinal.iterate_le_nfp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iterate_le_nfp (f a n) : f^[n] a <= nfp f a
参数：f a n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_iterate_eq_nfp`：iSup_iterate_eq_nfp (f : Ordinal.{u} -> Ord
inal.{u}) (a : Ordinal.{u}) : ⨆ n : Nat, f^[n] a = nfp f a
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a := by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.le_iSup (fun n ↦ f^[n] a) n
/-
**Ordinal.le_nfp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_nfp (f a) : a <= nfp f a
参数：f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.iterate_le_nfp`：iterate_le_nfp (f a n) : f^[n] a <= nfp f a
-/
theorem le_nfp (f a) : a ≤ nfp f a :=
  iterate_le_nfp f a 0
/-
**Ordinal.lt_nfp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：lt_nfp_iff {a b} : a < nfp f b ↔ exists n, a < f^[n] b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_iterate_eq_nfp`：iSup_iterate_eq_nfp (f : Ordinal.{u} -> Ord
inal.{u}) (a : Ordinal.{u}) : ⨆ n : Nat, f^[n] a = nfp f a
· 使用定理 `Ordinal.lt_iSup_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], a < ⨆ i, f i ↔ ∃ i, a < f i
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem lt_nfp_iff {a b} : a < nfp f b ↔ ∃ n, a < f^[n] b := by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.lt_iSup_iff
/-
**Ordinal.nfp_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_le_iff {a b} : nfp f a <= b ↔ forall n, f^[n] a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_iterate_eq_nfp`：iSup_iterate_eq_nfp (f : Ordinal.{u} -> Ord
inal.{u}) (a : Ordinal.{u}) : ⨆ n : Nat, f^[n] a = nfp f a
· 使用定理 `Ordinal.iSup_le_iff`：∀ {ι : Type u_3} {f : ι → Ordinal.{u}} {a : Ordinal
.{u}} [Small.{u, u_3} ι], ⨆ i, f i ≤ a ↔ ∀ (i : ι), f i ≤ a
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem nfp_le_iff {a b} : nfp f a ≤ b ↔ ∀ n, f^[n] a ≤ b := by
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.iSup_le_iff
/-
**Ordinal.nfp_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_le {a b} : (forall n, f^[n] a <= b) -> nfp f a <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.nfp_le_iff`：nfp_le_iff {a b} : nfp f a <= b ↔ forall n, f^[n] a 
<= b
-/
theorem nfp_le {a b} : (∀ n, f^[n] a ≤ b) → nfp f a ≤ b :=
  nfp_le_iff.2

@[simp]
/-
**Ordinal.nfp_id** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_id : nfp id = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_id`：iterate_id (n : Nat) : (id : α -> α)^[n] = id
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem nfp_id : nfp id = id := by
  ext
  simp_rw [← iSup_iterate_eq_nfp, iterate_id]
  exact ciSup_const
/-
**Ordinal.nfp_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_monotone (hf : Monotone f) : Monotone (nfp f)
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nfpFamily_monotone`：nfpFamily_monotone [Small.{u} ι] (hf : foral
l i, Monotone (f i)) : Monotone (nfpFamily f)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem nfp_monotone (hf : Monotone f) : Monotone (nfp f) :=
  nfpFamily_monotone fun _ => hf
/-
**Ordinal.iterate_lt_nfp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：iterate_lt_nfp (hf : StrictMono f) {a} (h : a < f a) (n : Nat) : f^[n] a <
 nfp f a
参数：hf : StrictMono f；h : a < f a；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `StrictMono.iterate`：∀ {α : Type u} [inst : Preorder α] {f : α → α}, Stri
ctMono f → ∀ (n : ℕ), StrictMono f^[n]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)
· 使用定理 `Ordinal.iterate_le_nfp`：iterate_le_nfp (f a n) : f^[n] a <= nfp f a
-/
theorem iterate_lt_nfp (hf : StrictMono f) {a} (h : a < f a) (n : ℕ) : f^[n] a < nfp f a := by
  apply (hf.iterate n h).trans_le
  rw [← iterate_succ_apply]
  exact iterate_le_nfp ..
/-
**Ordinal.apply_lt_nfp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：apply_lt_nfp (H : IsNormal f) {a b} : f b < nfp f a ↔ b < nfp f a
参数：H : IsNormal f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.apply_lt_nfpFamily_iff`：apply_lt_nfpFamily_iff [Nonempty ι] [Sma
ll.{u} ι] (H : forall i, IsNormal (f i)) {a b} : (forall i, f i b < nfpFamily f 
a) ↔ b < nfpFamily f…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem apply_lt_nfp (H : IsNormal f) {a b} : f b < nfp f a ↔ b < nfp f a := by
  unfold nfp
  rw [← @apply_lt_nfpFamily_iff Unit (fun _ => f) _ _ (fun _ => H) a b]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩
/-
**Ordinal.nfp_le_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_le_apply (H : IsNormal f) {a b} : nfp f a <= f b ↔ nfp f a <= b
参数：H : IsNormal f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Ordinal.apply_lt_nfp`：apply_lt_nfp (H : IsNormal f) {a b} : f b < nfp f 
a ↔ b < nfp f a
-/
theorem nfp_le_apply (H : IsNormal f) {a b} : nfp f a ≤ f b ↔ nfp f a ≤ b :=
  le_iff_le_iff_lt_iff_lt.2 (apply_lt_nfp H)
/-
**Ordinal.nfp_le_fp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_le_fp (H : Monotone f) {a b} (ab : a <= b) (h : f b <= b) : nfp f a <=
 b
参数：H : Monotone f；ab : a <= b；h : f b <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nfpFamily_le_fp`：nfpFamily_le_fp (H : forall i, Monotone (f i)) 
{a b} (ab : a <= b) (h : forall i, f i b <= b) : nfpFamily f a <= b
-/
theorem nfp_le_fp (H : Monotone f) {a b} (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
  nfpFamily_le_fp (fun _ => H) ab fun _ => h
/-
**Ordinal.nfp_fp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_fp (H : IsNormal f) : forall a, f (nfp f a) = nfp f a
参数：H : IsNormal f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nfpFamily_fp`：nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)
) (a) : f i (nfpFamily f a) = nfpFamily f a
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem nfp_fp (H : IsNormal f) : ∀ a, f (nfp f a) = nfp f a :=
  @nfpFamily_fp Unit (fun _ => f) _ () H
/-
**Ordinal.apply_le_nfp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：apply_le_nfp (H : IsNormal f) {a b} : f b <= nfp f a ↔ b <= nfp f a
参数：H : IsNormal f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.nfp_fp`：nfp_fp (H : IsNormal f) : forall a, f (nfp f a) = nfp f 
a
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f
-/
theorem apply_le_nfp (H : IsNormal f) {a b} : f b ≤ nfp f a ↔ b ≤ nfp f a :=
  ⟨H.strictMono.le_apply.trans, fun h => by simpa only [nfp_fp H] using H.monotone h⟩
/-
**Ordinal.nfp_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_eq_self {a} (h : f a = a) : nfp f a = a
参数：h : f a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.nfpFamily_eq_self`：nfpFamily_eq_self [Small.{u} ι] {a} (h : fora
ll i, f i a = a) : nfpFamily f a = a
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem nfp_eq_self {a} (h : f a = a) : nfp f a = a :=
  nfpFamily_eq_self fun _ => h

/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
/-
**Ordinal.not_bddAbove_fp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：not_bddAbove_fp (H : IsNormal f) : ¬ BddAbove (Function.fixedPoints f)
参数：H : IsNormal f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.iInter_const`：iInter_const (s : Set β) : ⋂ _ : ι, s = s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ordinal.not_bddAbove_fp_family`：not_bddAbove_fp_family [Small.{u} ι] (H 
: forall i, IsNormal (f i)) : ¬ BddAbove (⋂ i, Function.fixedPoints (f i))
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
The fixed point lemma for normal functions: any normal function has an unbounded
 set of
fixed points.
-/
theorem not_bddAbove_fp (H : IsNormal f) : ¬ BddAbove (Function.fixedPoints f) := by
  convert! not_bddAbove_fp_family fun _ : Unit => H
  exact (Set.iInter_const _).symm

/-- The derivative of a normal function `f` is the sequence of fixed points of `f`.

This is defined as `Ordinal.derivFamily` applied to a trivial family consisting only of `f`. -/
/-
**Ordinal.deriv** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：deriv (f : Ordinal -> Ordinal) : Ordinal -> Ordinal
参数：f : Ordinal -> Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of a normal function `f` is the sequence of fixed points of `f`.

This is defined as `Ordinal.derivFamily` applied to a trivial family consisting 
only of `f`.
-/
def deriv (f : Ordinal → Ordinal) : Ordinal → Ordinal :=
  derivFamily fun _ : Unit => f
/-
**Ordinal.deriv_eq_derivFamily** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_eq_derivFamily (f : Ordinal -> Ordinal) : deriv f = derivFamily fun 
_ : Unit => f
参数：f : Ordinal -> Ordinal。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem deriv_eq_derivFamily (f : Ordinal → Ordinal) : deriv f = derivFamily fun _ : Unit => f :=
  rfl

-- TODO: rename to `deriv_zero` once the name is available
@[simp]
/-
**Ordinal.deriv_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_zero_right (f) : deriv f 0 = nfp f 0
参数：f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.derivFamily_zero`：derivFamily_zero (f : ι -> Ordinal -> Ordinal)
 : derivFamily f 0 = nfpFamily f 0
-/
theorem deriv_zero_right (f) : deriv f 0 = nfp f 0 :=
  derivFamily_zero _

@[simp]
/-
**Ordinal.deriv_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_add_one (f o) : deriv f (o + 1) = nfp f (deriv f o + 1)
参数：f o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.derivFamily_succ`：derivFamily_succ (f : ι -> Ordinal -> Ordinal)
 (o) : derivFamily f (succ o) = nfpFamily f (succ (derivFamily f o))
-/
theorem deriv_add_one (f o) : deriv f (o + 1) = nfp f (deriv f o + 1) :=
  derivFamily_succ _ _

-- TODO: deprecate
/-
**Ordinal.deriv_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o))
参数：f o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.deriv_add_one`：deriv_add_one (f o) : deriv f (o + 1) = nfp f (de
riv f o + 1)
-/
theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
  deriv_add_one ..
/-
**Ordinal.deriv_limit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_limit (f) {o} : IsSuccLimit o -> deriv f o = ⨆ a : {a // a < o}, der
iv f a
参数：f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.derivFamily_limit`：derivFamily_limit (f : ι -> Ordinal -> Ordina
l) {o} : IsSuccLimit o -> derivFamily f o = ⨆ b : Set.Iio o, derivFamily f b
-/
theorem deriv_limit (f) {o} : IsSuccLimit o → deriv f o = ⨆ a : {a // a < o}, deriv f a :=
  derivFamily_limit _
/-
**Ordinal.isNormal_deriv** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isNormal_deriv (f) : IsNormal (deriv f)
参数：f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.isNormal_derivFamily`：isNormal_derivFamily [Small.{u} ι] (f : ι 
-> Ordinal.{u} -> Ordinal.{u}) : IsNormal (derivFamily f)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem isNormal_deriv (f) : IsNormal (deriv f) :=
  isNormal_derivFamily _
/-
**Ordinal.deriv_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_strictMono (f) : StrictMono (deriv f)
参数：f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.derivFamily_strictMono`：derivFamily_strictMono [Small.{u} ι] (f 
: ι -> Ordinal.{u} -> Ordinal.{u}) : StrictMono (derivFamily f)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem deriv_strictMono (f) : StrictMono (deriv f) :=
  derivFamily_strictMono _

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]
/-
**Ordinal.deriv_eq_id_of_nfp_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_eq_id_of_nfp_eq_id (h : nfp f = id) : deriv f = id
参数：h : nfp f = id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.IsNormal.ext_iff`：ext_iff [OrderBot α] {g : α -> β} (hf : IsNormal
 f) (hg : IsNormal g) : f = g ↔ f ⊥ = g ⊥ ∧ forall a, f a = g a -> f (succ a) = 
g (succ a)
· 使用定理 `Ordinal.isNormal_deriv`：isNormal_deriv (f) : IsNormal (deriv f)
· 使用定理 `Order.IsNormal.id`：∀ {α : Type u_1} [inst : LinearOrder α], Order.IsNorm
al id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `Ordinal.deriv_zero_right`：deriv_zero_right (f) : deriv f 0 = nfp f 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.deriv_add_one`：deriv_add_one (f o) : deriv f (o + 1) = nfp f (de
riv f o + 1)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem deriv_eq_id_of_nfp_eq_id (h : nfp f = id) : deriv f = id :=
  ((isNormal_deriv _).ext_iff .id).2 (by simp [h])
/-
**Ordinal.deriv_fp** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_fp (H : IsNormal f) : forall o, f (deriv f o) = deriv f o
参数：H : IsNormal f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.derivFamily_fp`：derivFamily_fp [Small.{u} ι] {i} (H : IsNormal (
f i)) (o : Ordinal) : f i (derivFamily f o) = derivFamily f o
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem deriv_fp (H : IsNormal f) : ∀ o, f (deriv f o) = deriv f o :=
  derivFamily_fp (i := ⟨⟩) H
/-
**Ordinal.le_iff_deriv** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：le_iff_deriv (H : IsNormal f) {a} : f a <= a ↔ exists o, deriv f o = a
参数：H : IsNormal f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.le_iff_derivFamily`：le_iff_derivFamily [Small.{u} ι] (H : forall
 i, IsNormal (f i)) {a} : (forall i, f i a <= a) ↔ exists o, derivFamily f o = a
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem le_iff_deriv (H : IsNormal f) {a} : f a ≤ a ↔ ∃ o, deriv f o = a := by
  unfold deriv
  rw [← le_iff_derivFamily fun _ : Unit => H]
  exact ⟨fun h _ => h, fun h => h Unit.unit⟩
/-
**Ordinal.mem_range_deriv** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_range_deriv (H : IsNormal f) {a} : a in Set.range (deriv f) ↔ f a = a
参数：H : IsNormal f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.le_iff_deriv`：le_iff_deriv (H : IsNormal f) {a} : f a <= a ↔ exi
sts o, deriv f o = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range_deriv (H : IsNormal f) {a} : a ∈ Set.range (deriv f) ↔ f a = a := by
  rw [Set.mem_range, ← H.strictMono.le_apply.ge_iff_eq', le_iff_deriv H]

/-- `Ordinal.deriv` enumerates the fixed points of a normal function. -/
/-
**Ordinal.deriv_eq_enumOrd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_eq_enumOrd (H : IsNormal f) : deriv f = enumOrd (Function.fixedPoint
s f)
参数：H : IsNormal f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.iInter_const`：iInter_const (s : Set β) : ⋂ _ : ι, s = s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ordinal.derivFamily_eq_enumOrd`：derivFamily_eq_enumOrd [Small.{u} ι] (H 
: forall i, IsNormal (f i)) : derivFamily f = enumOrd (⋂ i, Function.fixedPoints
 (f i))
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
`Ordinal.deriv` enumerates the fixed points of a normal function.
-/
theorem deriv_eq_enumOrd (H : IsNormal f) : deriv f = enumOrd (Function.fixedPoints f) := by
  convert! derivFamily_eq_enumOrd fun _ : Unit => H
  exact (Set.iInter_const _).symm

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]
/-
**Ordinal.nfp_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_zero_left (a) : nfp 0 a = a
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_iterate_eq_nfp`：iSup_iterate_eq_nfp (f : Ordinal.{u} -> Ord
inal.{u}) (a : Ordinal.{u}) : ⨆ n : Nat, f^[n] a = nfp f a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ordinal.iSup_le`：∀ {ι : Sort u_3} {f : ι → Ordinal.{u_4}} {a : Ordinal.{
u_4}}, (∀ (i : ι), f i ≤ a) → ⨆ i, f i ≤ a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.le_iSup`：∀ {ι : Type u_3} (f : ι → Ordinal.{u}) [Small.{u, u_3} 
ι] (i : ι), f i ≤ ⨆ i, f i
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem nfp_zero_left (a) : nfp 0 a = a := by
  rw [← iSup_iterate_eq_nfp]
  apply (Ordinal.iSup_le ?_).antisymm (Ordinal.le_iSup _ 0)
  intro n
  cases n
  · rfl
  · rw [Function.iterate_succ']
    simp

@[deprecated "do not depend on the junk values of `nfp`" (since := "2026-05-13")]
/-
**Ordinal.nfp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_zero : nfp 0 = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ordinal.nfp_zero_left`：nfp_zero_left (a) : nfp 0 a = a
-/
theorem nfp_zero : nfp 0 = id := by
  ext
  exact nfp_zero_left _

@[deprecated "do not depend on the junk values of `deriv`" (since := "2026-05-13")]
/-
**Ordinal.deriv_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_zero : deriv 0 = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.deriv_eq_id_of_nfp_eq_id`：deriv_eq_id_of_nfp_eq_id (h : nfp f = 
id) : deriv f = id
· 使用定理 `Ordinal.nfp_zero`：nfp_zero : nfp 0 = id
-/
theorem deriv_zero : deriv 0 = id :=
  deriv_eq_id_of_nfp_eq_id nfp_zero

@[deprecated "do not depend on the junk values of `deriv`" (since := "2026-05-13")]
/-
**Ordinal.deriv_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_zero_left (a) : deriv 0 a = a
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.deriv_zero`：deriv_zero : deriv 0 = id
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
-/
theorem deriv_zero_left (a) : deriv 0 a = a := by
  rw [deriv_zero, id_eq]

end

/-! ### Fixed points of addition -/

@[simp]
/-
**Ordinal.nfp_add_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_add_zero (a) : nfp (a + ·) 0 = a * ω
参数：a。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_left_iterate`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M) (n : ℕ),
 (fun x => a + x)^[n] = fun x => n • a + x
· 使用定理 `Ordinal.nsmul_eq_mul`：∀ (n : ℕ) (a : Ordinal.{u_4}), n • a = a * ↑n
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.iSup_mul_natCast`：iSup_mul_natCast (o : Ordinal) : ⨆ n : Nat, o 
* n = o * ω
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Fixed points of addition
-/
theorem nfp_add_zero (a) : nfp (a + ·) 0 = a * ω := by
  simp [← iSup_iterate_eq_nfp]
/-
**Ordinal.nfp_add_eq_mul_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_add_eq_mul_omega0 {a b} (hba : b <= a * ω) : nfp (a + ·) b = a * ω
参数：hba : b <= a * ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.nfp_le_fp`：nfp_le_fp (H : Monotone f) {a b} (ab : a <= b) (h : f
 b <= b) : nfp f a <= b
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one_add`：mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = 
a + a * b
· 使用定理 `Ordinal.one_add_omega0`：one_add_omega0 : 1 + ω = ω
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ordinal.nfp_add_zero`：nfp_add_zero (a) : nfp (a + ·) 0 = a * ω
· 使用定理 `Ordinal.nfp_monotone`：nfp_monotone (hf : Monotone f) : Monotone (nfp f)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
theorem nfp_add_eq_mul_omega0 {a b} (hba : b ≤ a * ω) : nfp (a + ·) b = a * ω := by
  apply le_antisymm (nfp_le_fp (isNormal_add_right a).monotone hba _)
  · rw [← nfp_add_zero]
    exact nfp_monotone (isNormal_add_right a).monotone zero_le
  · rw [← mul_one_add, one_add_omega0]
/-
**Ordinal.add_eq_right_iff_mul_omega0_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_eq_right_iff_mul_omega0_le {a b : Ordinal} : a + b = b ↔ a * ω <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.nfp_add_zero`：nfp_add_zero (a) : nfp (a + ·) 0 = a * ω
· 使用定理 `Ordinal.deriv_zero_right`：deriv_zero_right (f) : deriv f 0 = nfp f 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.mem_range_deriv`：mem_range_deriv (H : IsNormal f) {a} : a in Set
.range (deriv f) ↔ f a = a
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f
· 使用定理 `Ordinal.isNormal_deriv`：isNormal_deriv (f) : IsNormal (deriv f)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.add_sub_cancel_of_le`：∀ {a b : Ordinal.{u_4}}, b ≤ a → b + (a - 
b) = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `mul_one_add`：mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = 
a + a * b
· 使用定理 `Ordinal.one_add_omega0`：one_add_omega0 : 1 + ω = ω
-/
theorem add_eq_right_iff_mul_omega0_le {a b : Ordinal} : a + b = b ↔ a * ω ≤ b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← nfp_add_zero a, ← deriv_zero_right]
    obtain ⟨c, hc⟩ := (mem_range_deriv (isNormal_add_right a)).2 h
    rw [← hc]
    exact (isNormal_deriv _).monotone zero_le
  · have := Ordinal.add_sub_cancel_of_le h
    nth_rw 1 [← this]
    rwa [← add_assoc, ← mul_one_add, one_add_omega0]
/-
**Ordinal.add_le_right_iff_mul_omega0_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：add_le_right_iff_mul_omega0_le {a b : Ordinal} : a + b <= b ↔ a * ω <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.add_eq_right_iff_mul_omega0_le`：add_eq_right_iff_mul_omega0_le {
a b : Ordinal} : a + b = b ↔ a * ω <= b
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
-/
theorem add_le_right_iff_mul_omega0_le {a b : Ordinal} : a + b ≤ b ↔ a * ω ≤ b := by
  rw [← add_eq_right_iff_mul_omega0_le]
  exact (isNormal_add_right a).strictMono.le_apply.ge_iff_eq'
/-
**Ordinal.deriv_add_eq_mul_omega0_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_add_eq_mul_omega0_add (a b : Ordinal.{u}) : deriv (a + ·) b = a * ω 
+ b
参数：a b : Ordinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Order.IsNormal.ext_iff`：ext_iff [OrderBot α] {g : α -> β} (hf : IsNormal
 f) (hg : IsNormal g) : f = g ↔ f ⊥ = g ⊥ ∧ forall a, f a = g a -> f (succ a) = 
g (succ a)
· 使用定理 `Ordinal.isNormal_deriv`：isNormal_deriv (f) : IsNormal (deriv f)
· 使用定理 `Ordinal.isNormal_add_right`：isNormal_add_right (a : Ordinal) : IsNormal 
(a + ·)
· 使用定理 `Ordinal.bot_eq_zero`：bot_eq_zero : (⊥ : Ordinal) = 0
· 使用定理 `Ordinal.deriv_zero_right`：deriv_zero_right (f) : deriv f 0 = nfp f 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordinal.nfp_add_zero`：nfp_add_zero (a) : nfp (a + ·) 0 = a * ω
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
· 使用定理 `Ordinal.deriv_add_one`：deriv_add_one (f o) : deriv f (o + 1) = nfp f (de
riv f o + 1)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Ordinal.nfp_eq_self`：nfp_eq_self {a} (h : f a = a) : nfp f a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.add_eq_right_iff_mul_omega0_le`：add_eq_right_iff_mul_omega0_le {
a b : Ordinal} : a + b = b ↔ a * ω <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
-/
theorem deriv_add_eq_mul_omega0_add (a b : Ordinal.{u}) : deriv (a + ·) b = a * ω + b := by
  revert b
  rw [← funext_iff, IsNormal.ext_iff (isNormal_deriv _) (isNormal_add_right _)]
  refine ⟨?_, fun a h => ?_⟩
  · rw [bot_eq_zero, deriv_zero_right, add_zero]
    exact nfp_add_zero a
  · rw [succ_eq_add_one, deriv_add_one, h, ← add_assoc]
    exact nfp_eq_self (add_eq_right_iff_mul_omega0_le.2 (le_self_add.trans (le_succ _)))

/-! ### Fixed points of multiplication -/

@[simp]
/-
**Ordinal.nfp_mul_one** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp (a * ·) 1 = a ^ ω
参数：ha : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.iSup_iterate_eq_nfp`：iSup_iterate_eq_nfp (f : Ordinal.{u} -> Ord
inal.{u}) (a : Ordinal.{u}) : ⨆ n : Nat, f^[n] a = nfp f a
· 使用定理 `Ordinal.iSup_pow_natCast`：iSup_pow_natCast {o : Ordinal} (ho : 0 < o) : 
⨆ n : Nat, o ^ n = o ^ ω
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Fixed points of multiplication
-/
theorem nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp (a * ·) 1 = a ^ ω := by
  rw [← iSup_iterate_eq_nfp, ← iSup_pow_natCast ha]
  simp

@[simp]
/-
**Ordinal.nfp_mul_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_mul_zero (a : Ordinal) : nfp (a * ·) 0 = 0
参数：a : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Ordinal.nfp_le_iff`：nfp_le_iff {a b} : nfp f a <= b ↔ forall n, f^[n] a 
<= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem nfp_mul_zero (a : Ordinal) : nfp (a * ·) 0 = 0 := by
  rw [← nonpos_iff_eq_zero, nfp_le_iff]
  simp
/-
**Ordinal.nfp_mul_eq_opow_omega0** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_mul_eq_opow_omega0 {a b : Ordinal} (hb : 0 < b) (hba : b <= a ^ ω) : n
fp (a * ·) b = a ^ ω
参数：hb : 0 < b；hba : b <= a ^ ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `Ordinal.omega0_ne_zero`：omega0_ne_zero : ω != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.nfp_le_fp`：nfp_le_fp (H : Monotone f) {a b} (ab : a <= b) (h : f
 b <= b) : nfp f a <= b
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
· 使用定理 `Ordinal.opow_one_add`：opow_one_add (a b : Ordinal) : a ^ (1 + b) = a * a
 ^ b
· 使用定理 `Ordinal.one_add_omega0`：one_add_omega0 : 1 + ω = ω
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ordinal.nfp_mul_one`：nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp (a * ·
) 1 = a ^ ω
· 使用定理 `Ordinal.nfp_monotone`：nfp_monotone (hf : Monotone f) : Monotone (nfp f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
-/
theorem nfp_mul_eq_opow_omega0 {a b : Ordinal} (hb : 0 < b) (hba : b ≤ a ^ ω) :
    nfp (a * ·) b = a ^ ω := by
  rcases eq_zero_or_pos a with rfl | ha
  · rw [zero_opow omega0_ne_zero] at hba
    cases hba.not_gt hb
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone hba
    rw [← opow_one_add, one_add_omega0]
  rw [← nfp_mul_one ha]
  exact nfp_monotone (isNormal_mul_right ha).monotone (one_le_iff_pos.2 hb)
/-
**Ordinal.eq_zero_or_opow_omega0_le_of_mul_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `O
rdinal`。
形式化陈述：eq_zero_or_opow_omega0_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b
) : b = 0 ∨ a ^ ω <= b
参数：hab : a * b = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `Ordinal.omega0_ne_zero`：omega0_ne_zero : ω != 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.nfp_mul_one`：nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp (a * ·
) 1 = a ^ ω
· 使用定理 `Ordinal.nfp_le_fp`：nfp_le_fp (H : Monotone f) {a b} (ab : a <= b) (h : f
 b <= b) : nfp f a <= b
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem eq_zero_or_opow_omega0_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b) :
    b = 0 ∨ a ^ ω ≤ b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_opow omega0_ne_zero]
    exact .inr zero_le
  rw [or_iff_not_imp_left]
  intro hb
  rw [← nfp_mul_one ha]
  rw [← Ne, ← one_le_iff_ne_zero] at hb
  exact nfp_le_fp (isNormal_mul_right ha).monotone hb (le_of_eq hab)
/-
**Ordinal.mul_eq_right_iff_opow_omega0_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_eq_right_iff_opow_omega0_dvd {a b : Ordinal} : a * b = b ↔ a ^ ω ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Ordinal.zero_opow`：zero_opow {a : Ordinal} (a0 : a != 0) : (0 : Ordinal)
 ^ a = 0
· 使用定理 `Ordinal.omega0_ne_zero`：omega0_ne_zero : ω != 0
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Ordinal.dvd_iff_mod_eq_zero`：dvd_iff_mod_eq_zero {a b : Ordinal} : b ∣ a
 ↔ a % b = 0
· 使用定理 `Ordinal.eq_zero_or_opow_omega0_le_of_mul_eq_right`：eq_zero_or_opow_omega
0_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b) : b = 0 ∨ a ^ ω <= b
· 使用定理 `add_left_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 {a b c : G}, a + b = a + c ↔ b = c
· 使用定理 `Ordinal.instIsLeftCancelAdd`：IsLeftCancelAdd Ordinal.{u_4}
· 使用定理 `Ordinal.one_add_omega0`：one_add_omega0 : 1 + ω = ω
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.opow_one_add`：opow_one_add (a b : Ordinal) : a ^ (1 + b) = a * a
 ^ b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Ordinal.div_add_mod`：div_add_mod (a b : Ordinal) : b * (a / b) + a % b =
 a
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Ordinal.mod_lt`：mod_lt (a) {b : Ordinal} (h : b != 0) : a % b < b
· 使用定理 `Ordinal.opow_ne_zero`：opow_ne_zero {a : Ordinal} (b : Ordinal) (a0 : a !
= 0) : a ^ b != 0
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
-/
theorem mul_eq_right_iff_opow_omega0_dvd {a b : Ordinal} : a * b = b ↔ a ^ ω ∣ b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_mul, zero_opow omega0_ne_zero, zero_dvd_iff]
    exact eq_comm
  refine ⟨fun hab => ?_, fun h => ?_⟩
  · rw [dvd_iff_mod_eq_zero]
    rw [← div_add_mod b (a ^ ω), mul_add, ← mul_assoc, ← opow_one_add, one_add_omega0,
      add_left_cancel_iff] at hab
    rcases eq_zero_or_opow_omega0_le_of_mul_eq_right hab with hab | hab
    · exact hab
    refine (not_lt_of_ge hab (mod_lt b (opow_ne_zero ω ?_))).elim
    rwa [← pos_iff_ne_zero]
  obtain ⟨c, hc⟩ := h
  rw [hc, ← mul_assoc, ← opow_one_add, one_add_omega0]
/-
**Ordinal.mul_le_right_iff_opow_omega0_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mul_le_right_iff_opow_omega0_dvd {a b : Ordinal} (ha : 0 < a) : a * b <= b
 ↔ (a ^ ω) ∣ b
参数：ha : 0 < a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.mul_eq_right_iff_opow_omega0_dvd`：mul_eq_right_iff_opow_omega0_d
vd {a b : Ordinal} : a * b = b ↔ a ^ ω ∣ b
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `Order.IsNormal.strictMono`：∀ {α : Type u_1} {β : Type u_2} [inst : Linea
rOrder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → StrictMono 
f
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
-/
theorem mul_le_right_iff_opow_omega0_dvd {a b : Ordinal} (ha : 0 < a) :
    a * b ≤ b ↔ (a ^ ω) ∣ b := by
  rw [← mul_eq_right_iff_opow_omega0_dvd]
  exact (isNormal_mul_right ha).strictMono.le_apply.ge_iff_eq'
/-
**Ordinal.nfp_mul_opow_omega0_add** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nfp_mul_opow_omega0_add {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c) (hca
 : c <= a ^ ω) : nfp (a * ·) (a ^ ω * b + c) = a ^ ω * succ b
参数：b；ha : 0 < a；hc : 0 < c；hca : c <= a ^ ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordinal.nfp_le_fp`：nfp_le_fp (H : Monotone f) {a b} (ab : a <= b) (h : f
 b <= b) : nfp f a <= b
· 使用定理 `Order.IsNormal.monotone`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearO
rder α] [inst_1 : LinearOrder β] {f : α → β},   Order.IsNormal f → Monotone f
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.mul_succ`：mul_succ (a b : Ordinal) : a * succ b = a * b + a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ordinal.opow_one_add`：opow_one_add (a b : Ordinal) : a ^ (1 + b) = a * a
 ^ b
· 使用定理 `Ordinal.one_add_omega0`：one_add_omega0 : 1 + ω = ω
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.mul_eq_right_iff_opow_omega0_dvd`：mul_eq_right_iff_opow_omega0_d
vd {a b : Ordinal} : a * b = b ↔ a ^ ω ∣ b
· 使用定理 `Ordinal.nfp_fp`：nfp_fp (H : IsNormal f) : forall a, f (nfp f a) = nfp f 
a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `Ordinal.le_nfp`：le_nfp (f a) : a <= nfp f a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `Order.succ_le_iff`：succ_le_iff : succ a <= b ↔ a < b
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `mul_lt_mul_iff_right₀`：mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMu
lReflectLT α] (a0 : 0 < a) : a * b < a * c ↔ b < c where mp h
· 使用定理 `Ordinal.instPosMulStrictMono`：PosMulStrictMono Ordinal.{u_4}
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem nfp_mul_opow_omega0_add {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c)
    (hca : c ≤ a ^ ω) : nfp (a * ·) (a ^ ω * b + c) = a ^ ω * succ b := by
  apply le_antisymm
  · apply nfp_le_fp (isNormal_mul_right ha).monotone
    · rw [mul_succ]
      gcongr
    · rw [← mul_assoc, ← opow_one_add, one_add_omega0]
  · obtain ⟨d, hd⟩ :=
      mul_eq_right_iff_opow_omega0_dvd.1 (nfp_fp (isNormal_mul_right ha) (a ^ ω * b + c))
    rw [hd]
    apply mul_le_mul_right
    have := le_nfp (a * ·) (a ^ ω * b + c)
    rw [hd] at this
    have := (add_lt_add_right hc (a ^ ω * b)).trans_le this
    rw [add_zero, mul_lt_mul_iff_right₀ (opow_pos ω ha)] at this
    rwa [succ_le_iff]
/-
**Ordinal.deriv_mul_eq_opow_omega0_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：deriv_mul_eq_opow_omega0_mul {a : Ordinal.{u}} (ha : 0 < a) (b) : deriv (a
 * ·) b = a ^ ω * b
参数：ha : 0 < a；b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Order.IsNormal.ext_iff`：ext_iff [OrderBot α] {g : α -> β} (hf : IsNormal
 f) (hg : IsNormal g) : f = g ↔ f ⊥ = g ⊥ ∧ forall a, f a = g a -> f (succ a) = 
g (succ a)
· 使用定理 `Ordinal.isNormal_deriv`：isNormal_deriv (f) : IsNormal (deriv f)
· 使用定理 `Ordinal.isNormal_mul_right`：isNormal_mul_right {a : Ordinal} (h : 0 < a)
 : IsNormal (a * ·)
· 使用定理 `Ordinal.opow_pos`：opow_pos {a : Ordinal} (b : Ordinal) (a0 : 0 < a) : 0 
< a ^ b
· 使用定理 `Ordinal.bot_eq_zero`：bot_eq_zero : (⊥ : Ordinal) = 0
· 使用定理 `Ordinal.deriv_zero_right`：deriv_zero_right (f) : deriv f 0 = nfp f 0
· 使用定理 `Ordinal.nfp_mul_zero`：nfp_mul_zero (a : Ordinal) : nfp (a * ·) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Ordinal.deriv_succ`：deriv_succ (f o) : deriv f (succ o) = nfp f (succ (d
eriv f o))
· 使用定理 `Ordinal.nfp_mul_opow_omega0_add`：nfp_mul_opow_omega0_add {a c : Ordinal}
 (b) (ha : 0 < a) (hc : 0 < c) (hca : c <= a ^ ω) : nfp (a * ·) (a ^ ω * b + c) 
= a ^ ω * succ b
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
-/
theorem deriv_mul_eq_opow_omega0_mul {a : Ordinal.{u}} (ha : 0 < a) (b) :
    deriv (a * ·) b = a ^ ω * b := by
  revert b
  rw [← funext_iff,
    IsNormal.ext_iff (isNormal_deriv _) (isNormal_mul_right (opow_pos ω ha))]
  refine ⟨?_, fun c h => ?_⟩
  · rw [bot_eq_zero, deriv_zero_right, nfp_mul_zero, mul_zero]
  · rw [deriv_succ, h]
    exact nfp_mul_opow_omega0_add c ha zero_lt_one (one_le_iff_pos.2 (opow_pos _ ha))

end Ordinal

