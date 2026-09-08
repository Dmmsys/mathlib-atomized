/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.PiLex
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Complete linear order instance on lexicographically ordered pi types

We show that for `α` a family of complete linear orders, the lexicographically ordered type of
dependent functions `Πₗ i, α i` is itself a complete linear order.
-/

@[expose] public section

variable {ι : Type*} {α : ι → Type*} [LinearOrder ι] [∀ i, CompleteLinearOrder (α i)]

namespace Pi

/-! ### Lexicographic ordering -/

namespace Lex

/-
**Pi.Lex.inf** 是 Mathlib 中的一个定义，位于命名空间 `Pi.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def inf [WellFoundedLT ι] (s : Set (Πₗ i, α i)) (i : ι) : α i :=
  ⨅ e : {e ∈ s | ∀ j < i, e j = inf s j}, e.1 i
termination_by wellFounded_lt.wrap i

variable [WellFoundedLT ι]

@[no_expose]
/-
**Pi.Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Pi.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Πₗ i, α i) where
  sInf s := toLex (inf s)
/-
**Pi.Lex.sInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
形式化陈述：sInf_apply (s : Set (Πₗ i, α i)) (i : ι) : sInf s i = ⨅ e : {e in s | fora
ll j < i, e j = sInf s j}, e.1 i
参数：s : Set (Πₗ i, α i)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Order.CompleteLattice.PiLex.0.Pi.Lex.inf.eq_1`：∀ {ι : T
ype u_1} {α : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (i : ι) → CompleteL
inearOrder (α i)]   [inst_2 : WellFoundedLT ι] (s : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_apply (s : Set (Πₗ i, α i)) (i : ι) :
    sInf s i = ⨅ e : {e ∈ s | ∀ j < i, e j = sInf s j}, e.1 i := by
  simp [sInf, inf]
/-
**Pi.Lex.sInf_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
形式化陈述：sInf_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i} (he : e in s) 
(h : forall j < i, e j = sInf s j) : sInf s i <= e i
参数：Πₗ i, α i；he : e in s；h : forall j < i, e j = sInf s j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.Lex.sInf_apply`：sInf_apply (s : Set (Πₗ i, α i)) (i : ι) : sInf s i =
 ⨅ e : {e in s | forall j < i, e j = sInf s j}, e.1 i
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem sInf_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e ∈ s) (h : ∀ j < i, e j = sInf s j) : sInf s i ≤ e i := by
  rw [sInf_apply]
  exact sInf_le ⟨⟨e, he, h⟩, rfl⟩
/-
**Pi.Lex.le_sInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
形式化陈述：le_sInf_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i} (h : forall f 
in s, (forall j < i, f j = sInf s j) -> e i <= f i) : e i <= sInf s i
参数：Πₗ i, α i；h : forall f in s, (forall j < i, f j = sInf s j) -> e i <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.Lex.sInf_apply`：sInf_apply (s : Set (Πₗ i, α i)) (i : ι) : sInf s i =
 ⨅ e : {e in s | forall j < i, e j = sInf s j}, e.1 i
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
-/
theorem le_sInf_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : ∀ f ∈ s, (∀ j < i, f j = sInf s j) → e i ≤ f i) : e i ≤ sInf s i := by
  rw [sInf_apply]
  apply le_sInf
  grind
/-
**Pi.Lex.isGLB_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isGLB_sInf {s : Set (Πₗ i, α i)} : IsGLB s (sInf s) := by
  refine ⟨fun e he ↦ ?_, fun e h ↦ ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (sInf_apply_le he ha.1)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    refine ha.2.not_ge <| le_sInf_apply fun f hf hf' ↦ apply_le_of_toLex (h hf) ?_
    simp_all

-- TODO: figure out how to use `to_dual` here

@[no_expose]
/-
**Pi.Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Pi.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet (Πₗ i, α i) where
  sSup s := sInf (α := Πₗ i, (α i)ᵒᵈ) s
/-
**Pi.Lex.sSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
形式化陈述：sSup_apply (s : Set (Πₗ i, α i)) (i : ι) : sSup s i = ⨆ e : {e in s | fora
ll j < i, e j = sSup s j}, e.1 i
参数：s : Set (Πₗ i, α i)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.sInf_apply`：sInf_apply (s : Set (Πₗ i, α i)) (i : ι) : sInf s i =
 ⨅ e : {e in s | forall j < i, e j = sInf s j}, e.1 i
-/
theorem sSup_apply (s : Set (Πₗ i, α i)) (i : ι) :
    sSup s i = ⨆ e : {e ∈ s | ∀ j < i, e j = sSup s j}, e.1 i :=
  sInf_apply (α := fun i ↦ (α i)ᵒᵈ) ..
/-
**Pi.Lex.le_sSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
形式化陈述：le_sSup_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i} (he : e in s) 
(h : forall j < i, e j = sSup s j) : e i <= sSup s i
参数：Πₗ i, α i；he : e in s；h : forall j < i, e j = sSup s j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.sInf_apply_le`：sInf_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Π
ₗ i, α i} (he : e in s) (h : forall j < i, e j = sInf s j) : sInf s i <= e i
-/
theorem le_sSup_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (he : e ∈ s) (h : ∀ j < i, e j = sSup s j) : e i ≤ sSup s i :=
  sInf_apply_le (α := fun i ↦ (α i)ᵒᵈ) he h
/-
**Pi.Lex.sSup_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
形式化陈述：sSup_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i} (h : forall f 
in s, (forall j < i, f j = sSup s j) -> f i <= e i) : sSup s i <= e i
参数：Πₗ i, α i；h : forall f in s, (forall j < i, f j = sSup s j) -> f i <= e i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.le_sInf_apply`：le_sInf_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Π
ₗ i, α i} (h : forall f in s, (forall j < i, f j = sInf s j) -> e i <= f i) : e 
i <= sInf …
-/
theorem sSup_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Πₗ i, α i}
    (h : ∀ f ∈ s, (∀ j < i, f j = sSup s j) → f i ≤ e i) : sSup s i ≤ e i :=
  le_sInf_apply (α := fun i ↦ (α i)ᵒᵈ) h
/-
**Pi.Lex.isLUB_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isLUB_sSup {s : Set (Πₗ i, α i)} : IsLUB s (sSup s) := by
  refine ⟨fun e he ↦ ?_, fun e h ↦ ?_⟩
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    exact ha.2.not_ge (le_sSup_apply he fun j hj ↦ (ha.1 j hj).symm)
  · by_contra! hs
    obtain ⟨a, ha⟩ := hs
    refine ha.2.not_ge <| sSup_apply_le fun f hf hf' ↦ apply_le_of_toLex (h hf) ?_
    simp_all
/-
**Pi.Lex.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `Pi.Lex`。
形式化陈述：completeLattice : CompleteLattice (Πₗ i, α i) where isLUB_sSup _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance completeLattice : CompleteLattice (Πₗ i, α i) where
  isLUB_sSup _ := by exact isLUB_sSup
  isGLB_sInf _ := by exact isGLB_sInf
/-
**Pi.Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Pi.Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CompleteLinearOrder (Πₗ i, α i) where
  __ := linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

end Lex

/-! ### Colexicographic ordering -/

namespace Colex
variable [WellFoundedGT ι]

set_option backward.isDefEq.respectTransparency false in
@[no_expose]
/-
**Pi.Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Pi.Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Colex ((i : ι) → α i)) where
  sInf s := sInf (α := Πₗ i : ιᵒᵈ, α i) s

set_option backward.isDefEq.respectTransparency false in
/-
**Pi.Colex.sInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Colex`。
形式化陈述：sInf_apply (s : Set (Colex ((i : ι) -> α i))) (i : ι) : sInf s i = ⨅ e : {
e in s | forall j > i, e j = sInf s j}, e.1 i
参数：s : Set (Colex ((i : ι) -> α i))；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.sInf_apply`：sInf_apply (s : Set (Πₗ i, α i)) (i : ι) : sInf s i =
 ⨅ e : {e in s | forall j < i, e j = sInf s j}, e.1 i
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem sInf_apply (s : Set (Colex ((i : ι) → α i))) (i : ι) :
    sInf s i = ⨅ e : {e ∈ s | ∀ j > i, e j = sInf s j}, e.1 i :=
  Lex.sInf_apply (ι := ιᵒᵈ) s i

set_option backward.isDefEq.respectTransparency false in
/-
**Pi.Colex.sInf_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Colex`。
形式化陈述：sInf_apply_le {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : 
ι) -> α i)} (he : e in s) (h : forall j > i, e j = sInf s j) : sInf s i <= e i
参数：Colex ((i : ι) -> α i)；(i : ι) -> α i；he : e in s；h : forall j > i, e j = sIn
f s j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.sInf_apply_le`：sInf_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Π
ₗ i, α i} (he : e in s) (h : forall j < i, e j = sInf s j) : sInf s i <= e i
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem sInf_apply_le {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (he : e ∈ s) (h : ∀ j > i, e j = sInf s j) : sInf s i ≤ e i :=
  Lex.sInf_apply_le (ι := ιᵒᵈ) he h

set_option backward.isDefEq.respectTransparency false in
/-
**Pi.Colex.le_sInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Colex`。
形式化陈述：le_sInf_apply {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : 
ι) -> α i)} (h : forall f in s, (forall j > i, f j = sInf s j) -> e i <= f i) : 
e i <= sInf s i
参数：Colex ((i : ι) -> α i)；(i : ι) -> α i；h : forall f in s, (forall j > i, f j =
 sInf s j) -> e i <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.le_sInf_apply`：le_sInf_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Π
ₗ i, α i} (h : forall f in s, (forall j < i, f j = sInf s j) -> e i <= f i) : e 
i <= sInf …
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem le_sInf_apply {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (h : ∀ f ∈ s, (∀ j > i, f j = sInf s j) → e i ≤ f i) : e i ≤ sInf s i :=
  Lex.le_sInf_apply (ι := ιᵒᵈ) h

-- TODO: figure out how to use `to_dual` here

set_option backward.isDefEq.respectTransparency false in
@[no_expose]
/-
**Pi.Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Pi.Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupSet (Colex ((i : ι) → α i)) where
  sSup s := sSup (α := Πₗ i : ιᵒᵈ, α i) s

set_option backward.isDefEq.respectTransparency false in
/-
**Pi.Colex.sSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Colex`。
形式化陈述：sSup_apply (s : Set (Colex ((i : ι) -> α i))) (i : ι) : sSup s i = ⨆ e : {
e in s | forall j > i, e j = sSup s j}, e.1 i
参数：s : Set (Colex ((i : ι) -> α i))；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.sSup_apply`：sSup_apply (s : Set (Πₗ i, α i)) (i : ι) : sSup s i =
 ⨆ e : {e in s | forall j < i, e j = sSup s j}, e.1 i
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem sSup_apply (s : Set (Colex ((i : ι) → α i))) (i : ι) :
    sSup s i = ⨆ e : {e ∈ s | ∀ j > i, e j = sSup s j}, e.1 i :=
  Lex.sSup_apply (ι := ιᵒᵈ) s i

set_option backward.isDefEq.respectTransparency false in
/-
**Pi.Colex.le_sSup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Colex`。
形式化陈述：le_sSup_apply {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : 
ι) -> α i)} (he : e in s) (h : forall j > i, e j = sSup s j) : e i <= sSup s i
参数：Colex ((i : ι) -> α i)；(i : ι) -> α i；he : e in s；h : forall j > i, e j = sSu
p s j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.le_sSup_apply`：le_sSup_apply {s : Set (Πₗ i, α i)} {i : ι} {e : Π
ₗ i, α i} (he : e in s) (h : forall j < i, e j = sSup s j) : e i <= sSup s i
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem le_sSup_apply {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (he : e ∈ s) (h : ∀ j > i, e j = sSup s j) : e i ≤ sSup s i :=
  Lex.le_sSup_apply (ι := ιᵒᵈ) he h

set_option backward.isDefEq.respectTransparency false in
/-
**Pi.Colex.sSup_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Colex`。
形式化陈述：sSup_apply_le {s : Set (Colex ((i : ι) -> α i))} {i : ι} {e : Colex ((i : 
ι) -> α i)} (h : forall f in s, (forall j > i, f j = sSup s j) -> f i <= e i) : 
sSup s i <= e i
参数：Colex ((i : ι) -> α i)；(i : ι) -> α i；h : forall f in s, (forall j > i, f j =
 sSup s j) -> f i <= e i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.sSup_apply_le`：sSup_apply_le {s : Set (Πₗ i, α i)} {i : ι} {e : Π
ₗ i, α i} (h : forall f in s, (forall j < i, f j = sSup s j) -> f i <= e i) : sS
up s i <= …
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem sSup_apply_le {s : Set (Colex ((i : ι) → α i))} {i : ι} {e : Colex ((i : ι) → α i)}
    (h : ∀ f ∈ s, (∀ j > i, f j = sSup s j) → f i ≤ e i) : sSup s i ≤ e i :=
  Lex.sSup_apply_le (ι := ιᵒᵈ) h

set_option backward.isDefEq.respectTransparency false in
/-
**Pi.Colex.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 `Pi.Colex`。
形式化陈述：completeLattice : CompleteLattice (Colex ((i : ι) -> α i)) where isLUB_sSu
p _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance completeLattice : CompleteLattice (Colex ((i : ι) → α i)) where
  isLUB_sSup _ := by exact Lex.isLUB_sSup (ι := ιᵒᵈ)
  isGLB_sInf _ := by exact Lex.isGLB_sInf (ι := ιᵒᵈ)
/-
**Pi.Colex.** 是 Mathlib 中的一个实例，位于命名空间 `Pi.Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CompleteLinearOrder (Colex ((i : ι) → α i)) where
  __ := linearOrder
  __ := completeLattice
  __ := LinearOrder.toBiheytingAlgebra _

end Colex
end Pi

