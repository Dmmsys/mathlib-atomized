/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Dedup
public import Mathlib.Data.Multiset.UnionInter

/-!
# Erasing duplicates in a multiset.
-/

@[expose] public section

assert_not_exists Monoid

namespace Multiset

open List

variable {α β : Type*} [DecidableEq α]

/-! ### dedup -/


/-- `dedup s` removes duplicates from `s`, yielding a `nodup` multiset. -/
/-
**Multiset.dedup** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：dedup (s : Multiset α) : Multiset α
参数：s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`dedup s` removes duplicates from `s`, yielding a `nodup` multiset.
-/
def dedup (s : Multiset α) : Multiset α :=
  Quot.liftOn s (fun l => (l.dedup : Multiset α)) fun _ _ p => Quot.sound p.dedup

@[simp]
/-
**Multiset.coe_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_dedup (l : List α) : @dedup α _ l = l.dedup
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_dedup (l : List α) : @dedup α _ l = l.dedup :=
  rfl

@[simp]
/-
**Multiset.dedup_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_zero : @dedup α _ 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dedup_zero : @dedup α _ 0 = 0 :=
  rfl

@[simp]
/-
**Multiset.mem_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_dedup {a : α} {s : Multiset α} : a in dedup s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.mem_dedup`：mem_dedup {a : α} {l : List α} : a in dedup l ↔ a in l
-/
theorem mem_dedup {a : α} {s : Multiset α} : a ∈ dedup s ↔ a ∈ s :=
  Quot.induction_on s fun _ => List.mem_dedup

@[simp]
/-
**Multiset.dedup_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_cons_of_mem {a : α} {s : Multiset α} : a in s -> dedup (a ::ₘ s) = d
edup s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {l : List α} (h : a in
 l) : dedup (a :: l) = dedup l
-/
theorem dedup_cons_of_mem {a : α} {s : Multiset α} : a ∈ s → dedup (a ::ₘ s) = dedup s :=
  Quot.induction_on s fun _ m => @congr_arg _ _ _ _ ofList <| List.dedup_cons_of_mem m

@[simp]
/-
**Multiset.dedup_cons_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_cons_of_notMem {a : α} {s : Multiset α} : a ∉ s -> dedup (a ::ₘ s) =
 a ::ₘ dedup s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {l : List α} (h 
: a ∉ l) : dedup (a :: l) = a :: dedup l
-/
theorem dedup_cons_of_notMem {a : α} {s : Multiset α} : a ∉ s → dedup (a ::ₘ s) = a ::ₘ dedup s :=
  Quot.induction_on s fun _ m => congr_arg ofList <| List.dedup_cons_of_notMem m
/-
**Multiset.dedup_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_le (s : Multiset α) : dedup s <= s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.dedup_sublist`：dedup_sublist : forall l : List α, dedup l <+ l
-/
theorem dedup_le (s : Multiset α) : dedup s ≤ s :=
  Quot.induction_on s fun _ => (dedup_sublist _).subperm
/-
**Multiset.dedup_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_subset (s : Multiset α) : dedup s subseteq s
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `Multiset.dedup_le`：dedup_le (s : Multiset α) : dedup s <= s
-/
theorem dedup_subset (s : Multiset α) : dedup s ⊆ s :=
  subset_of_le <| dedup_le _
/-
**Multiset.subset_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：subset_dedup (s : Multiset α) : s subseteq dedup s
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_dedup`：mem_dedup {a : α} {s : Multiset α} : a in dedup s ↔ 
a in s
-/
theorem subset_dedup (s : Multiset α) : s ⊆ dedup s := fun _ => mem_dedup.2

@[simp]
/-
**Multiset.dedup_subset'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_subset' {s t : Multiset α} : dedup s subseteq t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Subset.trans`：∀ {α : Type u_1} {s t u : Multiset α}, s ⊆ t → t 
⊆ u → s ⊆ u
· 使用定理 `Multiset.subset_dedup`：subset_dedup (s : Multiset α) : s subseteq dedup 
s
· 使用定理 `Multiset.dedup_subset`：dedup_subset (s : Multiset α) : dedup s subseteq 
s
-/
theorem dedup_subset' {s t : Multiset α} : dedup s ⊆ t ↔ s ⊆ t :=
  ⟨Subset.trans (subset_dedup _), Subset.trans (dedup_subset _)⟩

@[simp]
/-
**Multiset.subset_dedup'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：subset_dedup' {s t : Multiset α} : s subseteq dedup t ↔ s subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Subset.trans`：∀ {α : Type u_1} {s t u : Multiset α}, s ⊆ t → t 
⊆ u → s ⊆ u
· 使用定理 `Multiset.dedup_subset`：dedup_subset (s : Multiset α) : dedup s subseteq 
s
· 使用定理 `Multiset.subset_dedup`：subset_dedup (s : Multiset α) : s subseteq dedup 
s
-/
theorem subset_dedup' {s t : Multiset α} : s ⊆ dedup t ↔ s ⊆ t :=
  ⟨fun h => Subset.trans h (dedup_subset _), fun h => Subset.trans h (subset_dedup _)⟩

@[simp]
/-
**Multiset.nodup_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_dedup (s : Multiset α) : Nodup (dedup s)
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.nodup_dedup`：nodup_dedup : forall l : List α, Nodup (dedup l)
-/
theorem nodup_dedup (s : Multiset α) : Nodup (dedup s) :=
  Quot.induction_on s List.nodup_dedup
/-
**Multiset.dedup_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_eq_self {s : Multiset α} : dedup s = s ↔ Nodup s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_dedup`：nodup_dedup (s : Multiset α) : Nodup (dedup s)
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {l : List α}, 
l.Nodup → l.dedup = l
-/
theorem dedup_eq_self {s : Multiset α} : dedup s = s ↔ Nodup s :=
  ⟨fun e => e ▸ nodup_dedup s, Quot.induction_on s fun _ h => congr_arg ofList h.dedup⟩

alias ⟨_, Nodup.dedup⟩ := dedup_eq_self
/-
**Multiset.count_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_dedup (m : Multiset α) (a : α) : m.dedup.count a = if a in m then 1 
else 0
参数：m : Multiset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `List.count_dedup`：count_dedup (l : List α) (a : α) : l.dedup.count a = i
f a in l then 1 else 0
-/
theorem count_dedup (m : Multiset α) (a : α) : m.dedup.count a = if a ∈ m then 1 else 0 :=
  Quot.induction_on m fun _ => by
    simp only [quot_mk_to_coe'', coe_dedup, mem_coe, coe_count]
    apply List.count_dedup _ _

@[simp]
/-
**Multiset.dedup_idem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_idem {m : Multiset α} : m.dedup.dedup = m.dedup
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.dedup_idem`：dedup_idem {l : List α} : dedup (dedup l) = dedup l
-/
theorem dedup_idem {m : Multiset α} : m.dedup.dedup = m.dedup :=
  Quot.induction_on m fun _ => @congr_arg _ _ _ _ ofList List.dedup_idem
/-
**Multiset.dedup_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_eq_zero {s : Multiset α} : dedup s = 0 ↔ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.eq_zero_of_subset_zero`：eq_zero_of_subset_zero {s : Multiset α}
 (h : s subseteq 0) : s = 0
· 使用定理 `Multiset.subset_dedup`：subset_dedup (s : Multiset α) : s subseteq dedup 
s
· 使用定理 `Multiset.dedup_zero`：dedup_zero : @dedup α _ 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dedup_eq_zero {s : Multiset α} : dedup s = 0 ↔ s = 0 :=
  ⟨fun h => eq_zero_of_subset_zero <| h ▸ subset_dedup _, fun h => h.symm ▸ dedup_zero⟩

@[simp]
/-
**Multiset.dedup_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_singleton {a : α} : dedup ({a} : Multiset α) = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Multiset.nodup_singleton`：nodup_singleton : forall a : α, Nodup ({a} : M
ultiset α)
-/
theorem dedup_singleton {a : α} : dedup ({a} : Multiset α) = {a} :=
  (nodup_singleton _).dedup
/-
**Multiset.le_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_dedup {s t : Multiset α} : s <= dedup t ↔ s <= t ∧ Nodup s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Multiset.dedup_le`：dedup_le (s : Multiset α) : dedup s <= s
· 使用定理 `Multiset.nodup_of_le`：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodu
p t -> Nodup s
· 使用定理 `Multiset.nodup_dedup`：nodup_dedup (s : Multiset α) : Nodup (dedup s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_iff_subset`：le_iff_subset {s t : Multiset α} : Nodup s -> (s
 <= t ↔ s subseteq t)
· 使用定理 `Multiset.Subset.trans`：∀ {α : Type u_1} {s t u : Multiset α}, s ⊆ t → t 
⊆ u → s ⊆ u
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `Multiset.subset_dedup`：subset_dedup (s : Multiset α) : s subseteq dedup 
s
-/
theorem le_dedup {s t : Multiset α} : s ≤ dedup t ↔ s ≤ t ∧ Nodup s :=
  ⟨fun h => ⟨le_trans h (dedup_le _), nodup_of_le h (nodup_dedup _)⟩,
   fun ⟨l, d⟩ => (le_iff_subset d).2 <| Subset.trans (subset_of_le l) (subset_dedup _)⟩
/-
**Multiset.le_dedup_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_dedup_self {s : Multiset α} : s <= dedup s ↔ Nodup s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.le_dedup`：le_dedup {s t : Multiset α} : s <= dedup t ↔ s <= t ∧
 Nodup s
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_dedup_self {s : Multiset α} : s ≤ dedup s ↔ Nodup s := by
  rw [le_dedup, and_iff_right le_rfl]
/-
**Multiset.dedup_ext** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ forall a, a in s ↔ a in
 t
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ ∀ a, a ∈ s ↔ a ∈ t := by
  simp [Nodup.ext]
/-
**Multiset.dedup_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_map_of_injective [DecidableEq β] {f : α -> β} (hf : Function.Injecti
ve f) (s : Multiset α) : (s.map f).dedup = s.dedup.map f
参数：hf : Function.Injective f；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dedup_map_of_injective`：dedup_map_of_injective [DecidableEq β] {f :
 α -> β} (hf : Function.Injective f) (xs : List α) : (xs.map f).dedup = xs.dedup
.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dedup_map_of_injective [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (s : Multiset α) :
    (s.map f).dedup = s.dedup.map f :=
  Quot.induction_on s fun l => by simp [List.dedup_map_of_injective hf l]
/-
**Multiset.dedup_map_dedup_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：dedup_map_dedup_eq [DecidableEq β] (f : α -> β) (s : Multiset α) : dedup (
map f (dedup s)) = dedup (map f s)
参数：f : α -> β；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem dedup_map_dedup_eq [DecidableEq β] (f : α → β) (s : Multiset α) :
    dedup (map f (dedup s)) = dedup (map f s) := by
  simp [dedup_ext]
/-
**Multiset.Nodup.le_dedup_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, s.Nodup → (s ≤
 t.dedup ↔ s ≤ t)
参数：s ≤ t.dedup ↔ s ≤ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Nodup.le_dedup_iff_le {s t : Multiset α} (hno : s.Nodup) : s ≤ t.dedup ↔ s ≤ t := by
  simp [le_dedup, hno]
/-
**Multiset.Subset.dedup_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Subset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, s ⊆ t → (s + t
).dedup = t.dedup
参数：s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.Subset.dedup_append_right`：∀ {α : Type u_1} [inst : DecidableEq α] 
{xs ys : List α}, xs ⊆ ys → (xs ++ ys).dedup = ys.dedup
-/
theorem Subset.dedup_add_right {s t : Multiset α} (h : s ⊆ t) :
    dedup (s + t) = dedup t := by
  induction s, t using Quot.induction_on₂
  exact congr_arg ((↑) : List α → Multiset α) <| List.Subset.dedup_append_right h
/-
**Multiset.Subset.dedup_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Subset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, t ⊆ s → (s + t
).dedup = s.dedup
参数：s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用定理 `Multiset.Subset.dedup_add_right`：∀ {α : Type u_1} [inst : DecidableEq α]
 {s t : Multiset α}, s ⊆ t → (s + t).dedup = t.dedup
-/
theorem Subset.dedup_add_left {s t : Multiset α} (h : t ⊆ s) :
    dedup (s + t) = dedup s := by
  rw [s.add_comm, Subset.dedup_add_right h]
/-
**Multiset.Disjoint.dedup_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Disjoint`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, Disjoint s t →
 (s + t).dedup = s.dedup + t.dedup
参数：s + t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.Disjoint.dedup_append`：∀ {α : Type u_1} [inst : DecidableEq α] {xs 
ys : List α}, xs.Disjoint ys → (xs ++ ys).dedup = xs.dedup ++ ys.dedup
-/
theorem Disjoint.dedup_add {s t : Multiset α} (h : Disjoint s t) :
    dedup (s + t) = dedup s + dedup t := by
  induction s, t using Quot.induction_on₂
  exact congr_arg ((↑) : List α → Multiset α) <| List.Disjoint.dedup_append (by simpa using h)

/-- Note that the stronger `List.Subset.dedup_append_right` is proved earlier. -/
/-
**Multiset._root_.List.Subset.dedup_append_left** 是 Mathlib 中的一个定理，位于命名空间 `Multi
set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that the stronger `List.Subset.dedup_append_right` is proved earlier.
-/
theorem _root_.List.Subset.dedup_append_left {s t : List α} (h : t ⊆ s) :
    List.dedup (s ++ t) ~ List.dedup s := by
  rw [← coe_eq_coe, ← coe_dedup, ← coe_add, Subset.dedup_add_left h, coe_dedup]

end Multiset

