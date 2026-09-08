/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Perm.Lattice
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Order.MinMax
public import Mathlib.Logic.Pairwise

/-!
# Distributive lattice structure on multisets

This file defines an instance `DistribLattice (Multiset α)` using the union and intersection
operators:

* `s ∪ t`: The multiset for which the number of occurrences of each `a` is the max of the
  occurrences of `a` in `s` and `t`.
* `s ∩ t`: The multiset for which the number of occurrences of each `a` is the min of the
  occurrences of `a` in `s` and `t`.
-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

/-! ### Union -/

/-- `s ∪ t` is the multiset such that the multiplicity of each `a` in it is the maximum of the
multiplicity of `a` in `s` and `t`. This is the supremum of multisets. -/
/-
**Multiset.union** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：union (s t : Multiset α) : Multiset α
参数：s t : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ∪ t` is the multiset such that the multiplicity of each `a` in it is the maxi
mum of the
multiplicity of `a` in `s` and `t`. This is the supremum of multisets.
-/
def union (s t : Multiset α) : Multiset α := s - t + t
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Union (Multiset α) :=
  ⟨union⟩
/-
**Multiset.union_def** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：union_def (s t : Multiset α) : s union t = s - t + t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma union_def (s t : Multiset α) : s ∪ t = s - t + t := rfl
/-
**Multiset.le_union_left** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：le_union_left : s <= s union t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.le_sub_add`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Mult
iset α}, s ≤ s - t + t
-/
lemma le_union_left : s ≤ s ∪ t := Multiset.le_sub_add
/-
**Multiset.le_union_right** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：le_union_right : t <= s union t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.le_add_left`：le_add_left (s t : Multiset α) : s <= t + s
-/
lemma le_union_right : t ≤ s ∪ t := le_add_left _ _
/-
**Multiset.eq_union_left** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：eq_union_left : t <= s -> s union t = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sub_add_cancel`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : 
Multiset α}, t ≤ s → s - t + t = s
-/
lemma eq_union_left : t ≤ s → s ∪ t = s := Multiset.sub_add_cancel

@[gcongr]
/-
**Multiset.union_le_union_right** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：union_le_union_right (h : s <= t) (u) : s union u <= t union u
参数：h : s <= t；u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.add_le_add_right`：∀ {α : Type u_1} {s t u : Multiset α}, s ≤ t 
→ s + u ≤ t + u
· 使用定理 `Multiset.sub_le_sub_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s t 
u : Multiset α}, s ≤ t → s - u ≤ t - u
-/
lemma union_le_union_right (h : s ≤ t) (u) : s ∪ u ≤ t ∪ u :=
  Multiset.add_le_add_right <| Multiset.sub_le_sub_right h
/-
**Multiset.union_le** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：union_le (h₁ : s <= u) (h₂ : t <= u) : s union t <= u
参数：h₁ : s <= u；h₂ : t <= u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multiset.eq_union_left`：eq_union_left : t <= s -> s union t = s
· 使用引理 `Multiset.union_le_union_right`：union_le_union_right (h : s <= t) (u) : s
 union u <= t union u
-/
lemma union_le (h₁ : s ≤ u) (h₂ : t ≤ u) : s ∪ t ≤ u := by
  rw [← eq_union_left h₂]; exact union_le_union_right h₁ t

@[simp]
/-
**Multiset.mem_union** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：mem_union : a in s union t ↔ a in s ∨ a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `Multiset.sub_le_self`：∀ {α : Type u_1} [inst : DecidableEq α] (s t : Mul
tiset α), s - t ≤ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `Multiset.le_union_left`：le_union_left : s <= s union t
· 使用引理 `Multiset.le_union_right`：le_union_right : t <= s union t
-/
lemma mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
  ⟨fun h => (mem_add.1 h).imp_left (mem_of_le <| Multiset.sub_le_self _ _),
    (Or.elim · (mem_of_le le_union_left) (mem_of_le le_union_right))⟩

@[simp]
/-
**Multiset.map_union** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_union [DecidableEq β] {f : α -> β} (finj : Function.Injective f) {s t 
: Multiset α} : map f (s union t) = map f s union map f t
参数：finj : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_diff`：map_diff [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f :
 α -> β} (finj : Injective f) {l₁ l₂ : List α} : map f (l₁.diff l₂) = (map f l₁)
.di…
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
lemma map_union [DecidableEq β] {f : α → β} (finj : Function.Injective f) {s t : Multiset α} :
    map f (s ∪ t) = map f s ∪ map f t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ =>
    congr_arg ofList (by rw [List.map_append, List.map_diff finj])
/-
**Multiset.zero_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multiset α}, 0 ∪ s = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.zero_sub`：∀ {α : Type u_1} [inst : DecidableEq α] (t : Multiset
 α), 0 - t = 0
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma zero_union : 0 ∪ s = s := by simp [union_def, Multiset.zero_sub]
/-
**Multiset.union_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multiset α}, s ∪ 0 = s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sub_zero`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multiset
 α), s - 0 = s
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma union_zero : s ∪ 0 = s := by simp [union_def]

@[simp]
/-
**Multiset.count_union** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：count_union (a : α) (s t : Multiset α) : count a (s union t) = max (count 
a s) (count a t)
参数：a : α；s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `Nat.sub_add_eq_max`：∀ (a b : ℕ), a - b + b = max a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma count_union (a : α) (s t : Multiset α) : count a (s ∪ t) = max (count a s) (count a t) := by
  simp [(· ∪ ·), union, Nat.sub_add_eq_max]
/-
**Multiset.filter_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (p : α → Prop) [inst_1 : Decidable
Pred p] (s t : Multiset α),   Multiset.filter p (s ∪ t) = Multiset.filter p s ∪ 
Multiset.filter p t
参数：p : α → Prop；s t : Multiset α；s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_add`：filter_add (s t : Multiset α) : filter p (s + t) = 
filter p s + filter p t
· 使用引理 `Multiset.filter_sub`：filter_sub (p : α -> Prop) [DecidablePred p] (s t :
 Multiset α) : filter p (s - t) = filter p s - filter p t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma filter_union (p : α → Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s ∪ t) = filter p s ∪ filter p t := by simp [(· ∪ ·), union]

/-! ### Intersection -/

/-- `s ∩ t` is the multiset such that the multiplicity of each `a` in it is the minimum of the
multiplicity of `a` in `s` and `t`. This is the infimum of multisets. -/
/-
**Multiset.inter** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：inter (s t : Multiset α) : Multiset α
参数：s t : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s ∩ t` is the multiset such that the multiplicity of each `a` in it is the mini
mum of the
multiplicity of `a` in `s` and `t`. This is the infimum of multisets.
-/
def inter (s t : Multiset α) : Multiset α :=
  Quotient.liftOn₂ s t (fun l₁ l₂ => (l₁.bagInter l₂ : Multiset α)) fun _v₁ _v₂ _w₁ _w₂ p₁ p₂ =>
    Quot.sound <| p₁.bagInter p₂
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inter (Multiset α) := ⟨inter⟩
/-
**Multiset.inter_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multiset α), s ∩ 0 = 0
参数：s : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.bagInter_nil`：bagInter_nil (l : List α) : l.bagInter [] = []
-/
@[simp] lemma inter_zero (s : Multiset α) : s ∩ 0 = 0 :=
  Quot.inductionOn s fun l => congr_arg ofList l.bagInter_nil
/-
**Multiset.zero_inter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multiset α), 0 ∩ s = 0
参数：s : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.nil_bagInter`：nil_bagInter (l : List α) : [].bagInter l = []
-/
@[simp] lemma zero_inter (s : Multiset α) : 0 ∩ s = 0 :=
  Quot.inductionOn s fun l => congr_arg ofList l.nil_bagInter

@[simp]
/-
**Multiset.cons_inter_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：cons_inter_of_pos (s : Multiset α) : a in t -> (a ::ₘ s) inter t = a ::ₘ s
 inter t.erase a
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.cons_bagInter_of_mem`：cons_bagInter_of_mem (l₁ : List α) (h : a in 
l₂) : (a :: l₁).bagInter l₂ = a :: l₁.bagInter (l₂.erase a)
-/
lemma cons_inter_of_pos (s : Multiset α) : a ∈ t → (a ::ₘ s) ∩ t = a ::ₘ s ∩ t.erase a :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList <| cons_bagInter_of_mem _ h

@[simp]
/-
**Multiset.cons_inter_of_neg** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：cons_inter_of_neg (s : Multiset α) : a ∉ t -> (a ::ₘ s) inter t = s inter 
t
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.cons_bagInter_of_not_mem`：cons_bagInter_of_not_mem (l₁ : List α) (h
 : a ∉ l₂) : (a :: l₁).bagInter l₂ = l₁.bagInter l₂
-/
lemma cons_inter_of_neg (s : Multiset α) : a ∉ t → (a ::ₘ s) ∩ t = s ∩ t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ h => congr_arg ofList <| cons_bagInter_of_not_mem _ h
/-
**Multiset.inter_le_left** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：inter_le_left : s inter t <= s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.bagInter_sublist_left`：bagInter_sublist_left {l₁ l₂ : List α} : l₁.
bagInter l₂ <+ l₁
-/
lemma inter_le_left : s ∩ t ≤ s :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => bagInter_sublist_left.subperm
/-
**Multiset.inter_le_right** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：inter_le_right : s inter t <= t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Multiset.zero_le`：zero_le (s : Multiset α) : 0 <= s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.zero_inter`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multis
et α), 0 ∩ s = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.cons_inter_of_pos`：cons_inter_of_pos (s : Multiset α) : a in t 
-> (a ::ₘ s) inter t = a ::ₘ s inter t.erase a
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Multiset.cons_le_cons`：cons_le_cons (a : α) : s <= t -> a ::ₘ s <= a ::ₘ
 t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Multiset.cons_inter_of_neg`：cons_inter_of_neg (s : Multiset α) : a ∉ t -
> (a ::ₘ s) inter t = s inter t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma inter_le_right : s ∩ t ≤ t := by
  induction s using Multiset.induction_on generalizing t with
  | empty => exact (zero_inter t).symm ▸ zero_le _
  | cons a s IH =>
    by_cases h : a ∈ t
    · simpa [h] using cons_le_cons a (IH (t := t.erase a))
    · simp [h, IH]
/-
**Multiset.le_inter** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：le_inter (h₁ : s <= t) (h₂ : s <= u) : s <= t inter u
参数：h₁ : s <= t；h₂ : s <= u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.zero_inter`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multis
et α), 0 ∩ s = 0
· 使用引理 `Multiset.cons_inter_of_pos`：cons_inter_of_pos (s : Multiset α) : a in t 
-> (a ::ₘ s) inter t = a ::ₘ s inter t.erase a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.erase_le_iff_le_cons`：erase_le_iff_le_cons {s t : Multiset α} {
a : α} : s.erase a <= t ↔ s <= a ::ₘ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.erase_le_erase`：erase_le_erase {s t : Multiset α} (a : α) (h : 
s <= t) : s.erase a <= t.erase a
· 使用引理 `Multiset.cons_inter_of_neg`：cons_inter_of_neg (s : Multiset α) : a ∉ t -
> (a ::ₘ s) inter t = s inter t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.le_cons_of_notMem`：le_cons_of_notMem (m : a ∉ s) : s <= a ::ₘ t
 ↔ s <= t
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
-/
lemma le_inter (h₁ : s ≤ t) (h₂ : s ≤ u) : s ≤ t ∩ u := by
  revert s u; refine @(Multiset.induction_on t ?_ fun a t IH => ?_) <;> intro s u h₁ h₂
  · simpa only [zero_inter] using h₁
  by_cases h : a ∈ u
  · rw [cons_inter_of_pos _ h, ← erase_le_iff_le_cons]
    exact IH (erase_le_iff_le_cons.2 h₁) (erase_le_erase _ h₂)
  · rw [cons_inter_of_neg _ h]
    exact IH ((le_cons_of_notMem <| mt (mem_of_le h₂) h).1 h₁) h₂

@[simp]
/-
**Multiset.mem_inter** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：mem_inter : a in s inter t ↔ a in s ∧ a in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用引理 `Multiset.inter_le_left`：inter_le_left : s inter t <= s
· 使用引理 `Multiset.inter_le_right`：inter_le_right : s inter t <= t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用引理 `Multiset.cons_inter_of_pos`：cons_inter_of_pos (s : Multiset α) : a in t 
-> (a ::ₘ s) inter t = a ::ₘ s inter t.erase a
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
-/
lemma mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t :=
  ⟨fun h => ⟨mem_of_le inter_le_left h, mem_of_le inter_le_right h⟩, fun ⟨h₁, h₂⟩ => by
    rw [← cons_erase h₁, cons_inter_of_pos _ h₂]; apply mem_cons_self⟩
/-
**Multiset.instLattice** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：instLattice : Lattice (Multiset α) where sup
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.le_union_left`：le_union_left : s <= s union t
· 使用引理 `Multiset.le_union_right`：le_union_right : t <= s union t
· 使用引理 `Multiset.union_le`：union_le (h₁ : s <= u) (h₂ : t <= u) : s union t <= u
· 使用引理 `Multiset.inter_le_left`：inter_le_left : s inter t <= s
· 使用引理 `Multiset.inter_le_right`：inter_le_right : s inter t <= t
· 使用引理 `Multiset.le_inter`：le_inter (h₁ : s <= t) (h₂ : s <= u) : s <= t inter u
-/
instance instLattice : Lattice (Multiset α) where
  sup := (· ∪ ·)
  sup_le _ _ _ := union_le
  le_sup_left _ _ := le_union_left
  le_sup_right _ _ := le_union_right
  inf := (· ∩ ·)
  le_inf _ _ _ := le_inter
  inf_le_left _ _ := inter_le_left
  inf_le_right _ _ := inter_le_right
/-
**Multiset.sup_eq_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s t : Multiset α), s ⊔ t = s ∪ t
参数：s t : Multiset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma sup_eq_union (s t : Multiset α) : s ⊔ t = s ∪ t := rfl
/-
**Multiset.inf_eq_inter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s t : Multiset α), s ⊓ t = s ∩ t
参数：s t : Multiset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma inf_eq_inter (s t : Multiset α) : s ⊓ t = s ∩ t := rfl
/-
**Multiset.le_inter_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t u : Multiset α}, s ≤ t ∩ u ↔ 
s ≤ t ∧ s ≤ u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
-/
@[simp] lemma le_inter_iff : s ≤ t ∩ u ↔ s ≤ t ∧ s ≤ u := le_inf_iff
/-
**Multiset.union_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t u : Multiset α}, s ∪ t ≤ u ↔ 
s ≤ u ∧ t ≤ u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
-/
@[simp] lemma union_le_iff : s ∪ t ≤ u ↔ s ≤ u ∧ t ≤ u := sup_le_iff
/-
**Multiset.union_comm** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：union_comm (s t : Multiset α) : s union t = t union s
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
lemma union_comm (s t : Multiset α) : s ∪ t = t ∪ s := sup_comm ..
/-
**Multiset.inter_comm** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：inter_comm (s t : Multiset α) : s inter t = t inter s
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
lemma inter_comm (s t : Multiset α) : s ∩ t = t ∩ s := inf_comm ..
/-
**Multiset.eq_union_right** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：eq_union_right (h : s <= t) : s union t = t
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.union_comm`：union_comm (s t : Multiset α) : s union t = t union
 s
· 使用引理 `Multiset.eq_union_left`：eq_union_left : t <= s -> s union t = s
-/
lemma eq_union_right (h : s ≤ t) : s ∪ t = t := by rw [union_comm, eq_union_left h]
/-
**Multiset.union_le_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Multiset α}, s ≤ t → ∀ (u :
 Multiset α), u ∪ s ≤ u ∪ t
参数：u : Multiset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
-/
@[gcongr] lemma union_le_union_left (h : s ≤ t) (u) : u ∪ s ≤ u ∪ t := sup_le_sup_left h _
/-
**Multiset.union_le_add** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：union_le_add (s t : Multiset α) : s union t <= s + t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.union_le`：union_le (h₁ : s <= u) (h₂ : t <= u) : s union t <= u
· 使用引理 `Multiset.le_add_right`：le_add_right (s t : Multiset α) : s <= s + t
· 使用引理 `Multiset.le_add_left`：le_add_left (s t : Multiset α) : s <= t + s
-/
lemma union_le_add (s t : Multiset α) : s ∪ t ≤ s + t := union_le (le_add_right ..) (le_add_left ..)
/-
**Multiset.union_add_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：union_add_distrib (s t u : Multiset α) : s union t + u = s + u union (t + 
u)
参数：s t u : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_assoc`：∀ {α : Type u_1} (s t u : Multiset α), s + t + u = s
 + (t + u)
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用定理 `Multiset.sub_add_eq_sub_sub`：∀ {α : Type u_1} [inst : DecidableEq α] {s 
t u : Multiset α}, s - (t + u) = s - t - u
· 使用定理 `Multiset.add_sub_cancel_right`：∀ {α : Type u_1} [inst : DecidableEq α] {
s t : Multiset α}, s + t - t = s
-/
lemma union_add_distrib (s t u : Multiset α) : s ∪ t + u = s + u ∪ (t + u) := by
  simpa [(· ∪ ·), union, eq_comm, Multiset.add_assoc, Multiset.add_left_inj] using
    show s + u - (t + u) = s - t by
      rw [t.add_comm, Multiset.sub_add_eq_sub_sub, Multiset.add_sub_cancel_right]
/-
**Multiset.add_union_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：add_union_distrib (s t u : Multiset α) : s + (t union u) = s + t union (s 
+ u)
参数：s t u : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用引理 `Multiset.union_add_distrib`：union_add_distrib (s t u : Multiset α) : s u
nion t + u = s + u union (t + u)
-/
lemma add_union_distrib (s t u : Multiset α) : s + (t ∪ u) = s + t ∪ (s + u) := by
  rw [Multiset.add_comm, union_add_distrib, s.add_comm, s.add_comm]
/-
**Multiset.cons_union_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：cons_union_distrib (a : α) (s t : Multiset α) : a ::ₘ (s union t) = a ::ₘ 
s union a ::ₘ t
参数：a : α；s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.add_union_distrib`：add_union_distrib (s t u : Multiset α) : s +
 (t union u) = s + t union (s + u)
-/
lemma cons_union_distrib (a : α) (s t : Multiset α) : a ::ₘ (s ∪ t) = a ::ₘ s ∪ a ::ₘ t := by
  simpa using add_union_distrib (a ::ₘ 0) s t
/-
**Multiset.inter_add_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：inter_add_distrib (s t u : Multiset α) : s inter t + u = (s + u) inter (t 
+ u)
参数：s t u : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.lt_iff_cons_le`：lt_iff_cons_le {s t : Multiset α} : s < t ↔ exi
sts a, a ::ₘ s <= t
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
· 使用引理 `Multiset.le_inter`：le_inter (h₁ : s <= t) (h₂ : s <= u) : s <= t inter u
· 使用定理 `Multiset.add_le_add_right`：∀ {α : Type u_1} {s t u : Multiset α}, s ≤ t 
→ s + u ≤ t + u
· 使用引理 `Multiset.inter_le_left`：inter_le_left : s inter t <= s
· 使用引理 `Multiset.inter_le_right`：inter_le_right : s inter t <= t
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Multiset.lt_cons_self`：lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ
 s
· 使用定理 `Multiset.le_of_add_le_add_right`：∀ {α : Type u_1} {s t u : Multiset α}, 
s + u ≤ t + u → s ≤ t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.cons_add`：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a
 ::ₘ (s + t)
-/
lemma inter_add_distrib (s t u : Multiset α) : s ∩ t + u = (s + u) ∩ (t + u) := by
  by_contra! h
  obtain ⟨a, ha⟩ := lt_iff_cons_le.1 <| h.lt_of_le <| le_inter
    (Multiset.add_le_add_right inter_le_left) (Multiset.add_le_add_right inter_le_right)
  rw [← cons_add] at ha
  exact (lt_cons_self (s ∩ t) a).not_ge <| le_inter
    (Multiset.le_of_add_le_add_right (ha.trans inter_le_left))
    (Multiset.le_of_add_le_add_right (ha.trans inter_le_right))
/-
**Multiset.add_inter_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：add_inter_distrib (s t u : Multiset α) : s + t inter u = (s + t) inter (s 
+ u)
参数：s t u : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用引理 `Multiset.inter_add_distrib`：inter_add_distrib (s t u : Multiset α) : s i
nter t + u = (s + u) inter (t + u)
-/
lemma add_inter_distrib (s t u : Multiset α) : s + t ∩ u = (s + t) ∩ (s + u) := by
  rw [Multiset.add_comm, inter_add_distrib, s.add_comm, s.add_comm]
/-
**Multiset.cons_inter_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：cons_inter_distrib (a : α) (s t : Multiset α) : a ::ₘ s inter t = (a ::ₘ s
) inter (a ::ₘ t)
参数：a : α；s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.cons_inter_of_pos`：cons_inter_of_pos (s : Multiset α) : a in t 
-> (a ::ₘ s) inter t = a ::ₘ s inter t.erase a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Multiset.erase_cons_head`：erase_cons_head (a : α) (s : Multiset α) : (a 
::ₘ s).erase a = s
-/
lemma cons_inter_distrib (a : α) (s t : Multiset α) : a ::ₘ s ∩ t = (a ::ₘ s) ∩ (a ::ₘ t) := by
  simp
/-
**Multiset.union_add_inter** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：union_add_inter (s t : Multiset α) : s union t + s inter t = s + t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.union_add_distrib`：union_add_distrib (s t u : Multiset α) : s u
nion t + u = s + u union (t + u)
· 使用引理 `Multiset.union_le`：union_le (h₁ : s <= u) (h₂ : t <= u) : s union t <= u
· 使用定理 `Multiset.add_le_add_left`：∀ {α : Type u_1} {s t u : Multiset α}, t ≤ u →
 s + t ≤ s + u
· 使用引理 `Multiset.inter_le_right`：inter_le_right : s inter t <= t
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
· 使用定理 `Multiset.add_le_add_right`：∀ {α : Type u_1} {s t u : Multiset α}, s ≤ t 
→ s + u ≤ t + u
· 使用引理 `Multiset.inter_le_left`：inter_le_left : s inter t <= s
· 使用引理 `Multiset.add_inter_distrib`：add_inter_distrib (s t u : Multiset α) : s +
 t inter u = (s + t) inter (s + u)
· 使用引理 `Multiset.le_inter`：le_inter (h₁ : s <= t) (h₂ : s <= u) : s <= t inter u
· 使用引理 `Multiset.le_union_right`：le_union_right : t <= s union t
· 使用引理 `Multiset.le_union_left`：le_union_left : s <= s union t
-/
lemma union_add_inter (s t : Multiset α) : s ∪ t + s ∩ t = s + t := by
  apply _root_.le_antisymm
  · rw [union_add_distrib]
    refine union_le (Multiset.add_le_add_left inter_le_right) ?_
    rw [Multiset.add_comm]
    exact Multiset.add_le_add_right inter_le_left
  · rw [Multiset.add_comm, add_inter_distrib]
    refine le_inter (Multiset.add_le_add_right le_union_right) ?_
    rw [Multiset.add_comm]
    exact Multiset.add_le_add_right le_union_left
/-
**Multiset.sub_add_inter** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：sub_add_inter (s t : Multiset α) : s - t + s inter t = s
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.inter_comm`：inter_comm (s t : Multiset α) : s inter t = t inter
 s
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.sub_zero`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multiset
 α), s - 0 = s
· 使用定理 `Multiset.zero_inter`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multis
et α), 0 ∩ s = 0
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Multiset.cons_inter_of_pos`：cons_inter_of_pos (s : Multiset α) : a in t 
-> (a ::ₘ s) inter t = a ::ₘ s inter t.erase a
· 使用引理 `Multiset.sub_cons`：sub_cons (a : α) (s t : Multiset α) : s - a ::ₘ t = s
.erase a - t
· 使用定理 `Multiset.add_cons`：add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a
 ::ₘ (s + t)
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用引理 `Multiset.cons_inter_of_neg`：cons_inter_of_neg (s : Multiset α) : a ∉ t -
> (a ::ₘ s) inter t = s inter t
· 使用定理 `Multiset.erase_of_notMem`：erase_of_notMem {a : α} {s : Multiset α} : a ∉
 s -> s.erase a = s
-/
lemma sub_add_inter (s t : Multiset α) : s - t + s ∩ t = s := by
  rw [inter_comm]
  revert s; refine Multiset.induction_on t (by simp) fun a t IH s => ?_
  by_cases h : a ∈ s
  · rw [cons_inter_of_pos _ h, sub_cons, add_cons, IH, cons_erase h]
  · rw [cons_inter_of_neg _ h, sub_cons, erase_of_notMem h, IH]
/-
**Multiset.sub_inter** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：sub_inter (s t : Multiset α) : s - s inter t = s - t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.eq_sub_of_add_eq`：∀ {α : Type u_1} [inst : DecidableEq α] {s t 
u : Multiset α}, s + t = u → s = u - t
· 使用引理 `Multiset.sub_add_inter`：sub_add_inter (s t : Multiset α) : s - t + s int
er t = s
-/
lemma sub_inter (s t : Multiset α) : s - s ∩ t = s - t :=
  (Multiset.eq_sub_of_add_eq <| sub_add_inter ..).symm

@[simp]
/-
**Multiset.count_inter** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：count_inter (a : α) (s t : Multiset α) : count a (s inter t) = min (count 
a s) (count a t)
参数：a : α；s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.add_left_cancel`：∀ {n m k : ℕ}, n + m = n + k → m = k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用引理 `Multiset.sub_add_inter`：sub_add_inter (s t : Multiset α) : s - t + s int
er t = s
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `Nat.sub_add_min_cancel`：∀ (n m : ℕ), n - m + min n m = n
-/
lemma count_inter (a : α) (s t : Multiset α) : count a (s ∩ t) = min (count a s) (count a t) := by
  apply @Nat.add_left_cancel (count a (s - t))
  rw [← count_add, sub_add_inter, count_sub, Nat.sub_add_min_cancel]

@[simp]
/-
**Multiset.coe_inter** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：coe_inter (s t : List α) : (s inter t : Multiset α) = (s.bagInter t : List
 α)
参数：s t : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_inter`：count_inter (a : α) (s t : Multiset α) : count a (
s inter t) = min (count a s) (count a t)
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `List.count_bagInter`：count_bagInter {a : α} {l₁ l₂ : List α} : count a (
l₁.bagInter l₂) = min (count a l₁) (count a l₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_inter (s t : List α) : (s ∩ t : Multiset α) = (s.bagInter t : List α) := by ext; simp
/-
**Multiset.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：instDistribLattice : DistribLattice (Multiset α) where le_sup_inf s t u
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribLattice : DistribLattice (Multiset α) where
  le_sup_inf s t u := ge_of_eq <| ext.2 fun a ↦ by
    simp only [max_min_distrib_left, Multiset.count_inter, Multiset.sup_eq_union,
      Multiset.count_union, Multiset.inf_eq_inter]
/-
**Multiset.filter_inter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (p : α → Prop) [inst_1 : Decidable
Pred p] (s t : Multiset α),   Multiset.filter p (s ∩ t) = Multiset.filter p s ∩ 
Multiset.filter p t
参数：p : α → Prop；s t : Multiset α；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Multiset.le_inter`：le_inter (h₁ : s <= t) (h₂ : s <= u) : s <= t inter u
· 使用定理 `Multiset.filter_le_filter`：filter_le_filter {s t} (h : s <= t) : filter 
p s <= filter p t
· 使用引理 `Multiset.inter_le_left`：inter_le_left : s inter t <= s
· 使用引理 `Multiset.inter_le_right`：inter_le_right : s inter t <= t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_filter`：le_filter {s t} : s <= filter p t ↔ s <= t ∧ forall 
a in s, p a
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `Multiset.filter_le`：filter_le (s : Multiset α) : filter p s <= s
· 使用定理 `Multiset.of_mem_filter`：of_mem_filter {a : α} {s} (h : a in filter p s) 
: p a
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
-/
@[simp] lemma filter_inter (p : α → Prop) [DecidablePred p] (s t : Multiset α) :
    filter p (s ∩ t) = filter p s ∩ filter p t :=
  le_antisymm (le_inter (filter_le_filter _ inter_le_left) (filter_le_filter _ inter_le_right)) <|
    le_filter.2 ⟨inf_le_inf (filter_le _ _) (filter_le _ _), fun _a h =>
      of_mem_filter (mem_of_le inter_le_left h)⟩

@[simp]
/-
**Multiset.replicate_inter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：replicate_inter (n : Nat) (x : α) (s : Multiset α) : replicate n x inter s
 = replicate (min n (s.count x)) x
参数：n : Nat；x : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_inter`：count_inter (a : α) (s t : Multiset α) : count a (
s inter t) = min (count a s) (count a t)
· 使用定理 `Multiset.count_replicate`：count_replicate (a b : α) (n : Nat) : count a 
(replicate n b) = if b = a then n else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `Nat.zero_min`：∀ (a : ℕ), min 0 a = 0
-/
theorem replicate_inter (n : ℕ) (x : α) (s : Multiset α) :
    replicate n x ∩ s = replicate (min n (s.count x)) x := by
  ext y
  rw [count_inter, count_replicate, count_replicate]
  by_cases h : x = y
  · simp only [h, if_true]
  · simp only [h, if_false, Nat.zero_min]

@[simp]
/-
**Multiset.inter_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：inter_replicate (s : Multiset α) (n : Nat) (x : α) : s inter replicate n x
 = replicate (min (s.count x) n) x
参数：s : Multiset α；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.inter_comm`：inter_comm (s t : Multiset α) : s inter t = t inter
 s
· 使用定理 `Multiset.replicate_inter`：replicate_inter (n : Nat) (x : α) (s : Multise
t α) : replicate n x inter s = replicate (min n (s.count x)) x
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
-/
theorem inter_replicate (s : Multiset α) (n : ℕ) (x : α) :
    s ∩ replicate n x = replicate (min (s.count x) n) x := by
  rw [inter_comm, replicate_inter, min_comm]

end sub

/-
**Multiset.inter_add_sub_of_add_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：inter_add_sub_of_add_eq_add [DecidableEq α] {M N P Q : Multiset α} (h : M 
+ N = P + Q) : (N inter Q) + (P - M) = N
参数：h : M + N = P + Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用引理 `Multiset.count_inter`：count_inter (a : α) (s t : Multiset α) : count a (
s inter t) = min (count a s) (count a t)
· 使用引理 `Multiset.count_sub`：count_sub (a : α) (s t : Multiset α) : count a (s - 
t) = count a s - count a t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.ext`：ext {s t : Multiset α} : s = t ↔ forall a, count a s = cou
nt a t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
theorem inter_add_sub_of_add_eq_add [DecidableEq α] {M N P Q : Multiset α} (h : M + N = P + Q) :
    (N ∩ Q) + (P - M) = N := by
  ext x
  rw [Multiset.count_add, Multiset.count_inter, Multiset.count_sub]
  have h0 : M.count x + N.count x = P.count x + Q.count x := by
    rw [Multiset.ext] at h
    simp_all only [Multiset.count_add]
  omega

/-! ### Disjoint multisets -/

/-
**Multiset.disjoint_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_left {s t : Multiset α} : Disjoint s t ↔ forall {a}, a in s -> a 
∉ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.singleton_le`：singleton_le {a : α} {s : Multiset α} : {a} <= s 
↔ a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Multiset.bot_eq_zero`：bot_eq_zero : (⊥ : Multiset α) = 0
· 使用定理 `Multiset.eq_zero_iff_forall_notMem`：eq_zero_iff_forall_notMem {s : Multi
set α} : s = 0 ↔ forall a, a ∉ s
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t

--- 原说明 ---
### Disjoint multisets
-/
theorem disjoint_left {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t := by
  refine ⟨fun h a hs ht ↦ ?_, fun h u hs ht ↦ ?_⟩
  · simpa using h (singleton_le.mpr hs) (singleton_le.mpr ht)
  · rw [le_bot_iff, bot_eq_zero, eq_zero_iff_forall_notMem]
    exact fun a ha ↦ h (subset_of_le hs ha) (subset_of_le ht ha)

alias ⟨_root_.Disjoint.notMem_of_mem_left_multiset, _⟩ := disjoint_left

@[simp, norm_cast]
/-
**Multiset.coe_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_disjoint (l₁ l₂ : List α) : Disjoint (l₁ : Multiset α) l₂ ↔ l₁.Disjoin
t l₂
参数：l₁ l₂ : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.disjoint_left`：disjoint_left {s t : Multiset α} : Disjoint s t 
↔ forall {a}, a in s -> a ∉ t
-/
theorem coe_disjoint (l₁ l₂ : List α) : Disjoint (l₁ : Multiset α) l₂ ↔ l₁.Disjoint l₂ :=
  disjoint_left
/-
**Multiset.disjoint_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_right {s t : Multiset α} : Disjoint s t ↔ forall {a}, a in t -> a
 ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Multiset.disjoint_left`：disjoint_left {s t : Multiset α} : Disjoint s t 
↔ forall {a}, a in s -> a ∉ t
-/
theorem disjoint_right {s t : Multiset α} : Disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
  disjoint_comm.trans disjoint_left

alias ⟨_root_.Disjoint.notMem_of_mem_right_multiset, _⟩ := disjoint_right
/-
**Multiset.disjoint_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_iff_ne {s t : Multiset α} : Disjoint s t ↔ forall a in s, forall 
b in t, a != b
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_iff_ne {s t : Multiset α} : Disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b := by
  simp [disjoint_left, imp_not_comm]
/-
**Multiset.disjoint_of_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_of_subset_left {s t u : Multiset α} (h : s subseteq u) (d : Disjo
int u t) : Disjoint s t
参数：h : s subseteq u；d : Disjoint u t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.disjoint_left`：disjoint_left {s t : Multiset α} : Disjoint s t 
↔ forall {a}, a in s -> a ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem disjoint_of_subset_left {s t u : Multiset α} (h : s ⊆ u) (d : Disjoint u t) :
    Disjoint s t :=
  disjoint_left.mpr fun ha ↦ disjoint_left.mp d <| h ha
/-
**Multiset.disjoint_of_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_of_subset_right {s t u : Multiset α} (h : t subseteq u) (d : Disj
oint s u) : Disjoint s t
参数：h : t subseteq u；d : Disjoint s u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Multiset.disjoint_of_subset_left`：disjoint_of_subset_left {s t u : Multi
set α} (h : s subseteq u) (d : Disjoint u t) : Disjoint s t
-/
theorem disjoint_of_subset_right {s t u : Multiset α} (h : t ⊆ u) (d : Disjoint s u) :
    Disjoint s t :=
  (disjoint_of_subset_left h d.symm).symm

@[simp]
/-
**Multiset.zero_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_disjoint (l : Multiset α) : Disjoint 0 l
参数：l : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_bot_left`：disjoint_bot_left : Disjoint ⊥ a
-/
theorem zero_disjoint (l : Multiset α) : Disjoint 0 l := disjoint_bot_left

@[simp]
/-
**Multiset.singleton_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：singleton_disjoint {l : Multiset α} {a : α} : Disjoint {a} l ↔ a ∉ l
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem singleton_disjoint {l : Multiset α} {a : α} : Disjoint {a} l ↔ a ∉ l := by
  simp [disjoint_left]

@[simp]
/-
**Multiset.disjoint_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_singleton {l : Multiset α} {a : α} : Disjoint l {a} ↔ a ∉ l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Multiset.singleton_disjoint`：singleton_disjoint {l : Multiset α} {a : α}
 : Disjoint {a} l ↔ a ∉ l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_singleton {l : Multiset α} {a : α} : Disjoint l {a} ↔ a ∉ l := by
  rw [_root_.disjoint_comm, singleton_disjoint]

@[simp]
/-
**Multiset.disjoint_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_add_left {s t u : Multiset α} : Disjoint (s + t) u ↔ Disjoint s u
 ∧ Disjoint t u
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_add_left {s t u : Multiset α} :
    Disjoint (s + t) u ↔ Disjoint s u ∧ Disjoint t u := by simp [disjoint_left, or_imp, forall_and]

@[simp]
/-
**Multiset.disjoint_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_add_right {s t u : Multiset α} : Disjoint s (t + u) ↔ Disjoint s 
t ∧ Disjoint s u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Multiset.disjoint_add_left`：disjoint_add_left {s t u : Multiset α} : Dis
joint (s + t) u ↔ Disjoint s u ∧ Disjoint t u
-/
theorem disjoint_add_right {s t u : Multiset α} :
    Disjoint s (t + u) ↔ Disjoint s t ∧ Disjoint s u := by
  rw [_root_.disjoint_comm, disjoint_add_left]; tauto

@[simp]
/-
**Multiset.disjoint_cons_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_cons_left {a : α} {s t : Multiset α} : Disjoint (a ::ₘ s) t ↔ a ∉
 t ∧ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.disjoint_add_left`：disjoint_add_left {s t u : Multiset α} : Dis
joint (s + t) u ↔ Disjoint s u ∧ Disjoint t u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.singleton_disjoint`：singleton_disjoint {l : Multiset α} {a : α}
 : Disjoint {a} l ↔ a ∉ l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_cons_left {a : α} {s t : Multiset α} :
    Disjoint (a ::ₘ s) t ↔ a ∉ t ∧ Disjoint s t :=
  (@disjoint_add_left _ {a} s t).trans <| by rw [singleton_disjoint]

@[simp]
/-
**Multiset.disjoint_cons_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_cons_right {a : α} {s t : Multiset α} : Disjoint s (a ::ₘ t) ↔ a 
∉ s ∧ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Multiset.disjoint_cons_left`：disjoint_cons_left {a : α} {s t : Multiset 
α} : Disjoint (a ::ₘ s) t ↔ a ∉ t ∧ Disjoint s t
-/
theorem disjoint_cons_right {a : α} {s t : Multiset α} :
    Disjoint s (a ::ₘ t) ↔ a ∉ s ∧ Disjoint s t := by
  rw [_root_.disjoint_comm, disjoint_cons_left]; tauto
/-
**Multiset.inter_eq_zero_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：inter_eq_zero_iff_disjoint [DecidableEq α] {s t : Multiset α} : s inter t 
= 0 ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.subset_zero`：∀ {α : Type u_1} {s : Multiset α}, s ⊆ 0 ↔ s = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inter_eq_zero_iff_disjoint [DecidableEq α] {s t : Multiset α} :
    s ∩ t = 0 ↔ Disjoint s t := by rw [← subset_zero]; simp [subset_iff, disjoint_left]

@[simp]
/-
**Multiset.disjoint_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_union_left [DecidableEq α] {s t u : Multiset α} : Disjoint (s uni
on t) u ↔ Disjoint s u ∧ Disjoint t u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sup_left`：disjoint_sup_left : Disjoint (a ⊔ b) c ↔ Disjoint a c
 ∧ Disjoint b c
-/
theorem disjoint_union_left [DecidableEq α] {s t u : Multiset α} :
    Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u := disjoint_sup_left

@[simp]
/-
**Multiset.disjoint_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_union_right [DecidableEq α] {s t u : Multiset α} : Disjoint s (t 
union u) ↔ Disjoint s t ∧ Disjoint s u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `disjoint_sup_right`：disjoint_sup_right : Disjoint a (b ⊔ c) ↔ Disjoint a
 b ∧ Disjoint a c
-/
theorem disjoint_union_right [DecidableEq α] {s t u : Multiset α} :
    Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u := disjoint_sup_right
/-
**Multiset.add_eq_union_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：add_eq_union_iff_disjoint [DecidableEq α] {s t : Multiset α} : s + t = s u
nion t ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用引理 `Multiset.count_union`：count_union (a : α) (s t : Multiset α) : count a (
s union t) = max (count a s) (count a t)
· 使用引理 `Multiset.count_inter`：count_inter (a : α) (s t : Multiset α) : count a (
s inter t) = min (count a s) (count a t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem add_eq_union_iff_disjoint [DecidableEq α] {s t : Multiset α} :
    s + t = s ∪ t ↔ Disjoint s t := by
  simp_rw [← inter_eq_zero_iff_disjoint, ext, count_add, count_union, count_inter, count_zero,
    Nat.min_eq_zero_iff, Nat.add_eq_max_iff]
/-
**Multiset.add_eq_union_left_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：add_eq_union_left_of_le [DecidableEq α] {s t u : Multiset α} (h : t <= s) 
: u + s = u union t ↔ Disjoint u s ∧ s = t
参数：h : t <= s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.add_eq_union_iff_disjoint`：add_eq_union_iff_disjoint [Decidable
Eq α] {s t : Multiset α} : s + t = s union t ↔ Disjoint s t
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Multiset.le_of_add_le_add_left`：∀ {α : Type u_1} {s t u : Multiset α}, s
 + t ≤ s + u → t ≤ u
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用引理 `Multiset.union_le_add`：union_le_add (s t : Multiset α) : s union t <= s 
+ t
-/
lemma add_eq_union_left_of_le [DecidableEq α] {s t u : Multiset α} (h : t ≤ s) :
    u + s = u ∪ t ↔ Disjoint u s ∧ s = t := by
  rw [← add_eq_union_iff_disjoint]
  refine ⟨fun h0 ↦ ?_, ?_⟩
  · rw [and_iff_right_of_imp]
    · exact (Multiset.le_of_add_le_add_left <| h0.trans_le <| union_le_add u t).antisymm h
    · rintro rfl
      exact h0
  · rintro ⟨h0, rfl⟩
    exact h0
/-
**Multiset.add_eq_union_right_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：add_eq_union_right_of_le [DecidableEq α] {x y z : Multiset α} (h : z <= y)
 : x + y = x union z ↔ y = z ∧ Disjoint x y
参数：h : z <= y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.add_eq_union_left_of_le`：add_eq_union_left_of_le [DecidableEq α
] {s t u : Multiset α} (h : t <= s) : u + s = u union t ↔ Disjoint u s ∧ s = t
-/
lemma add_eq_union_right_of_le [DecidableEq α] {x y z : Multiset α} (h : z ≤ y) :
    x + y = x ∪ z ↔ y = z ∧ Disjoint x y := by
  simpa only [and_comm] using add_eq_union_left_of_le h
/-
**Multiset.disjoint_map_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_map_map {f : α -> γ} {g : β -> γ} {s : Multiset α} {t : Multiset 
β} : Disjoint (s.map f) (t.map g) ↔ forall a in s, forall b in t, f a != g b
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem disjoint_map_map {f : α → γ} {g : β → γ} {s : Multiset α} {t : Multiset β} :
    Disjoint (s.map f) (t.map g) ↔ ∀ a ∈ s, ∀ b ∈ t, f a ≠ g b := by
  simp [disjoint_iff_ne]
/-
**Multiset.map_set_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_set_pairwise {f : α -> β} {r : β -> β -> Prop} {m : Multiset α} (h : {
 a | a in m }.Pairwise fun a₁ a₂ => r (f a₁) (f a₂)) : { b | b in m.map f }.Pair
wise r
参数：h : { a | a in m }.Pairwise fun a₁ a₂ => r (f a₁) (f a₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem map_set_pairwise {f : α → β} {r : β → β → Prop} {m : Multiset α}
    (h : { a | a ∈ m }.Pairwise fun a₁ a₂ => r (f a₁) (f a₂)) : { b | b ∈ m.map f }.Pairwise r :=
  fun b₁ h₁ b₂ h₂ hn => by
    obtain ⟨⟨a₁, H₁, rfl⟩, a₂, H₂, rfl⟩ := Multiset.mem_map.1 h₁, Multiset.mem_map.1 h₂
    exact h H₁ H₂ (mt (congr_arg f) hn)

section Nodup

variable {s t : Multiset α} {a : α}

/-
**Multiset.nodup_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_add {s t : Multiset α} : Nodup (s + t) ↔ Nodup s ∧ Nodup t ∧ Disjoin
t s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nodup_add {s t : Multiset α} : Nodup (s + t) ↔ Nodup s ∧ Nodup t ∧ Disjoint s t :=
  Quotient.inductionOn₂ s t fun _ _ => by simp [nodup_append, disjoint_iff_ne]
/-
**Multiset.disjoint_of_nodup_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：disjoint_of_nodup_add {s t : Multiset α} (d : Nodup (s + t)) : Disjoint s 
t
参数：d : Nodup (s + t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.nodup_add`：nodup_add {s t : Multiset α} : Nodup (s + t) ↔ Nodup
 s ∧ Nodup t ∧ Disjoint s t
-/
theorem disjoint_of_nodup_add {s t : Multiset α} (d : Nodup (s + t)) : Disjoint s t :=
  (nodup_add.1 d).2.2
/-
**Multiset.Nodup.add_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {s t : Multiset α}, s.Nodup → t.Nodup → ((s + t).Nodup ↔ 
Disjoint s t)
参数：(s + t).Nodup ↔ Disjoint s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Nodup.add_iff (d₁ : Nodup s) (d₂ : Nodup t) : Nodup (s + t) ↔ Disjoint s t := by
  simp [nodup_add, d₁, d₂]
/-
**Multiset.Nodup.inter_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α} [inst : DecidableEq α] (t : Multiset α),
 s.Nodup → (s ∩ t).Nodup
参数：t : Multiset α；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_of_le`：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodu
p t -> Nodup s
· 使用引理 `Multiset.inter_le_left`：inter_le_left : s inter t <= s
-/
lemma Nodup.inter_left [DecidableEq α] (t) : Nodup s → Nodup (s ∩ t) := nodup_of_le inter_le_left
/-
**Multiset.Nodup.inter_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {t : Multiset α} [inst : DecidableEq α] (s : Multiset α),
 t.Nodup → (s ∩ t).Nodup
参数：s : Multiset α；s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_of_le`：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodu
p t -> Nodup s
· 使用引理 `Multiset.inter_le_right`：inter_le_right : s inter t <= t
-/
lemma Nodup.inter_right [DecidableEq α] (s) : Nodup t → Nodup (s ∩ t) := nodup_of_le inter_le_right

@[simp]
/-
**Multiset.nodup_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_union [DecidableEq α] {s t : Multiset α} : Nodup (s union t) ↔ Nodup
 s ∧ Nodup t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_of_le`：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodu
p t -> Nodup s
· 使用引理 `Multiset.le_union_left`：le_union_left : s <= s union t
· 使用引理 `Multiset.le_union_right`：le_union_right : t <= s union t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.nodup_iff_count_le_one`：nodup_iff_count_le_one [DecidableEq α] 
{s : Multiset α} : Nodup s ↔ forall a, count a s <= 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Multiset.count_union`：count_union (a : α) (s t : Multiset α) : count a (
s union t) = max (count a s) (count a t)
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem nodup_union [DecidableEq α] {s t : Multiset α} : Nodup (s ∪ t) ↔ Nodup s ∧ Nodup t :=
  ⟨fun h => ⟨nodup_of_le le_union_left h, nodup_of_le le_union_right h⟩, fun ⟨h₁, h₂⟩ =>
    nodup_iff_count_le_one.2 fun a => by
      rw [count_union]
      exact max_le (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩

end Nodup

end Multiset

