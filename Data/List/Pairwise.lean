/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Data.List.Pairwise
public import Mathlib.Logic.Pairwise
public import Mathlib.Logic.Relation
public import Batteries.Data.List.Lemmas

/-!
# Pairwise relations on a list

This file provides basic results about `List.Pairwise` and `List.pwFilter` (definitions are in
`Data.List.Defs`).
`Pairwise R [a 0, ..., a (n - 1)]` means `∀ i j, i < j → R (a i) (a j)`. For example,
`Pairwise (≠) l` means that all elements of `l` are distinct, and `Pairwise (<) l` means that `l`
is strictly increasing.
`pwFilter R l` is the list obtained by iteratively adding each element of `l` that doesn't break
the pairwiseness of the list we have so far. It thus yields `l'` a maximal sublist of `l` such that
`Pairwise R l'`.

## Tags

sorted, nodup
-/

public section


open Nat Function

namespace List

variable {α β : Type*} {R : α → α → Prop} {l : List α} {a : α}

mk_iff_of_inductive_prop List.Pairwise List.pairwise_iff

/-! ### Pairwise -/

/-
**List.pairwise_iff_forall_infix** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwise_iff_forall_infix {α : Type*} {l : List α} {R : α -> α -> Prop} : 
l.Pairwise R ↔ forall l', (h : 1 < l'.length) -> l' <:+: l -> R (l'.head <| by g
rind) (l'.getLast <| by grind)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.pairwise_iff_getElem`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α},   List.Pairwise R l ↔ ∀ (i j : ℕ) (_hi : i < l.length) (_hj : j < l.length)
, i < j → R l[i…

--- 原说明 ---
### Pairwise
-/
theorem pairwise_iff_forall_infix {α : Type*} {l : List α} {R : α → α → Prop} :
    l.Pairwise R ↔
      ∀ l', (h : 1 < l'.length) → l' <:+: l → R (l'.head <| by grind) (l'.getLast <| by grind) := by
  refine l.pairwise_iff_getElem.trans ⟨fun h l' hne ⟨l₁, l₂, hl⟩ ↦ ?_, fun h i j hi hj hij ↦ ?_⟩
  · grind [getElem_append_left', getElem_append_right']
  · grind [h _ _ <| List.drop_suffix i _ |>.isInfix.trans <| l.take_prefix (j + 1) |>.isInfix]
/-
**List.Pairwise.forall_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} [Std.Symm R],   (∀ x ∈ l,
 R x x) → List.Pairwise R l → ∀ ⦃x : α⦄, x ∈ l → ∀ ⦃y : α⦄, y ∈ l → R x y
参数：∀ x ∈ l, R x x。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.forall_of_forall_of_flip`：∀ {α : Type u_1} {l : List α} {R
 : α → α → Prop},   (∀ x ∈ l, R x x) → List.Pairwise R l → List.Pairwise (flip R
) l → ∀ ⦃x : α⦄, x ∈ l → ∀ ⦃…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Std.Symm.flip_eq`：Std.Symm.flip_eq [Std.Symm r] : flip r = r
-/
theorem Pairwise.forall_of_forall [Std.Symm R] (H₁ : ∀ x ∈ l, R x x) (H₂ : l.Pairwise R) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → R x y :=
  H₂.forall_of_forall_of_flip H₁ <| by rwa [Std.Symm.flip_eq]
/-
**List.Pairwise.forall** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} [Std.Symm R],   List.Pair
wise R l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, b ∈ l → a ≠ b → R a b
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `List.Pairwise.forall_of_forall`：∀ {α : Type u_1} {R : α → α → Prop} {l :
 List α} [Std.Symm R],   (∀ x ∈ l, R x x) → List.Pairwise R l → ∀ ⦃x : α⦄, x ∈ l
 → ∀ ⦃y : α⦄, y ∈ l …
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
-/
theorem Pairwise.forall [Std.Symm R] (hl : l.Pairwise R) :
    ∀ ⦃a⦄, a ∈ l → ∀ ⦃b⦄, b ∈ l → a ≠ b → R a b := by
  have : Std.Symm fun x y ↦ x ≠ y → R x y := { symm a b h hne := symm <| h hne.symm }
  apply Pairwise.forall_of_forall
  · exact fun _ _ ↦ absurd rfl
  · exact hl.imp @fun a b h _ ↦ by exact h
/-
**List.Pairwise.set_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, List.Pairwise R l → ∀ [S
td.Symm R], {x | x ∈ l}.Pairwise R
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.forall`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} [
Std.Symm R],   List.Pairwise R l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, b ∈ l → a ≠ b →
 R a b
-/
theorem Pairwise.set_pairwise (hl : Pairwise R l) [Std.Symm R] : { x | x ∈ l }.Pairwise R :=
  hl.forall
/-
**List.pairwise_of_reflexive_of_forall_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwise_of_reflexive_of_forall_ne [Std.Refl R] (h : forall a in l, forall
 b in l, a != b -> R a b) : l.Pairwise R
参数：h : forall a in l, forall b in l, a != b -> R a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.pairwise_iff_forall_sublist`：∀ {α : Type u_1} {l : List α} {R : α →
 α → Prop}, List.Pairwise R l ↔ ∀ {a b : α}, [a, b].Sublist l → R a b
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem pairwise_of_reflexive_of_forall_ne [Std.Refl R] (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b) :
    l.Pairwise R := by
  rw [pairwise_iff_forall_sublist]
  intro a b hab
  if heq : a = b then
    cases heq; apply refl
  else
    apply h <;> try (apply hab.subset; simp)
    exact heq
/-
**List.Pairwise.rel_head_tail** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} {a : α}, List.Pairwise R 
l → ∀ (ha : a ∈ l.tail), R (l.head ⋯) a
参数：ha : a ∈ l.tail；l.head ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pairwise.rel_head_tail (h₁ : l.Pairwise R) (ha : a ∈ l.tail) :
    R (l.head <| ne_nil_of_mem <| mem_of_mem_tail ha) a := by
  grind +splitIndPred
/-
**List.Pairwise.rel_head_of_rel_head_head** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwi
se`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} {a : α},   List.Pairwise 
R l → ∀ (ha : a ∈ l), R (l.head ⋯) (l.head ⋯) → R (l.head ⋯) a
参数：ha : a ∈ l；l.head ⋯；l.head ⋯；l.head ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
-/
theorem Pairwise.rel_head_of_rel_head_head (h₁ : l.Pairwise R) (ha : a ∈ l)
    (hhead : R (l.head <| ne_nil_of_mem ha) (l.head <| ne_nil_of_mem ha)) :
    R (l.head <| ne_nil_of_mem ha) a := by
  grind +splitIndPred
/-
**List.Pairwise.rel_head** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} {a : α} [Std.Refl R],   L
ist.Pairwise R l → ∀ (ha : a ∈ l), R (l.head ⋯) a
参数：ha : a ∈ l；l.head ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.rel_head_of_rel_head_head`：∀ {α : Type u_1} {R : α → α → P
rop} {l : List α} {a : α},   List.Pairwise R l → ∀ (ha : a ∈ l), R (l.head ⋯) (l
.head ⋯) → R (l.head ⋯) a
· 使用定理 `refl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
-/
theorem Pairwise.rel_head [Std.Refl R] (h₁ : l.Pairwise R) (ha : a ∈ l) :
    R (l.head <| ne_nil_of_mem ha) a :=
  h₁.rel_head_of_rel_head_head ha (refl_of ..)
/-
**List.Pairwise.rel_dropLast_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} {a : α}, List.Pairwise R 
l → ∀ (ha : a ∈ l.dropLast), R a (l.getLast ⋯)
参数：ha : a ∈ l.dropLast；l.getLast ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `List.dropLast_subset`：∀ {α : Type u_1} (l : List α), l.dropLast ⊆ l
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getLast_eq_head_reverse`：∀ {α : Type u_1} {l : List α} (h : l ≠ [])
, l.getLast h = l.reverse.head ⋯
· 使用定理 `List.Pairwise.rel_head_tail`：∀ {α : Type u_1} {R : α → α → Prop} {l : Li
st α} {a : α}, List.Pairwise R l → ∀ (ha : a ∈ l.tail), R (l.head ⋯) a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.pairwise_reverse`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
 List.Pairwise R l.reverse ↔ List.Pairwise (fun a b => R b a) l
· 使用定理 `List.tail_reverse`：∀ {α : Type u_1} {l : List α}, l.reverse.tail = l.dro
pLast.reverse
· 使用定理 `List.mem_reverse`：∀ {α : Type u_1} {x : α} {as : List α}, x ∈ as.reverse
 ↔ x ∈ as
-/
theorem Pairwise.rel_dropLast_getLast (h : l.Pairwise R) (ha : a ∈ l.dropLast) :
    R a (l.getLast <| ne_nil_of_mem <| dropLast_subset _ ha) := by
  rw [← pairwise_reverse] at h
  rw [getLast_eq_head_reverse]
  exact h.rel_head_tail (by rwa [tail_reverse, mem_reverse])
/-
**List.Pairwise.rel_getLast_of_rel_getLast_getLast** 是 Mathlib 中的一个定理，位于命名空间 `Li
st.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} {a : α},   List.Pairwise 
R l → ∀ (ha : a ∈ l), R (l.getLast ⋯) (l.getLast ⋯) → R a (l.getLast ⋯)
参数：ha : a ∈ l；l.getLast ⋯；l.getLast ⋯；l.getLast ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_singleton`：∀ {α : Type u_1} {a b : α}, a ∈ [b] ↔ a = b
· 使用定理 `List.mem_append`：∀ {α : Type u_1} {a : α} {s t : List α}, a ∈ s ++ t ↔ a
 ∈ s ∨ a ∈ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.dropLast_concat_getLast`：∀ {α : Type u_1} {l : List α} (h : l ≠ [])
, l.dropLast ++ [l.getLast h] = l
· 使用定理 `List.Pairwise.rel_dropLast_getLast`：∀ {α : Type u_1} {R : α → α → Prop} 
{l : List α} {a : α}, List.Pairwise R l → ∀ (ha : a ∈ l.dropLast), R a (l.getLas
t ⋯)
-/
theorem Pairwise.rel_getLast_of_rel_getLast_getLast (h₁ : l.Pairwise R) (ha : a ∈ l)
    (hlast : R (l.getLast <| ne_nil_of_mem ha) (l.getLast <| ne_nil_of_mem ha)) :
    R a (l.getLast <| ne_nil_of_mem ha) := by
  rw [← dropLast_concat_getLast (ne_nil_of_mem ha), mem_append, List.mem_singleton] at ha
  exact ha.elim h₁.rel_dropLast_getLast (· ▸ hlast)
/-
**List.Pairwise.rel_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} {a : α} [Std.Refl R],   L
ist.Pairwise R l → ∀ (ha : a ∈ l), R a (l.getLast ⋯)
参数：ha : a ∈ l；l.getLast ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.rel_getLast_of_rel_getLast_getLast`：∀ {α : Type u_1} {R : 
α → α → Prop} {l : List α} {a : α},   List.Pairwise R l → ∀ (ha : a ∈ l), R (l.g
etLast ⋯) (l.getLast ⋯) → R a (l.getLa…
· 使用定理 `refl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
-/
theorem Pairwise.rel_getLast [Std.Refl R] (h₁ : l.Pairwise R) (ha : a ∈ l) :
    R a (l.getLast <| ne_nil_of_mem ha) :=
  h₁.rel_getLast_of_rel_getLast_getLast ha (refl_of ..)

protected alias ⟨Pairwise.of_reverse, Pairwise.reverse⟩ := pairwise_reverse
/-
**List.Pairwise.head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pairwise.head!_le [Inhabited α] [Std.Refl R] (h : l.Pairwise R)
    (ha : a ∈ l) : R l.head! a := by
  cases l
  · contradiction
  · cases ha with
    | head => exact refl_of ..
    | tail => exact rel_of_pairwise_cons h (by assumption)
/-
**List.pairwise_replicate_of_refl** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwise_replicate_of_refl {n} [Std.Refl R] : (replicate n a).Pairwise R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.pairwise_replicate`：∀ {α : Type u_1} {R : α → α → Prop} {n : ℕ} {a 
: α}, List.Pairwise R (List.replicate n a) ↔ n ≤ 1 ∨ R a a
· 使用定理 `refl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Refl r] (a : α), r a a
-/
theorem pairwise_replicate_of_refl {n} [Std.Refl R] : (replicate n a).Pairwise R :=
  pairwise_replicate.mpr (Or.inr <| refl_of ..)

/-! ### Pairwise filtering -/

protected alias ⟨_, Pairwise.pwFilter⟩ := pwFilter_eq_self

/-
**List.pairwise_cons_cons_iff_of_trans** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwise_cons_cons_iff_of_trans [IsTrans α R] {l : List α} {a b : α} : Pai
rwise R (a :: b :: l) ↔ R a b ∧ Pairwise R (b :: l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_cons_cons_iff_of_trans [IsTrans α R] {l : List α} {a b : α} :
    Pairwise R (a :: b :: l) ↔ R a b ∧ Pairwise R (b :: l) := by
  simp_rw [← isChain_iff_pairwise, isChain_cons_cons]
/-
**List.Pairwise.cons_cons_of_trans** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} [IsTrans α R] {l : List α} {a b : α}, 
  R a b → List.Pairwise R (b :: l) → List.Pairwise R (a :: b :: l)
参数：b :: l；a :: b :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem Pairwise.cons_cons_of_trans [IsTrans α R] {l : List α} {a b : α} :
    R a b → Pairwise R (b :: l) → Pairwise R (a :: b :: l) := by
  simp_rw [pairwise_cons_cons_iff_of_trans]
  exact And.intro
/-
**List.Pairwise.rel_get_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},   List.Pairwise R l → ∀ 
{a b : Fin l.length}, a < b → R (l.get a) (l.get b)
参数：l.get a；l.get b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_iff_get`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
   List.Pairwise R l ↔ ∀ (i j : Fin l.length), i < j → R (l.get i) (l.get j)
-/
theorem Pairwise.rel_get_of_lt {l : List α} (h : l.Pairwise R) {a b : Fin l.length} (hab : a < b) :
    R (l.get a) (l.get b) :=
  List.pairwise_iff_get.1 h _ _ hab
/-
**List.Pairwise.rel_get_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} [Std.Refl R] {l : List α},   List.Pair
wise R l → ∀ {a b : Fin l.length}, a ≤ b → R (l.get a) (l.get b)
参数：l.get a；l.get b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.eq_or_lt_of_le`：∀ {n : ℕ} {a b : Fin n}, a ≤ b → a = b ∨ a < b
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_iff_get`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
   List.Pairwise R l ↔ ∀ (i j : Fin l.length), i < j → R (l.get i) (l.get j)
-/
theorem Pairwise.rel_get_of_le [Std.Refl R] {l : List α} (h : l.Pairwise R) {a b : Fin l.length}
    (hab : a ≤ b) : R (l.get a) (l.get b) := by
  obtain rfl | hlt := Fin.eq_or_lt_of_le hab; exacts [refl _, (pairwise_iff_get.1 h) _ _ hlt]
/-
**List.Pairwise.decide** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} [inst : DecidableRel R] (l : List α), 
  List.Pairwise R l → List.Pairwise (fun a b => decide (R a b) = true) l
参数：l : List α；fun a b => decide (R a b) = true。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
-/
theorem Pairwise.decide [DecidableRel R] (l : List α) (h : Pairwise R l) :
    Pairwise (fun a b => decide (R a b) = true) l := by
  refine h.imp fun {a b} h => by simpa using h

end List

