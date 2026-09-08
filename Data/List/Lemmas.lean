/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.List.Basic

/-! # Some lemmas about lists involving sets

Split out from `Data.List.Basic` to reduce its dependencies.
-/

public section

variable {α β γ : Type*}

namespace List

@[simp]
/-
**List.setOfPred_mem_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：setOfPred_mem_eq_empty_iff {l : List α} : { x | x in l } = ∅ ↔ l = []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.eq_nil_iff_forall_not_mem`：∀ {α : Type u_1} {l : List α}, l = [] ↔ 
∀ (a : α), a ∉ l
-/
theorem setOfPred_mem_eq_empty_iff {l : List α} : { x | x ∈ l } = ∅ ↔ l = [] :=
  Set.eq_empty_iff_forall_notMem.trans eq_nil_iff_forall_not_mem.symm

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq_empty_iff := setOfPred_mem_eq_empty_iff
/-
**List.injOn_insertIdx_index_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：injOn_insertIdx_index_of_notMem (l : List α) (x : α) (hx : x ∉ l) : Set.In
jOn (fun k => l.insertIdx k x) { n | n <= l.length }
参数：l : List α；x : α；hx : x ∉ l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.succ_inj`：∀ {a b : ℕ}, a.succ = b.succ ↔ a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem injOn_insertIdx_index_of_notMem (l : List α) (x : α) (hx : x ∉ l) :
    Set.InjOn (fun k => l.insertIdx k x) { n | n ≤ l.length } := by
  intro n hn m hm h
  induction l generalizing n m with
  | nil =>
    simp_all [Set.mem_singleton_iff, Set.ofPred_eq_eq_singleton, length]
  | cons hd tl IH =>
    simp only [length, Set.mem_ofPred_eq] at hn hm
    simp only [mem_cons, not_or] at hx
    cases n <;> cases m
    · rfl
    · simp [hx.left] at h
    · simp [Ne.symm hx.left] at h
    · simp only [insertIdx_succ_cons, cons.injEq, true_and] at h
      rw [Nat.succ_inj]
      refine IH hx.right ?_ ?_ h
      · simpa [Nat.succ_le_succ_iff] using hn
      · simpa [Nat.succ_le_succ_iff] using hm
/-
**List.foldr_range_subset_of_range_subset** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldr_range_subset_of_range_subset {f : β -> α -> α} {g : γ -> α -> α} (hf
g : Set.range f subseteq Set.range g) (a : α) : Set.range (foldr f a) subseteq S
et.range (foldr g a)
参数：hfg : Set.range f subseteq Set.range g；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldr_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : α
 → β → β} {b : β},   List.foldr f b (a :: l) = f a (List.foldr f b l)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem foldr_range_subset_of_range_subset {f : β → α → α} {g : γ → α → α}
    (hfg : Set.range f ⊆ Set.range g) (a : α) : Set.range (foldr f a) ⊆ Set.range (foldr g a) := by
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons b l H =>
    obtain ⟨c, hgf⟩ := hfg (Set.mem_range_self b)
    obtain ⟨m, hgf'⟩ := H
    rw [foldr_cons, ← hgf, ← hgf']
    exact ⟨c :: m, rfl⟩
/-
**List.foldl_range_subset_of_range_subset** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_range_subset_of_range_subset {f : α -> β -> α} {g : α -> γ -> α} (hf
g : (Set.range fun a c => f c a) subseteq Set.range fun b c => g c b) (a : α) : 
Set.range (foldl f a) subseteq Set.range (foldl g a)
参数：hfg : (Set.range fun a c => f c a) subseteq Set.range fun b c => g c b；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.foldr_reverse`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {f : α 
→ β → β} {b : β},   List.foldr f b l.reverse = List.foldl (fun x y => f y x) b l
· 使用定理 `Set.range_comp'`：range_comp' (g : α -> β) (f : ι -> α) : range (fun x =>
 g (f x)) = g '' range f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用定理 `List.reverse_involutive`：reverse_involutive : Involutive (@reverse α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `List.foldr_range_subset_of_range_subset`：foldr_range_subset_of_range_sub
set {f : β -> α -> α} {g : γ -> α -> α} (hfg : Set.range f subseteq Set.range g)
 (a : α) : Set.range (foldr f…
-/
theorem foldl_range_subset_of_range_subset {f : α → β → α} {g : α → γ → α}
    (hfg : (Set.range fun a c => f c a) ⊆ Set.range fun b c => g c b) (a : α) :
    Set.range (foldl f a) ⊆ Set.range (foldl g a) := by
  change (Set.range fun l => _) ⊆ Set.range fun l => _
  -- Porting note: have to write `(foldr_reverse)` instead of `foldr_reverse`.
  simp_rw [← (foldr_reverse), Set.range_comp' _ reverse,
    reverse_involutive.bijective.surjective.range_eq, Set.image_univ]
  exact foldr_range_subset_of_range_subset hfg a
/-
**List.foldr_range_eq_of_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldr_range_eq_of_range_eq {f : β -> α -> α} {g : γ -> α -> α} (hfg : Set.
range f = Set.range g) (a : α) : Set.range (foldr f a) = Set.range (foldr g a)
参数：hfg : Set.range f = Set.range g；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `List.foldr_range_subset_of_range_subset`：foldr_range_subset_of_range_sub
set {f : β -> α -> α} {g : γ -> α -> α} (hfg : Set.range f subseteq Set.range g)
 (a : α) : Set.range (foldr f…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem foldr_range_eq_of_range_eq {f : β → α → α} {g : γ → α → α} (hfg : Set.range f = Set.range g)
    (a : α) : Set.range (foldr f a) = Set.range (foldr g a) :=
  (foldr_range_subset_of_range_subset hfg.le a).antisymm
    (foldr_range_subset_of_range_subset hfg.ge a)
/-
**List.foldl_range_eq_of_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_range_eq_of_range_eq {f : α -> β -> α} {g : α -> γ -> α} (hfg : (Set
.range fun a c => f c a) = Set.range fun b c => g c b) (a : α) : Set.range (fold
l f a) = Set.range (foldl g a)
参数：hfg : (Set.range fun a c => f c a) = Set.range fun b c => g c b；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `List.foldl_range_subset_of_range_subset`：foldl_range_subset_of_range_sub
set {f : α -> β -> α} {g : α -> γ -> α} (hfg : (Set.range fun a c => f c a) subs
eteq Set.range fun b c => g c…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
theorem foldl_range_eq_of_range_eq {f : α → β → α} {g : α → γ → α}
    (hfg : (Set.range fun a c => f c a) = Set.range fun b c => g c b) (a : α) :
    Set.range (foldl f a) = Set.range (foldl g a) :=
  (foldl_range_subset_of_range_subset hfg.le a).antisymm
    (foldl_range_subset_of_range_subset hfg.ge a)



/-!
  ### MapAccumr and Foldr
  Some lemmas relation `mapAccumr` and `foldr`
-/
section MapAccumr

/-
**List.mapAccumr_eq_foldr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mapAccumr_eq_foldr {σ : Type*} (f : α -> σ -> σ × β) : forall (as : List α
) (s : σ), mapAccumr f as s = List.foldr (fun a s => let r
参数：f : α -> σ -> σ × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr_eq_foldr {σ : Type*} (f : α → σ → σ × β) : ∀ (as : List α) (s : σ),
    mapAccumr f as s = List.foldr (fun a s =>
                                    let r := f a s.1
                                    (r.1, r.2 :: s.2)) (s, []) as
  | [], _ => rfl
  | a :: as, s => by
    simp only [mapAccumr, foldr, mapAccumr_eq_foldr f as]
/-
**List.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：mapAccumr (f : α -> γ -> γ × β) : List α -> γ -> γ × List β | [], c => (c,
 []) | y :: yr, c => let r
参数：f : α -> γ -> γ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapAccumr₂_eq_foldr {σ φ : Type*} (f : α → β → σ → σ × φ) :
    ∀ (as : List α) (bs : List β) (s : σ),
    mapAccumr₂ f as bs s = foldr (fun ab s =>
                              let r := f ab.1 ab.2 s.1
                              (r.1, r.2 :: s.2)) (s, []) (as.zip bs)
  | [], [], _ => rfl
  | _ :: _, [], _ => rfl
  | [], _ :: _, _ => rfl
  | a :: as, b :: bs, s => by
    simp only [mapAccumr₂, mapAccumr₂_eq_foldr f as]
    rfl

end MapAccumr

end List

