/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Intervals `Ixx (f x) (f (Order.succ x))`

In this file we prove

* `Monotone.biUnion_Ico_Ioc_map_succ`: if `α` is a linear archimedean succ order and `β` is a linear
  order, then for any monotone function `f` and `m n : α`, the union of intervals
  `Set.Ioc (f i) (f (Order.succ i))`, `m ≤ i < n`, is equal to `Set.Ioc (f m) (f n)`;

* `Monotone.pairwise_disjoint_on_Ioc_succ`: if `α` is a linear succ order, `β` is a preorder, and
  `f : α → β` is a monotone function, then the intervals `Set.Ioc (f n) (f (Order.succ n))` are
  pairwise disjoint.

For the latter lemma, we also prove various order dual versions.
-/

public section


open Set Order

variable {α β : Type*} [LinearOrder α]

/-- Union formula for `Set.Ico (f i) (f (Order.succ i))` over `i ∈ Ici a`. See also
`iUnion_Ico_map_succ_eq_Ici` for the specialization `a = ⊥`. -/
/-
**biUnion_Ici_Ico_map_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biUnion_Ici_Ico_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder 
β] {f : α -> β} {a : α} (hf : forall i in Ici a, f a <= f i) (h2f : ¬BddAbove (f
 '' Ici a)) : ⋃ i in Ici a, Ico (f i) (f (succ i)) = Ici (f a)
参数：hf : forall i in Ici a, f a <= f i；h2f : ¬BddAbove (f '' Ici a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ico_subset_Ico_left`：Ico_subset_Ico_left (h : a₁ <= a₂) : Ico a₂ b s
ubseteq Ico a₁ b
· 使用定理 `Set.Ico_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Ici b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Succ.rec`：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_
rfl) (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Union formula for `Set.Ico (f i) (f (Order.succ i))` over `i ∈ Ici a`. See also
`iUnion_Ico_map_succ_eq_Ici` for the specialization `a = ⊥`.
-/
theorem biUnion_Ici_Ico_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α → β}
    {a : α} (hf : ∀ i ∈ Ici a, f a ≤ f i) (h2f : ¬BddAbove (f '' Ici a)) :
    ⋃ i ∈ Ici a, Ico (f i) (f (succ i)) = Ici (f a) := by
  apply subset_antisymm <|
    iUnion₂_subset fun i hi ↦ Ico_subset_Ico_left (hf i hi) |>.trans Ico_subset_Ici_self
  intro b hb
  contrapose h2f
  use b
  simp only [upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact Succ.rec (P := fun i _ ↦ f i ≤ b) hb (by simp_all)

/-- Union formula for `Set.Ioc (f i) (f (Order.succ i))` over `i ∈ Ici a`. See also
`iUnion_Ioc_map_succ_eq_Ioi` for the specialization `a = ⊥`. -/
/-
**biUnion_Ici_Ioc_map_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biUnion_Ici_Ioc_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder 
β] {f : α -> β} {a : α} (hf : forall i in Ici a, f a <= f i) (h2f : ¬BddAbove (f
 '' Ici a)) : ⋃ i in Ici a, Ioc (f i) (f (succ i)) = Ioi (f a)
参数：hf : forall i in Ici a, f a <= f i；h2f : ¬BddAbove (f '' Ici a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioc_subset_Ioc_left`：Ioc_subset_Ioc_left (h : a₁ <= a₂) : Ioc a₂ b s
ubseteq Ioc a₁ b
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Succ.rec`：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_
rfl) (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Union formula for `Set.Ioc (f i) (f (Order.succ i))` over `i ∈ Ici a`. See also
`iUnion_Ioc_map_succ_eq_Ioi` for the specialization `a = ⊥`.
-/
theorem biUnion_Ici_Ioc_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α → β}
    {a : α} (hf : ∀ i ∈ Ici a, f a ≤ f i) (h2f : ¬BddAbove (f '' Ici a)) :
    ⋃ i ∈ Ici a, Ioc (f i) (f (succ i)) = Ioi (f a) := by
  apply subset_antisymm <|
    iUnion₂_subset fun i hi ↦ Ioc_subset_Ioc_left (hf i hi) |>.trans Ioc_subset_Ioi_self
  intro b hb
  contrapose h2f
  suffices ∀ i, a ≤ i → f i < b from ⟨b, by aesop (add simp [upperBounds, le_of_lt])⟩
  exact Succ.rec (P := fun i _ ↦ f i < b) hb (by simp_all)

/-- Special case `a = ⊥` of `biUnion_Ici_Ico_map_succ`. -/
/-
**iUnion_Ico_map_succ_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ico_map_succ_eq_Ici [OrderBot α] [SuccOrder α] [IsSuccArchimedean α
] [LinearOrder β] {f : α -> β} (hf : forall a, f ⊥ <= f a) (h2f : ¬BddAbove (ran
ge f)) : (⋃ a : α, Ico (f a) (f (succ a))) = Ici (f ⊥)
参数：hf : forall a, f ⊥ <= f a；h2f : ¬BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.Ici_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α],
 Set.Ici ⊥ = Set.univ
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `biUnion_Ici_Ico_map_succ`：biUnion_Ici_Ico_map_succ [SuccOrder α] [IsSucc
Archimedean α] [LinearOrder β] {f : α -> β} {a : α} (hf : forall i in Ici a, f a
 <= f i) (h2f …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f

--- 原说明 ---
Special case `a = ⊥` of `biUnion_Ici_Ico_map_succ`.
-/
theorem iUnion_Ico_map_succ_eq_Ici [OrderBot α] [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β]
    {f : α → β} (hf : ∀ a, f ⊥ ≤ f a) (h2f : ¬BddAbove (range f)) :
    (⋃ a : α, Ico (f a) (f (succ a))) = Ici (f ⊥) := by
  simpa using biUnion_Ici_Ico_map_succ (f := f) (a := ⊥) (by simpa) (by simpa)

/-- Special case `a = ⊥` of `biUnion_Ici_Ioc_map_succ`. -/
/-
**iUnion_Ioc_map_succ_eq_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ioc_map_succ_eq_Ioi [OrderBot α] [SuccOrder α] [IsSuccArchimedean α
] [LinearOrder β] {f : α -> β} (hf : forall a, f ⊥ <= f a) (h2f : ¬BddAbove (ran
ge f)) : (⋃ a : α, Ioc (f a) (f (succ a))) = Ioi (f ⊥)
参数：hf : forall a, f ⊥ <= f a；h2f : ¬BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.Ici_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α],
 Set.Ici ⊥ = Set.univ
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `biUnion_Ici_Ioc_map_succ`：biUnion_Ici_Ioc_map_succ [SuccOrder α] [IsSucc
Archimedean α] [LinearOrder β] {f : α -> β} {a : α} (hf : forall i in Ici a, f a
 <= f i) (h2f …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f

--- 原说明 ---
Special case `a = ⊥` of `biUnion_Ici_Ioc_map_succ`.
-/
theorem iUnion_Ioc_map_succ_eq_Ioi [OrderBot α] [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β]
    {f : α → β} (hf : ∀ a, f ⊥ ≤ f a) (h2f : ¬BddAbove (range f)) :
    (⋃ a : α, Ioc (f a) (f (succ a))) = Ioi (f ⊥) := by
  simpa using biUnion_Ici_Ioc_map_succ (f := f) (a := ⊥) (by simpa) (by simpa)

namespace Monotone

/-- If `α` is a linear archimedean succ order and `β` is a linear order, then for any monotone
function `f` and `m n : α`, the union of intervals `Set.Ioc (f i) (f (Order.succ i))`, `m ≤ i < n`,
is equal to `Set.Ioc (f m) (f n)` -/
/-
**Monotone.biUnion_Ico_Ioc_map_succ** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：biUnion_Ico_Ioc_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder 
β] {f : α -> β} (hf : Monotone f) (m n : α) : ⋃ i in Ico m n, Ioc (f i) (f (succ
 i)) = Ioc (f m) (f n)
参数：hf : Monotone f；m n : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `Set.Ioc_eq_empty_of_le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, 
a ≤ b → Set.Ioc b a = ∅
· 使用定理 `Set.biUnion_empty`：biUnion_empty (s : α -> Set β) : ⋃ x in (∅ : Set α), 
s x = ∅
· 使用定理 `Succ.rec`：Succ.rec {m : α} {P : forall n, m <= n -> Prop} (rfl : P m le_
rfl) (succ : forall n (hmn : m <= n), P n hmn -> P (succ n) (hmn.trans <| le_s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioc_union_Ioc_eq_Ioc`：Ioc_union_Ioc_eq_Ioc (h₁ : a <= b) (h₂ : b <= 
c) : Ioc a b union Ioc b c = Ioc a c
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `IsMax.succ_eq`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : SuccOr
der α] {a : α}, IsMax a → Order.succ a = a
· 使用定理 `Set.Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] (a : α), Set.Ioc a a 
= ∅
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `Order.Ico_succ_right_eq_insert_of_not_isMax`：Ico_succ_right_eq_insert_of
_not_isMax (h₁ : a <= b) (h₂ : ¬IsMax b) : Ico a (succ b) = insert b (Ico a b)
· 使用定理 `Set.biUnion_insert`：biUnion_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋃ x in insert a s, t x = t a union ⋃ x in s, t x

--- 原说明 ---
If `α` is a linear archimedean succ order and `β` is a linear order, then for an
y monotone
function `f` and `m n : α`, the union of intervals `Set.Ioc (f i) (f (Order.succ
 i))`, `m ≤ i < n`,
is equal to `Set.Ioc (f m) (f n)`
-/
theorem biUnion_Ico_Ioc_map_succ [SuccOrder α] [IsSuccArchimedean α] [LinearOrder β] {f : α → β}
    (hf : Monotone f) (m n : α) : ⋃ i ∈ Ico m n, Ioc (f i) (f (succ i)) = Ioc (f m) (f n) := by
  rcases le_total n m with hnm | hmn
  · rw [Ico_eq_empty_of_le hnm, Ioc_eq_empty_of_le (hf hnm), biUnion_empty]
  · refine Succ.rec ?_ ?_ hmn
    · simp
    · intro k hmk ihk
      rw [← Ioc_union_Ioc_eq_Ioc (hf hmk) (hf <| le_succ _), union_comm, ← ihk]
      by_cases hk : IsMax k
      · rw [hk.succ_eq, Ioc_self, empty_union]
      · rw [Ico_succ_right_eq_insert_of_not_isMax hmk hk, biUnion_insert]

open scoped Function -- required for scoped `on` notation

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ioc (f n) (f (Order.succ n))` are pairwise disjoint. -/
/-
**Monotone.pairwise_disjoint_on_Ioc_succ** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：pairwise_disjoint_on_Ioc_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf 
: Monotone f) : Pairwise (Disjoint on fun n => Ioc (f n) (f (succ n)))
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pairwise_disjoint_on`：pairwise_disjoint_on [PartialOrder α] [OrderBot α]
 [LinearOrder ι] (f : ι -> α) : Pairwise (Disjoint on f) ↔ forall ⦃m n⦄, m < n -
> Disjoint…
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b

--- 原说明 ---
If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone 
function, then
the intervals `Set.Ioc (f n) (f (Order.succ n))` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ioc_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioc (f n) (f (succ n))) :=
  (pairwise_disjoint_on _).2 fun _ _ hmn =>
    disjoint_iff_inf_le.mpr fun _ ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩ =>
      h₂.not_ge <| h₁.trans <| hf <| succ_le_of_lt hmn

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ico (f n) (f (Order.succ n))` are pairwise disjoint. -/
/-
**Monotone.pairwise_disjoint_on_Ico_succ** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：pairwise_disjoint_on_Ico_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf 
: Monotone f) : Pairwise (Disjoint on fun n => Ico (f n) (f (succ n)))
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pairwise_disjoint_on`：pairwise_disjoint_on [PartialOrder α] [OrderBot α]
 [LinearOrder ι] (f : ι -> α) : Pairwise (Disjoint on f) ↔ forall ⦃m n⦄, m < n -
> Disjoint…
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b

--- 原说明 ---
If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone 
function, then
the intervals `Set.Ico (f n) (f (Order.succ n))` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ico_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ico (f n) (f (succ n))) :=
  (pairwise_disjoint_on _).2 fun _ _ hmn =>
    disjoint_iff_inf_le.mpr fun _ ⟨⟨_, h₁⟩, ⟨h₂, _⟩⟩ =>
      h₁.not_ge <| (hf <| succ_le_of_lt hmn).trans h₂

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ioo (f n) (f (Order.succ n))` are pairwise disjoint. -/
/-
**Monotone.pairwise_disjoint_on_Ioo_succ** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：pairwise_disjoint_on_Ioo_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf 
: Monotone f) : Pairwise (Disjoint on fun n => Ioo (f n) (f (succ n)))
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `Monotone.pairwise_disjoint_on_Ico_succ`：pairwise_disjoint_on_Ico_succ [S
uccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) : Pairwise (Disjoint on 
fun n => Ico (f n) (f (succ …
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b

--- 原说明 ---
If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is a monotone 
function, then
the intervals `Set.Ioo (f n) (f (Order.succ n))` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ioo_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioo (f n) (f (succ n))) :=
  hf.pairwise_disjoint_on_Ico_succ.mono fun _ _ h => h.mono Ioo_subset_Ico_self Ioo_subset_Ico_self

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ioc (f Order.pred n) (f n)` are pairwise disjoint. -/
/-
**Monotone.pairwise_disjoint_on_Ioc_pred** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：pairwise_disjoint_on_Ioc_pred [PredOrder α] [Preorder β] {f : α -> β} (hf 
: Monotone f) : Pairwise (Disjoint on fun n => Ioc (f (pred n)) (f n))
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Ico_toDual`：Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc 
b a
· 使用定理 `Monotone.pairwise_disjoint_on_Ico_succ`：pairwise_disjoint_on_Ico_succ [S
uccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) : Pairwise (Disjoint on 
fun n => Ico (f n) (f (succ …
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone 
function, then
the intervals `Set.Ioc (f Order.pred n) (f n)` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ioc_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioc (f (pred n)) (f n)) := by
  simpa using! hf.dual.pairwise_disjoint_on_Ico_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ico (f Order.pred n) (f n)` are pairwise disjoint. -/
/-
**Monotone.pairwise_disjoint_on_Ico_pred** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：pairwise_disjoint_on_Ico_pred [PredOrder α] [Preorder β] {f : α -> β} (hf 
: Monotone f) : Pairwise (Disjoint on fun n => Ico (f (pred n)) (f n))
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Ioc_toDual`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},   Set.Io
c (OrderDual.toDual b) (OrderDual.toDual a) = ⇑OrderDual.ofDual ⁻¹' Set.Ico a b
· 使用定理 `Monotone.pairwise_disjoint_on_Ioc_succ`：pairwise_disjoint_on_Ioc_succ [S
uccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) : Pairwise (Disjoint on 
fun n => Ioc (f n) (f (succ …
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone 
function, then
the intervals `Set.Ico (f Order.pred n) (f n)` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ico_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ico (f (pred n)) (f n)) := by
  simpa using! hf.dual.pairwise_disjoint_on_Ioc_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone function, then
the intervals `Set.Ioo (f Order.pred n) (f n)` are pairwise disjoint. -/
/-
**Monotone.pairwise_disjoint_on_Ioo_pred** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：pairwise_disjoint_on_Ioo_pred [PredOrder α] [Preorder β] {f : α -> β} (hf 
: Monotone f) : Pairwise (Disjoint on fun n => Ioo (f (pred n)) (f n))
参数：hf : Monotone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Ioo_toDual`：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo 
b a
· 使用定理 `Monotone.pairwise_disjoint_on_Ioo_succ`：pairwise_disjoint_on_Ioo_succ [S
uccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) : Pairwise (Disjoint on 
fun n => Ioo (f n) (f (succ …
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…

--- 原说明 ---
If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is a monotone 
function, then
the intervals `Set.Ioo (f Order.pred n) (f n)` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ioo_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Monotone f) :
    Pairwise (Disjoint on fun n => Ioo (f (pred n)) (f n)) := by
  simpa using! hf.dual.pairwise_disjoint_on_Ioo_succ

end Monotone

namespace Antitone

open scoped Function -- required for scoped `on` notation

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ioc (f (Order.succ n)) (f n)` are pairwise disjoint. -/
/-
**Antitone.pairwise_disjoint_on_Ioc_succ** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：pairwise_disjoint_on_Ioc_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf 
: Antitone f) : Pairwise (Disjoint on fun n => Ioc (f (succ n)) (f n))
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.pairwise_disjoint_on_Ioc_pred`：pairwise_disjoint_on_Ioc_pred [P
redOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) : Pairwise (Disjoint on 
fun n => Ioc (f (pred n)) (f…
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)

--- 原说明 ---
If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone
 function, then
the intervals `Set.Ioc (f (Order.succ n)) (f n)` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ioc_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioc (f (succ n)) (f n)) :=
  hf.dual_left.pairwise_disjoint_on_Ioc_pred

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ico (f (Order.succ n)) (f n)` are pairwise disjoint. -/
/-
**Antitone.pairwise_disjoint_on_Ico_succ** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：pairwise_disjoint_on_Ico_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf 
: Antitone f) : Pairwise (Disjoint on fun n => Ico (f (succ n)) (f n))
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.pairwise_disjoint_on_Ico_pred`：pairwise_disjoint_on_Ico_pred [P
redOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) : Pairwise (Disjoint on 
fun n => Ico (f (pred n)) (f…
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)

--- 原说明 ---
If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone
 function, then
the intervals `Set.Ico (f (Order.succ n)) (f n)` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ico_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ico (f (succ n)) (f n)) :=
  hf.dual_left.pairwise_disjoint_on_Ico_pred

/-- If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ioo (f (Order.succ n)) (f n)` are pairwise disjoint. -/
/-
**Antitone.pairwise_disjoint_on_Ioo_succ** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：pairwise_disjoint_on_Ioo_succ [SuccOrder α] [Preorder β] {f : α -> β} (hf 
: Antitone f) : Pairwise (Disjoint on fun n => Ioo (f (succ n)) (f n))
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.pairwise_disjoint_on_Ioo_pred`：pairwise_disjoint_on_Ioo_pred [P
redOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) : Pairwise (Disjoint on 
fun n => Ioo (f (pred n)) (f…
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)

--- 原说明 ---
If `α` is a linear succ order, `β` is a preorder, and `f : α → β` is an antitone
 function, then
the intervals `Set.Ioo (f (Order.succ n)) (f n)` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ioo_succ [SuccOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioo (f (succ n)) (f n)) :=
  hf.dual_left.pairwise_disjoint_on_Ioo_pred

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ioc (f n) (f (Order.pred n))` are pairwise disjoint. -/
/-
**Antitone.pairwise_disjoint_on_Ioc_pred** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：pairwise_disjoint_on_Ioc_pred [PredOrder α] [Preorder β] {f : α -> β} (hf 
: Antitone f) : Pairwise (Disjoint on fun n => Ioc (f n) (f (pred n)))
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.pairwise_disjoint_on_Ioc_succ`：pairwise_disjoint_on_Ioc_succ [S
uccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) : Pairwise (Disjoint on 
fun n => Ioc (f n) (f (succ …
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)

--- 原说明 ---
If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone
 function, then
the intervals `Set.Ioc (f n) (f (Order.pred n))` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ioc_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioc (f n) (f (pred n))) :=
  hf.dual_left.pairwise_disjoint_on_Ioc_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ico (f n) (f (Order.pred n))` are pairwise disjoint. -/
/-
**Antitone.pairwise_disjoint_on_Ico_pred** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：pairwise_disjoint_on_Ico_pred [PredOrder α] [Preorder β] {f : α -> β} (hf 
: Antitone f) : Pairwise (Disjoint on fun n => Ico (f n) (f (pred n)))
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.pairwise_disjoint_on_Ico_succ`：pairwise_disjoint_on_Ico_succ [S
uccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) : Pairwise (Disjoint on 
fun n => Ico (f n) (f (succ …
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)

--- 原说明 ---
If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone
 function, then
the intervals `Set.Ico (f n) (f (Order.pred n))` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ico_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ico (f n) (f (pred n))) :=
  hf.dual_left.pairwise_disjoint_on_Ico_succ

/-- If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone function, then
the intervals `Set.Ioo (f n) (f (Order.pred n))` are pairwise disjoint. -/
/-
**Antitone.pairwise_disjoint_on_Ioo_pred** 是 Mathlib 中的一个定理，位于命名空间 `Antitone`。
形式化陈述：pairwise_disjoint_on_Ioo_pred [PredOrder α] [Preorder β] {f : α -> β} (hf 
: Antitone f) : Pairwise (Disjoint on fun n => Ioo (f n) (f (pred n)))
参数：hf : Antitone f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.pairwise_disjoint_on_Ioo_succ`：pairwise_disjoint_on_Ioo_succ [S
uccOrder α] [Preorder β] {f : α -> β} (hf : Monotone f) : Pairwise (Disjoint on 
fun n => Ioo (f n) (f (succ …
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)

--- 原说明 ---
If `α` is a linear pred order, `β` is a preorder, and `f : α → β` is an antitone
 function, then
the intervals `Set.Ioo (f n) (f (Order.pred n))` are pairwise disjoint.
-/
theorem pairwise_disjoint_on_Ioo_pred [PredOrder α] [Preorder β] {f : α → β} (hf : Antitone f) :
    Pairwise (Disjoint on fun n => Ioo (f n) (f (pred n))) :=
  hf.dual_left.pairwise_disjoint_on_Ioo_succ

end Antitone

