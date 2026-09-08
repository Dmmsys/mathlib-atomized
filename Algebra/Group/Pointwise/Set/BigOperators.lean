/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Results about pointwise operations on sets and big operators.
-/

public section

namespace Set

open Function
open scoped Pointwise

variable {ι α β F : Type*} [FunLike F α β]

section Monoid

variable [Monoid α] [Monoid β] [MonoidHomClass F α β]

@[to_additive]
/-
**Set.image_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {F : Type u_4} [inst : FunLike F α β] [ins
t_1 : Monoid α] [inst_2 : Monoid β]   [MonoidHomClass F α β] (f : F) (l : List (
Set α)), ⇑f '' l.prod = (List.map (fun s => ⇑f '' s) l).prod
参数：f : F；l : List (Set α)；List.map (fun s => ⇑f '' s) l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem image_list_prod (f : F) :
    ∀ l : List (Set α), (f : α → β) '' l.prod = (l.map fun s => f '' s).prod
  | [] => image_one.trans <| congr_arg singleton (map_one f)
  | a :: as => by rw [List.map_cons, List.prod_cons, List.prod_cons, image_mul, image_list_prod _ _]

end Monoid

section CommMonoid

variable [CommMonoid α] [CommMonoid β] [MonoidHomClass F α β]

@[to_additive]
/-
**Set.image_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_multiset_prod (f : F) : forall m : Multiset (Set α), (f : α -> β) ''
 m.prod = (m.map fun s => f '' s).prod
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s → Prop}
, (∀ (a : α), motive ⟦a⟧) → ∀ (q : Quotient s), motive q
· 使用定理 `Set.image_list_prod`：∀ {α : Type u_2} {β : Type u_3} {F : Type u_4} [ins
t : FunLike F α β] [inst_1 : Monoid α] [inst_2 : Monoid β]   [MonoidHomClass F α
 β] (f : …
-/
theorem image_multiset_prod (f : F) :
    ∀ m : Multiset (Set α), (f : α → β) '' m.prod = (m.map fun s => f '' s).prod :=
  Quotient.ind <| by
    simpa only [Multiset.quot_mk_to_coe, Multiset.prod_coe, Multiset.map_coe] using
      image_list_prod f

@[to_additive]
/-
**Set.image_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_finsetProd (f : F) (m : Finset ι) (s : ι -> Set α) : ((f : α -> β) '
' ∏ i in m, s i) = ∏ i in m, f '' s i
参数：f : F；m : Finset ι；s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_multiset_prod`：image_multiset_prod (f : F) : forall m : Multis
et (Set α), (f : α -> β) '' m.prod = (m.map fun s => f '' s).prod
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem image_finsetProd (f : F) (m : Finset ι) (s : ι → Set α) :
    ((f : α → β) '' ∏ i ∈ m, s i) = ∏ i ∈ m, f '' s i :=
  (image_multiset_prod f _).trans <| congr_arg Multiset.prod <| Multiset.map_map _ _ _

@[deprecated (since := "2026-04-08")] alias image_finset_sum := image_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias image_finset_prod := image_finsetProd

/-- The n-ary version of `Set.mem_mul`. -/
@[to_additive /-- The n-ary version of `Set.mem_add`. -/]
/-
**Set.mem_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_finsetProd (t : Finset ι) (f : ι -> Set α) (a : α) : (a in ∏ i in t, f
 i) ↔ exists (g : ι -> α) (_ : forall {i}, i in t -> g i in f i), ∏ i in t, g i 
= a
参数：t : Finset ι；f : ι -> Set α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Set.mem_mul`：mem_mul : a in s * t ↔ exists x in s, exists y in t, x * y 
= a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.prod_update_of_notMem`：prod_update_of_notMem [DecidableEq ι] {s :
 Finset ι} {i : ι} (h : i ∉ s) (f : ι -> M) (b : M) : ∏ x in s, Function.update 
f i b x = ∏ x in s…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
The n-ary version of `Set.mem_mul`.
-/
theorem mem_finsetProd (t : Finset ι) (f : ι → Set α) (a : α) :
    (a ∈ ∏ i ∈ t, f i) ↔ ∃ (g : ι → α) (_ : ∀ {i}, i ∈ t → g i ∈ f i), ∏ i ∈ t, g i = a := by
  classical
    induction t using Finset.induction_on generalizing a with
    | empty =>
      simp_rw [Finset.prod_empty, Set.mem_one]
      exact ⟨fun h ↦ ⟨fun _ ↦ a, fun hi ↦ False.elim (Finset.notMem_empty _ hi), h.symm⟩,
        fun ⟨_, _, hf⟩ ↦ hf.symm⟩
    | insert i is hi ih => ?_
    rw [Finset.prod_insert hi, Set.mem_mul]
    simp_rw [Finset.prod_insert hi]
    simp_rw [ih]
    constructor
    · rintro ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩
      refine ⟨Function.update g i x, ?_, ?_⟩
      · intro j hj
        obtain rfl | hj := Finset.mem_insert.mp hj
        · rwa [Function.update_self]
        · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
          exact hg hj
      · rw [Finset.prod_update_of_notMem hi, Function.update_self]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g i, hg (is.mem_insert_self _), is.prod g,
        ⟨⟨g, fun hi ↦ hg (Finset.mem_insert_of_mem hi), rfl⟩, rfl⟩⟩

@[deprecated (since := "2026-04-08")] alias mem_finset_sum := mem_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias mem_finset_prod := mem_finsetProd

@[to_additive]
/-
**Set.mem_pow_iff_prod** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_pow_iff_prod {n : Nat} {s : Set α} {a : α} : a in s ^ n ↔ exists f : F
in n -> α, (forall i, f i in s) ∧ ∏ i, f i = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Set.mem_finsetProd`：mem_finsetProd (t : Finset ι) (f : ι -> Set α) (a : 
α) : (a in ∏ i in t, f i) ↔ exists (g : ι -> α) (_ : forall {i}, i in t -> g i i
n f i), …
-/
lemma mem_pow_iff_prod {n : ℕ} {s : Set α} {a : α} :
    a ∈ s ^ n ↔ ∃ f : Fin n → α, (∀ i, f i ∈ s) ∧ ∏ i, f i = a := by
  simpa using mem_finsetProd (t := .univ) (f := fun _ : Fin n ↦ s) _

/-- A version of `Set.mem_finsetProd` with a simpler RHS for products over a Fintype. -/
@[to_additive /-- A version of `Set.mem_finsetSum` with a simpler RHS for sums over a Fintype. -/]
/-
**Set.mem_fintype_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_fintype_prod [Fintype ι] (f : ι -> Set α) (a : α) : (a in ∏ i, f i) ↔ 
exists (g : ι -> α) (_ : forall i, g i in f i), ∏ i, g i = a
参数：f : ι -> Set α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_finsetProd`：mem_finsetProd (t : Finset ι) (f : ι -> Set α) (a : 
α) : (a in ∏ i in t, f i) ↔ exists (g : ι -> α) (_ : forall {i}, i in t -> g i i
n f i), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A version of `Set.mem_finsetProd` with a simpler RHS for products over a Fintype
.
-/
theorem mem_fintype_prod [Fintype ι] (f : ι → Set α) (a : α) :
    (a ∈ ∏ i, f i) ↔ ∃ (g : ι → α) (_ : ∀ i, g i ∈ f i), ∏ i, g i = a := by
  rw [mem_finsetProd]
  simp

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
/-
**Set.list_prod_mem_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：list_prod_mem_list_prod (t : List ι) (f : ι -> Set α) (g : ι -> α) (hg : f
orall i in t, g i in f i) : (t.map g).prod in (t.map f).prod
参数：t : List ι；f : ι -> Set α；g : ι -> α；hg : forall i in t, g i in f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Set.mul_mem_mul`：mul_mem_mul : a in s -> b in t -> a * b in s * t
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l

--- 原说明 ---
An n-ary version of `Set.mul_mem_mul`.
-/
theorem list_prod_mem_list_prod (t : List ι) (f : ι → Set α) (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
    (t.map g).prod ∈ (t.map f).prod := by
  induction t with
  | nil => simp_rw [List.map_nil, List.prod_nil, Set.mem_one]
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_mem_mul (hg h List.mem_cons_self)
      (ih fun i hi ↦ hg i <| List.mem_cons_of_mem _ hi)

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_subset_add`. -/]
/-
**Set.list_prod_subset_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：list_prod_subset_list_prod (t : List ι) (f₁ f₂ : ι -> Set α) (hf : forall 
i in t, f₁ i subseteq f₂ i) : (t.map f₁).prod subseteq (t.map f₂).prod
参数：t : List ι；f₁ f₂ : ι -> Set α；hf : forall i in t, f₁ i subseteq f₂ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Set.mul_subset_mul`：mul_subset_mul : s₁ subseteq t₁ -> s₂ subseteq t₂ ->
 s₁ * s₂ subseteq t₁ * t₂
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l

--- 原说明 ---
An n-ary version of `Set.mul_subset_mul`.
-/
theorem list_prod_subset_list_prod (t : List ι) (f₁ f₂ : ι → Set α) (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) :
    (t.map f₁).prod ⊆ (t.map f₂).prod := by
  induction t with
  | nil => rfl
  | cons h tl ih =>
    simp_rw [List.map_cons, List.prod_cons]
    exact mul_subset_mul (hf h List.mem_cons_self)
      (ih fun i hi ↦ hf i <| List.mem_cons_of_mem _ hi)

@[to_additive]
/-
**Set.list_prod_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：list_prod_singleton {M : Type*} [Monoid M] (s : List M) : (s.map fun i => 
({i} : Set M)).prod = {s.prod}
参数：s : List M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
theorem list_prod_singleton {M : Type*} [Monoid M] (s : List M) :
    (s.map fun i ↦ ({i} : Set M)).prod = {s.prod} :=
  (map_list_prod (singletonMonoidHom : M →* Set M) _).symm

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
/-
**Set.multiset_prod_mem_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：multiset_prod_mem_multiset_prod (t : Multiset ι) (f : ι -> Set α) (g : ι -
> α) (hg : forall i in t, g i in f i) : (t.map g).prod in (t.map f).prod
参数：t : Multiset ι；f : ι -> Set α；g : ι -> α；hg : forall i in t, g i in f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Set.list_prod_mem_list_prod`：list_prod_mem_list_prod (t : List ι) (f : ι
 -> Set α) (g : ι -> α) (hg : forall i in t, g i in f i) : (t.map g).prod in (t.
map f).prod

--- 原说明 ---
An n-ary version of `Set.mul_mem_mul`.
-/
theorem multiset_prod_mem_multiset_prod (t : Multiset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (t.map g).prod ∈ (t.map f).prod := by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_mem_list_prod _ _ _ hg

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_subset_add`. -/]
/-
**Set.multiset_prod_subset_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：multiset_prod_subset_multiset_prod (t : Multiset ι) (f₁ f₂ : ι -> Set α) (
hf : forall i in t, f₁ i subseteq f₂ i) : (t.map f₁).prod subseteq (t.map f₂).pr
od
参数：t : Multiset ι；f₁ f₂ : ι -> Set α；hf : forall i in t, f₁ i subseteq f₂ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Set.list_prod_subset_list_prod`：list_prod_subset_list_prod (t : List ι) 
(f₁ f₂ : ι -> Set α) (hf : forall i in t, f₁ i subseteq f₂ i) : (t.map f₁).prod 
subseteq (t.map f₂).…

--- 原说明 ---
An n-ary version of `Set.mul_subset_mul`.
-/
theorem multiset_prod_subset_multiset_prod (t : Multiset ι) (f₁ f₂ : ι → Set α)
    (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) : (t.map f₁).prod ⊆ (t.map f₂).prod := by
  induction t using Quotient.inductionOn
  simp_rw [Multiset.quot_mk_to_coe, Multiset.map_coe, Multiset.prod_coe]
  exact list_prod_subset_list_prod _ _ _ hf

@[to_additive]
/-
**Set.multiset_prod_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：multiset_prod_singleton {M : Type*} [CommMonoid M] (s : Multiset M) : (s.m
ap fun i => ({i} : Set M)).prod = {s.prod}
参数：s : Multiset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
-/
theorem multiset_prod_singleton {M : Type*} [CommMonoid M] (s : Multiset M) :
    (s.map fun i ↦ ({i} : Set M)).prod = {s.prod} :=
  (map_multiset_prod (singletonMonoidHom : M →* Set M) _).symm

/-- An n-ary version of `Set.mul_mem_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_mem_add`. -/]
/-
**Set.finsetProd_mem_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finsetProd_mem_finsetProd (t : Finset ι) (f : ι -> Set α) (g : ι -> α) (hg
 : forall i in t, g i in f i) : (∏ i in t, g i) in ∏ i in t, f i
参数：t : Finset ι；f : ι -> Set α；g : ι -> α；hg : forall i in t, g i in f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.multiset_prod_mem_multiset_prod`：multiset_prod_mem_multiset_prod (t 
: Multiset ι) (f : ι -> Set α) (g : ι -> α) (hg : forall i in t, g i in f i) : (
t.map g).prod in (t.map f…

--- 原说明 ---
An n-ary version of `Set.mul_mem_mul`.
-/
theorem finsetProd_mem_finsetProd (t : Finset ι) (f : ι → Set α) (g : ι → α)
    (hg : ∀ i ∈ t, g i ∈ f i) : (∏ i ∈ t, g i) ∈ ∏ i ∈ t, f i :=
  multiset_prod_mem_multiset_prod _ _ _ hg

@[deprecated (since := "2026-04-08")] alias finset_sum_mem_finset_sum := finsetSum_mem_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_mem_finset_prod := finsetProd_mem_finsetProd

/-- An n-ary version of `Set.mul_subset_mul`. -/
@[to_additive /-- An n-ary version of `Set.add_subset_add`. -/]
/-
**Set.finsetProd_subset_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finsetProd_subset_finsetProd (t : Finset ι) (f₁ f₂ : ι -> Set α) (hf : for
all i in t, f₁ i subseteq f₂ i) : ∏ i in t, f₁ i subseteq ∏ i in t, f₂ i
参数：t : Finset ι；f₁ f₂ : ι -> Set α；hf : forall i in t, f₁ i subseteq f₂ i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.multiset_prod_subset_multiset_prod`：multiset_prod_subset_multiset_pr
od (t : Multiset ι) (f₁ f₂ : ι -> Set α) (hf : forall i in t, f₁ i subseteq f₂ i
) : (t.map f₁).prod subseteq…

--- 原说明 ---
An n-ary version of `Set.mul_subset_mul`.
-/
theorem finsetProd_subset_finsetProd (t : Finset ι) (f₁ f₂ : ι → Set α)
    (hf : ∀ i ∈ t, f₁ i ⊆ f₂ i) : ∏ i ∈ t, f₁ i ⊆ ∏ i ∈ t, f₂ i :=
  multiset_prod_subset_multiset_prod _ _ _ hf

@[deprecated (since := "2026-04-08")]
alias finset_sum_subset_finset_sum := finsetSum_subset_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_subset_finset_prod := finsetProd_subset_finsetProd

@[to_additive]
/-
**Set.finsetProd_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：finsetProd_singleton {M ι : Type*} [CommMonoid M] (s : Finset ι) (I : ι ->
 M) : ∏ i in s, ({I i} : Set M) = {∏ i in s, I i}
参数：s : Finset ι；I : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem finsetProd_singleton {M ι : Type*} [CommMonoid M] (s : Finset ι) (I : ι → M) :
    ∏ i ∈ s, ({I i} : Set M) = {∏ i ∈ s, I i} :=
  (map_prod (singletonMonoidHom : M →* Set M) _ _).symm

@[deprecated (since := "2026-04-08")] alias finset_sum_singleton := finsetSum_singleton

@[to_additive existing, deprecated (since := "2026-04-08")]
alias finset_prod_singleton := finsetProd_singleton

/-- The n-ary version of `Set.image_mul_prod`. -/
@[to_additive /-- The n-ary version of `Set.add_image_prod`. -/]
/-
**Set.image_finsetProd_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_finsetProd_pi (l : Finset ι) (S : ι -> Set α) : (fun f : ι -> α => ∏
 i in l, f i) '' (l : Set ι).pi S = ∏ i in l, S i
参数：l : Finset ι；S : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The n-ary version of `Set.image_mul_prod`.
-/
theorem image_finsetProd_pi (l : Finset ι) (S : ι → Set α) :
    (fun f : ι → α => ∏ i ∈ l, f i) '' (l : Set ι).pi S = ∏ i ∈ l, S i := by
  ext
  simp_rw [mem_finsetProd, mem_image, mem_pi, exists_prop, Finset.mem_coe]

@[deprecated (since := "2026-04-08")] alias image_finset_sum_pi := image_finsetSum_pi

@[to_additive existing, deprecated (since := "2026-04-08")]
alias image_finset_prod_pi := image_finsetProd_pi

/-- A special case of `Set.image_finsetProd_pi` for `Finset.univ`. -/
@[to_additive /-- A special case of `Set.image_finsetSum_pi` for `Finset.univ`. -/]
/-
**Set.image_fintype_prod_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_fintype_prod_pi [Fintype ι] (S : ι -> Set α) : (fun f : ι -> α => ∏ 
i, f i) '' univ.pi S = ∏ i, S i
参数：S : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_finsetProd_pi`：image_finsetProd_pi (l : Finset ι) (S : ι -> Se
t α) : (fun f : ι -> α => ∏ i in l, f i) '' (l : Set ι).pi S = ∏ i in l, S i

--- 原说明 ---
A special case of `Set.image_finsetProd_pi` for `Finset.univ`.
-/
theorem image_fintype_prod_pi [Fintype ι] (S : ι → Set α) :
    (fun f : ι → α => ∏ i, f i) '' univ.pi S = ∏ i, S i := by
  simpa only [Finset.coe_univ] using image_finsetProd_pi Finset.univ S

end CommMonoid

/-! TODO: define `decidable_mem_finsetProd` and `decidable_mem_finsetSum`. -/


end Set

