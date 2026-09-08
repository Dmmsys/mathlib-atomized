/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Preorder.Finite

/-!
# Dissociation and span

This file defines dissociation and span of sets in groups. These are analogs to the usual linear
independence and linear span of sets in a vector space but where the scalars are only allowed to be
`0` or `±1`. In characteristic 2 or 3, the two pairs of concepts are actually equivalent.

## Main declarations

* `MulDissociated`/`AddDissociated`: Predicate for a set to be dissociated.
* `Finset.mulSpan`/`Finset.addSpan`: Span of a finset.
-/

@[expose] public section

variable {α β : Type*} [CommGroup α] [CommGroup β]

section dissociation
variable {s : Set α} {t u : Finset α} {d : ℕ} {a : α}
open Set

/-- A set is dissociated iff all its finite subsets have different products.

This is an analog of linear independence in a vector space, but with the "scalars" restricted to
`0` and `±1`. -/
@[to_additive /-- A set is dissociated iff all its finite subsets have different sums.

This is an analog of linear independence in a vector space, but with the "scalars" restricted to
`0` and `±1`. -/]
/-
**MulDissociated** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulDissociated (s : Set α) : Prop
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulDissociated (s : Set α) : Prop := {t : Finset α | ↑t ⊆ s}.InjOn (∏ x ∈ ·, x)
/-
**mulDissociated_iff_sum_eq_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α] {s : Set α},   MulDissociated s ↔ ∀ 
(a : α), {t | ↑t ⊆ s ∧ ∏ x ∈ t, x = a}.Subsingleton
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[to_additive] lemma mulDissociated_iff_sum_eq_subsingleton :
    MulDissociated s ↔ ∀ a, {t : Finset α | ↑t ⊆ s ∧ ∏ x ∈ t, x = a}.Subsingleton :=
  ⟨fun hs _ _t ht _u hu ↦ hs ht.1 hu.1 <| ht.2.trans hu.2.symm,
    fun hs _t ht _u hu htu ↦ hs _ ⟨ht, htu⟩ ⟨hu, rfl⟩⟩
/-
**MulDissociated.subset** 是 Mathlib 中的一个定理，位于命名空间 `MulDissociated`。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α] {s t : Set α}, s ⊆ t → MulDissociate
d t → MulDissociated s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
-/
@[to_additive] lemma MulDissociated.subset {t : Set α} (hst : s ⊆ t) (ht : MulDissociated t) :
    MulDissociated s := ht.mono fun _ ↦ hst.trans'
/-
**mulDissociated_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α], MulDissociated ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
@[to_additive (attr := simp)] lemma mulDissociated_empty : MulDissociated (∅ : Set α) := by
  simp [MulDissociated, subset_empty_iff]

@[to_additive (attr := simp)]
/-
**mulDissociated_singleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulDissociated_singleton : MulDissociated ({a} : Set α) ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulDissociated_singleton : MulDissociated ({a} : Set α) ↔ a ≠ 1 := by
  simp [MulDissociated, ofPred_or, -subset_singleton_iff,
    Finset.coe_subset_singleton]

@[to_additive (attr := simp)]
/-
**not_mulDissociated** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_mulDissociated : ¬ MulDissociated s ↔ exists t : Finset α, ↑t subseteq
 s ∧ exists u : Finset α, ↑u subseteq s ∧ t != u ∧ ∏ x in t, x = ∏ x in u, x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_mulDissociated :
    ¬ MulDissociated s ↔
      ∃ t : Finset α, ↑t ⊆ s ∧ ∃ u : Finset α, ↑u ⊆ s ∧ t ≠ u ∧ ∏ x ∈ t, x = ∏ x ∈ u, x := by
  grind [MulDissociated, InjOn]

@[to_additive]
/-
**not_mulDissociated_iff_exists_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_mulDissociated_iff_exists_disjoint : ¬ MulDissociated s ↔ exists t u :
 Finset α, ↑t subseteq s ∧ ↑u subseteq s ∧ Disjoint t u ∧ t != u ∧ ∏ a in t, a =
 ∏ a in u, a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `not_mulDissociated`：not_mulDissociated : ¬ MulDissociated s ↔ exists t :
 Finset α, ↑t subseteq s ∧ exists u : Finset α, ↑u subseteq s ∧ t != u ∧ ∏ x in 
t, x = ∏…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_sdiff`：coe_sdiff (s₁ s₂ : Finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ :
 Set α)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `disjoint_sdiff_sdiff`：disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sdiff_ne_sdiff_iff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra
 α] {a b : α}, a \ b ≠ b \ a ↔ a ≠ b
· 使用引理 `Finset.prod_sdiff_eq_prod_sdiff_iff`：prod_sdiff_eq_prod_sdiff_iff : ∏ i 
in s \ t, f i = ∏ i in t \ s, f i ↔ ∏ i in s, f i = ∏ i in t, f i
-/
lemma not_mulDissociated_iff_exists_disjoint :
    ¬ MulDissociated s ↔
      ∃ t u : Finset α, ↑t ⊆ s ∧ ↑u ⊆ s ∧ Disjoint t u ∧ t ≠ u ∧ ∏ a ∈ t, a = ∏ a ∈ u, a := by
  classical
  refine not_mulDissociated.trans
    ⟨?_, fun ⟨t, u, ht, hu, _, htune, htusum⟩ ↦ ⟨t, ht, u, hu, htune, htusum⟩⟩
  rintro ⟨t, ht, u, hu, htu, h⟩
  refine ⟨t \ u, u \ t, ?_, ?_, disjoint_sdiff_sdiff, sdiff_ne_sdiff_iff.2 htu,
    Finset.prod_sdiff_eq_prod_sdiff_iff.2 h⟩ <;> push_cast <;> exact sdiff_subset.trans ‹_›
/-
**MulEquiv.mulDissociated_preimage** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : CommGroup α] [inst_1 : CommGroup β
] {s : Set α} (e : β ≃* α),   MulDissociated (⇑e ⁻¹' s) ↔ MulDissociated s
参数：e : β ≃* α；⇑e ⁻¹' s。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulEquiv.apply_eq_iff_eq`：apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x =
 e y ↔ x = y
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.prod_map`：prod_map (s : Finset ι) (e : ι ↪ κ) (f : κ -> M) : ∏ x 
in s.map e, f x = ∏ x in s, f (e x)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finset.map_injective`：map_injective (f : α ↪ β) : Injective (map f)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive (attr := simp)] lemma MulEquiv.mulDissociated_preimage (e : β ≃* α) :
    MulDissociated (e ⁻¹' s) ↔ MulDissociated s := by
  simp [MulDissociated, InjOn, ← e.finsetCongr.forall_congr_right, ← e.apply_eq_iff_eq,
    (Finset.map_injective _).eq_iff]
/-
**mulDissociated_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : CommGroup α] {s : Set α}, MulDissociated s⁻¹ ↔ Mu
lDissociated s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.mulDissociated_preimage`：∀ {α : Type u_1} {β : Type u_2} [inst 
: CommGroup α] [inst_1 : CommGroup β] {s : Set α} (e : β ≃* α),   MulDissociated
 (⇑e ⁻¹' s) ↔ MulDisso…
-/
@[to_additive (attr := simp)] lemma mulDissociated_inv : MulDissociated s⁻¹ ↔ MulDissociated s :=
  (MulEquiv.inv α).mulDissociated_preimage

@[to_additive] protected alias ⟨MulDissociated.of_inv, MulDissociated.inv⟩ := mulDissociated_inv

end dissociation

namespace Finset
variable [DecidableEq α] [Fintype α] {s t u : Finset α} {a : α} {d : ℕ}

/-- The span of a finset `s` is the finset of elements of the form `∏ a ∈ s, a ^ ε a` where
`ε ∈ {-1, 0, 1} ^ s`.

This is an analog of the linear span in a vector space, but with the "scalars" restricted to
`0` and `±1`. -/
@[to_additive /-- The span of a finset `s` is the finset of elements of the form `∑ a ∈ s, ε a • a`
where `ε ∈ {-1, 0, 1} ^ s`.

This is an analog of the linear span in a vector space, but with the "scalars" restricted to
`0` and `±1`. -/]
/-
**Finset.mulSpan** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：mulSpan (s : Finset α) : Finset α
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulSpan (s : Finset α) : Finset α :=
  (Fintype.piFinset fun _a ↦ ({-1, 0, 1} : Finset ℤ)).image fun ε ↦ ∏ a ∈ s, a ^ ε a

@[to_additive (attr := simp)]
/-
**Finset.mem_mulSpan** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mem_mulSpan : a in mulSpan s ↔ exists ε : α -> Int, (forall a, ε a = -1 ∨ 
ε a = 0 ∨ ε a = 1) ∧ ∏ a in s, a ^ ε a = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_mulSpan :
    a ∈ mulSpan s ↔ ∃ ε : α → ℤ, (∀ a, ε a = -1 ∨ ε a = 0 ∨ ε a = 1) ∧ ∏ a ∈ s, a ^ ε a = a := by
  simp [mulSpan]

@[to_additive (attr := simp)]
/-
**Finset.subset_mulSpan** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：subset_mulSpan : s subseteq mulSpan s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.mem_mulSpan`：mem_mulSpan : a in mulSpan s ↔ exists ε : α -> Int, 
(forall a, ε a = -1 ∨ ε a = 0 ∨ ε a = 1) ∧ ∏ a in s, a ^ ε a = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用引理 `pow_ite`：pow_ite (p : Prop) [Decidable p] (a : α) (b c : β) : a ^ (if p 
then b else c) = if p then a ^ b else a ^ c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.prod_ite_eq'`：prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι)
 (b : ι -> M) : (∏ x in s, ite (x = a) (b x) 1) = ite (a in s) (b a) 1
（共 32 条，此处仅展示前 30 条）
-/
lemma subset_mulSpan : s ⊆ mulSpan s := fun a ha ↦
  mem_mulSpan.2 ⟨Pi.single a 1, fun b ↦ by obtain rfl | hab := eq_or_ne a b <;> simp [*], by
    simp [Pi.single, Function.update, pow_ite, ha]⟩

@[to_additive]
/-
**Finset.prod_div_prod_mem_mulSpan** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_div_prod_mem_mulSpan (ht : t subseteq s) (hu : u subseteq s) : (∏ a i
n t, a) / ∏ a in u, a in mulSpan s
参数：ht : t subseteq s；hu : u subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.mem_mulSpan`：mem_mulSpan : a in mulSpan s ↔ exists ε : α -> Int, 
(forall a, ε a = -1 ∨ ε a = 0 ∨ ε a = 1) ∧ ∏ a in s, a ^ ε a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zpow_sub`：∀ {G : Type u_3} [inst : Group G] (a : G) (m n : ℤ), a ^ (m - 
n) = a ^ m * (a ^ n)⁻¹
· 使用引理 `pow_ite`：pow_ite (p : Prop) [Decidable p] (a : α) (b c : β) : a ^ (if p 
then b else c) = if p then a ^ b else a ^ c
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
（共 33 条，此处仅展示前 30 条）
-/
lemma prod_div_prod_mem_mulSpan (ht : t ⊆ s) (hu : u ⊆ s) :
    (∏ a ∈ t, a) / ∏ a ∈ u, a ∈ mulSpan s :=
  mem_mulSpan.2 ⟨Set.indicator t 1 - Set.indicator u 1, fun a ↦ by
    by_cases a ∈ t <;> by_cases a ∈ u <;> simp [*], by simp [prod_div_distrib, zpow_sub,
      ← div_eq_mul_inv, Set.indicator, pow_ite, inter_eq_right.2, *]⟩

/-- If every dissociated subset of `s` has size at most `d`, then `s` is actually generated by a
subset of size at most `d`.

This is a dissociation analog of the fact that a set whose linearly independent subsets all have
size at most `d` is of dimension at most `d` itself. -/
@[to_additive /-- If every dissociated subset of `s` has size at most `d`, then `s` is actually
generated by a subset of size at most `d`.

This is a dissociation analog of the fact that a set whose linearly independent subspaces all have
size at most `d` is of dimension at most `d` itself. -/]
/-
**Finset.exists_subset_mulSpan_card_le_of_forall_mulDissociated** 是 Mathlib 中的一个
引理，位于命名空间 `Finset`。
形式化陈述：exists_subset_mulSpan_card_le_of_forall_mulDissociated (hs : forall s', s'
 subseteq s -> MulDissociated (s' : Set α) -> s'.card <= d) : exists s', s' subs
eteq s ∧ s'.card <= d ∧ s subseteq mulSpan s'
参数：hs : forall s', s' subseteq s -> MulDissociated (s' : Set α) -> s'.card <= d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_maximal`：exists_maximal (hs : s.Nonempty) : exists i, Maxi
mal (· in s) i
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Finset.empty_mem_powerset`：empty_mem_powerset (s : Finset α) : ∅ in powe
rset s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Finset.subset_mulSpan`：subset_mulSpan : s subseteq mulSpan s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `not_mulDissociated_iff_exists_disjoint`：not_mulDissociated_iff_exists_di
sjoint : ¬ MulDissociated s ↔ exists t u : Finset α, ↑t subseteq s ∧ ↑u subseteq
 s ∧ Disjoint t u ∧ t != u ∧…
· 使用定理 `Maximal.not_gt`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Preord
er α], Maximal P x → P y → ¬x < y
· 使用定理 `Finset.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a 
in t ∧ s subseteq t
· 使用定理 `Finset.ssubset_insert`：ssubset_insert (h : a ∉ s) : s ⊂ insert a s
· 使用定理 `Finset.prod_erase_eq_div`：prod_erase_eq_div {a : ι} (h : a in s) : ∏ x i
n s.erase a, f x = (∏ x in s, f x) / f a
· 使用定理 `div_div_self'`：div_div_self' (a b : G) : a / (a / b) = b
· 使用引理 `Finset.prod_div_prod_mem_mulSpan`：prod_div_prod_mem_mulSpan (ht : t subs
eteq s) (hu : u subseteq s) : (∏ a in t, a) / ∏ a in u, a in mulSpan s
· 使用定理 `Finset.subset_insert_iff_of_notMem`：subset_insert_iff_of_notMem (h : a ∉
 s) : s subseteq insert a t ↔ s subseteq t
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Finset.subset_insert_iff`：subset_insert_iff {a : α} {s t : Finset α} : s
 subseteq insert a t ↔ s.erase a subseteq t
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
-/
lemma exists_subset_mulSpan_card_le_of_forall_mulDissociated
    (hs : ∀ s', s' ⊆ s → MulDissociated (s' : Set α) → s'.card ≤ d) :
    ∃ s', s' ⊆ s ∧ s'.card ≤ d ∧ s ⊆ mulSpan s' := by
  classical
  obtain ⟨s', hs'⟩ :=
    (s.powerset.filter fun s' : Finset α ↦ MulDissociated (s' : Set α)).exists_maximal
      ⟨∅, mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  simp only [mem_filter, mem_powerset] at hs'
  refine ⟨s', hs'.1.1, hs _ hs'.1.1 hs'.1.2, fun a ha ↦ ?_⟩
  by_cases ha' : a ∈ s'
  · exact subset_mulSpan ha'
  obtain ⟨t, u, ht, hu, htu⟩ := not_mulDissociated_iff_exists_disjoint.1 fun h ↦
    hs'.not_gt ⟨insert_subset_iff.2 ⟨ha, hs'.1.1⟩, h⟩ <| ssubset_insert ha'
  by_cases hat : a ∈ t
  · have : a = (∏ b ∈ u, b) / ∏ b ∈ t.erase a, b := by
      rw [prod_erase_eq_div hat, htu.2.2, div_div_self']
    rw [this]
    exact prod_div_prod_mem_mulSpan
      ((subset_insert_iff_of_notMem <| disjoint_left.1 htu.1 hat).1 hu) (subset_insert_iff.1 ht)
  rw [coe_subset, subset_insert_iff_of_notMem hat] at ht
  by_cases hau : a ∈ u
  · have : a = (∏ b ∈ t, b) / ∏ b ∈ u.erase a, b := by
      rw [prod_erase_eq_div hau, htu.2.2, div_div_self']
    rw [this]
    exact prod_div_prod_mem_mulSpan ht (subset_insert_iff.1 hu)
  · rw [coe_subset, subset_insert_iff_of_notMem hau] at hu
    cases not_mulDissociated_iff_exists_disjoint.2 ⟨t, u, ht, hu, htu⟩ hs'.1.2

end Finset

