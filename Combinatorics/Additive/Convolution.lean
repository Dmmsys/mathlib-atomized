/-
Copyright (c) 2025 Yaël Dillies, Strahinja Gvozdić, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Strahinja Gvozdić, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# Convolution

This file defines convolution of finite subsets `A` and `B` of group `G` as the map `A ⋆ B : G → ℕ`
that maps `x ∈ G` to the number of distinct representations of `x` in the form `x = ab` for
`a ∈ A`, `b ∈ B`. It is shown how convolution behaves under the change of order of `A` and `B`, as
well as under the left and right actions on `A`, `B`, and the function argument.
-/

@[expose] public section

open MulOpposite MulAction
open scoped Pointwise RightActions

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {A B : Finset G} {s x y : G}

/-- Given finite subsets `A` and `B` of a group `G`, convolution of `A` and `B` is a map `G → ℕ`
that maps `x ∈ G` to the number of distinct representations of `x` in the form `x = ab`, where
`a ∈ A`, `b ∈ B`. -/
@[to_additive addConvolution /-- Given finite subsets `A` and `B` of an additive group `G`,
convolution of `A` and `B` is a map `G → ℕ` that maps `x ∈ G` to the number of distinct
representations of `x` in the form `x = a + b`, where `a ∈ A`, `b ∈ B`. -/]
/-
**Finset.convolution** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：convolution (A B : Finset G) : G -> Nat
参数：A B : Finset G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def convolution (A B : Finset G) : G → ℕ := fun x => #{ab ∈ A ×ˢ B | ab.1 * ab.2 = x}

@[to_additive]
/-
**Finset.card_smul_inter_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_smul_inter_smul (A B : Finset G) (x y : G) : #((x • A) inter (y • B))
 = A.convolution B⁻¹ (x⁻¹ * y)
参数：A B : Finset G；x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_nbij'`：card_nbij' (i : α -> β) (j : β -> α) (hi : Set.MapsTo
 i s t) (hj : Set.MapsTo j t s) (left_inv : Set.LeftInvOn j i s) (right_inv : Se
t.Right…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.LeftInvOn.eq_1`：∀ {α : Type u} {β : Type v} (g : β → α) (f : α → β) 
(s : Set α), Set.LeftInvOn g f s = ∀ ⦃x : α⦄, x ∈ s → g (f x) = x
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma card_smul_inter_smul (A B : Finset G) (x y : G) :
    #((x • A) ∩ (y • B)) = A.convolution B⁻¹ (x⁻¹ * y) :=
  card_nbij' (fun z ↦ (x⁻¹ * z, z⁻¹ * y)) (fun ab' ↦ x • ab'.1)
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem, mul_assoc])
    (by simp +contextual [Set.MapsTo, Set.mem_smul_set_iff_inv_smul_mem]
        simp +contextual [← eq_mul_inv_iff_mul_eq, mul_assoc])
    (by simp [Set.LeftInvOn])
    (by simp +contextual [Set.LeftInvOn, ← eq_mul_inv_iff_mul_eq, mul_assoc])

@[to_additive]
/-
**Finset.card_inter_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_inter_smul (A B : Finset G) (x : G) : #(A inter (x • B)) = A.convolut
ion B⁻¹ x
参数：A B : Finset G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.convolution.congr_simp`：∀ {G : Type u_1} [inst : Group G] {inst_1
 : DecidableEq G} [inst_2 : DecidableEq G] (A A_1 : Finset G),   A = A_1 → ∀ (B 
B_1 : Finset G), B …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Finset.card_smul_inter_smul`：card_smul_inter_smul (A B : Finset G) (x y 
: G) : #((x • A) inter (y • B)) = A.convolution B⁻¹ (x⁻¹ * y)
-/
lemma card_inter_smul (A B : Finset G) (x : G) : #(A ∩ (x • B)) = A.convolution B⁻¹ x := by
  simpa using card_smul_inter_smul _ _ 1 x

@[to_additive]
/-
**Finset.card_smul_inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_smul_inter (A B : Finset G) (x : G) : #((x • A) inter B) = A.convolut
ion B⁻¹ x⁻¹
参数：A B : Finset G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.convolution.congr_simp`：∀ {G : Type u_1} [inst : Group G] {inst_1
 : DecidableEq G} [inst_2 : DecidableEq G] (A A_1 : Finset G),   A = A_1 → ∀ (B 
B_1 : Finset G), B …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Finset.card_smul_inter_smul`：card_smul_inter_smul (A B : Finset G) (x y 
: G) : #((x • A) inter (y • B)) = A.convolution B⁻¹ (x⁻¹ * y)
-/
lemma card_smul_inter (A B : Finset G) (x : G) : #((x • A) ∩ B) = A.convolution B⁻¹ x⁻¹ := by
  simpa using card_smul_inter_smul _ _ x 1

@[to_additive]
/-
**Finset.card_inter_smul_inv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_inter_smul_inv (A B : Finset G) (x : G) : #(A inter (x • B⁻¹)) = A.co
nvolution B x
参数：A B : Finset G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.card_inter_smul`：card_inter_smul (A B : Finset G) (x : G) : #(A i
nter (x • B)) = A.convolution B⁻¹ x
· 使用定理 `Finset.convolution.congr_simp`：∀ {G : Type u_1} [inst : Group G] {inst_1
 : DecidableEq G} [inst_2 : DecidableEq G] (A A_1 : Finset G),   A = A_1 → ∀ (B 
B_1 : Finset G), B …
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_inter_smul_inv (A B : Finset G) (x : G) : #(A ∩ (x • B⁻¹)) = A.convolution B x := by
  simp [card_inter_smul]

@[to_additive]
/-
**Finset.card_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_mul_eq (A B : Finset G) (x : G) : #{ab in A ×ˢ B | ab.1 * ab.2 = x} =
 A.convolution B x
参数：A B : Finset G；x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma card_mul_eq (A B : Finset G) (x : G) :
    #{ab ∈ A ×ˢ B | ab.1 * ab.2 = x} = A.convolution B x := rfl

@[to_additive]
/-
**Finset.card_div_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_div_eq (A B : Finset G) (x : G) : #{ab in A ×ˢ B | ab.1 / ab.2 = x} =
 A.convolution B⁻¹ x
参数：A B : Finset G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_equiv`：card_equiv (e : α ≃ β) (hst : forall i, i in s ↔ e i 
in t) : #s = #t
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.prodCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_1
1} {β₂ : Type u_12} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂),   ⇑(e₁.prodCongr e₂) = Prod.m
ap ⇑e₁ ⇑e₂
· 使用定理 `Equiv.inv_apply`：∀ (G : Type u_14) [inst : InvolutiveInv G], ⇑(Equiv.inv
 G) = Inv.inv
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma card_div_eq (A B : Finset G) (x : G) :
    #{ab ∈ A ×ˢ B | ab.1 / ab.2 = x} = A.convolution B⁻¹ x :=
  Finset.card_equiv ((Equiv.refl _).prodCongr (.inv _)) (by simp [div_eq_mul_inv])

@[to_additive card_add_neg_eq_addConvolution_neg]
/-
**Finset.card_mul_inv_eq_convolution_inv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_mul_inv_eq_convolution_inv (A B : Finset G) (x : G) : #{ab in A ×ˢ B 
| ab.1 * ab.2⁻¹ = x} = A.convolution B⁻¹ x
参数：A B : Finset G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_nbij'`：card_nbij' (i : α -> β) (j : β -> α) (hi : Set.MapsTo
 i s t) (hj : Set.MapsTo j t s) (left_inv : Set.LeftInvOn j i s) (right_inv : Se
t.Right…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.LeftInvOn.eq_1`：∀ {α : Type u} {β : Type v} (g : β → α) (f : α → β) 
(s : Set α), Set.LeftInvOn g f s = ∀ ⦃x : α⦄, x ∈ s → g (f x) = x
-/
lemma card_mul_inv_eq_convolution_inv (A B : Finset G) (x : G) :
    #{ab ∈ A ×ˢ B | ab.1 * ab.2⁻¹ = x} = A.convolution B⁻¹ x :=
  card_nbij' (fun ab => (ab.1, ab.2⁻¹)) (fun ab => (ab.1, ab.2⁻¹))
    (by simp [Set.MapsTo]) (by simp [Set.MapsTo])
    (by simp [Set.LeftInvOn]) (by simp [Set.LeftInvOn])

@[to_additive (attr := simp) addConvolution_pos]
/-
**Finset.convolution_pos** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：convolution_pos : 0 < A.convolution B x ↔ x in A * B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma convolution_pos : 0 < A.convolution B x ↔ x ∈ A * B := by
  aesop (add simp [convolution, Finset.Nonempty, mem_mul])

@[to_additive addConvolution_ne_zero]
/-
**Finset.convolution_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：convolution_ne_zero : A.convolution B x != 0 ↔ x in A * B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma convolution_ne_zero : A.convolution B x ≠ 0 ↔ x ∈ A * B := by
  suffices A.convolution B x ≠ 0 ↔ 0 < A.convolution B x by simp [this]
  lia

@[to_additive (attr := simp) addConvolution_eq_zero]
/-
**Finset.convolution_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：convolution_eq_zero : A.convolution B x = 0 ↔ x ∉ A * B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma convolution_eq_zero : A.convolution B x = 0 ↔ x ∉ A * B := by
  simp [← convolution_ne_zero]

@[to_additive addConvolution_le_card_left]
/-
**Finset.convolution_le_card_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：convolution_le_card_left : A.convolution B x <= #A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `Finset.card_inter_smul`：card_inter_smul (A B : Finset G) (x : G) : #(A i
nter (x • B)) = A.convolution B⁻¹ x
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
-/
lemma convolution_le_card_left : A.convolution B x ≤ #A := by
  rw [← inv_inv B, ← card_inter_smul]
  exact card_le_card inter_subset_left

@[to_additive addConvolution_le_card_right]
/-
**Finset.convolution_le_card_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：convolution_le_card_right : A.convolution B x <= #B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `Finset.card_smul_inter`：card_smul_inter (A B : Finset G) (x : G) : #((x 
• A) inter B) = A.convolution B⁻¹ x⁻¹
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
-/
lemma convolution_le_card_right : A.convolution B x ≤ #B := by
  rw [← inv_inv B, ← inv_inv x, ← card_smul_inter, card_inv]
  exact card_le_card inter_subset_right

@[to_additive (attr := simp) addConvolution_neg]
/-
**Finset.convolution_inv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：convolution_inv (A B : Finset G) (x : G) : A.convolution B x⁻¹ = B⁻¹.convo
lution A⁻¹ x
参数：A B : Finset G；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `Finset.card_smul_inter`：card_smul_inter (A B : Finset G) (x : G) : #((x 
• A) inter B) = A.convolution B⁻¹ x⁻¹
· 使用引理 `Finset.card_inter_smul`：card_inter_smul (A B : Finset G) (x : G) : #(A i
nter (x • B)) = A.convolution B⁻¹ x
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
-/
lemma convolution_inv (A B : Finset G) (x : G) : A.convolution B x⁻¹ = B⁻¹.convolution A⁻¹ x := by
  nth_rw 1 [← inv_inv B]
  rw [← card_smul_inter, ← card_inter_smul, inter_comm]

@[to_additive (attr := simp) op_vadd_addConvolution_eq_addConvolution_vadd]
/-
**Finset.op_smul_convolution_eq_convolution_smul** 是 Mathlib 中的一个引理，位于命名空间 `Fins
et`。
形式化陈述：op_smul_convolution_eq_convolution_smul (A B : Finset G) (s : G) : (A <• s
).convolution B = A.convolution (s • B)
参数：A B : Finset G；s : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `Finset.inv_smul_finset_distrib`：inv_smul_finset_distrib (a : α) (s : Fin
set α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹
· 使用引理 `Finset.card_inter_smul`：card_inter_smul (A B : Finset G) (x : G) : #(A i
nter (x • B)) = A.convolution B⁻¹ x
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_smul_finset`：card_smul_finset (a : α) (s : Finset β) : (a • 
s).card = s.card
· 使用定理 `Finset.smul_finset_inter`：smul_finset_inter : a • (s inter t) = a • s in
ter a • t
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma op_smul_convolution_eq_convolution_smul (A B : Finset G) (s : G) :
    (A <• s).convolution B = A.convolution (s • B) := funext fun x => by
  nth_rw 1 [← inv_inv B, ← inv_inv (s • B), inv_smul_finset_distrib s B, ← card_inter_smul,
    ← card_inter_smul, smul_comm]
  simp [← card_smul_finset (op s) (A ∩ _), smul_finset_inter]

@[to_additive (attr := simp) vadd_addConvolution_eq_addConvolution_neg_add]
/-
**Finset.smul_convolution_eq_convolution_inv_mul** 是 Mathlib 中的一个引理，位于命名空间 `Fins
et`。
形式化陈述：smul_convolution_eq_convolution_inv_mul (A B : Finset G) (s x : G) : (s •>
 A).convolution B x = A.convolution B (s⁻¹ * x)
参数：A B : Finset G；s x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `Finset.card_smul_inter`：card_smul_inter (A B : Finset G) (x : G) : #((x 
• A) inter B) = A.convolution B⁻¹ x⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
lemma smul_convolution_eq_convolution_inv_mul (A B : Finset G) (s x : G) :
    (s •> A).convolution B x = A.convolution B (s⁻¹ * x) := by
  nth_rw 1 [← inv_inv x, ← inv_inv (s⁻¹ * x)]
  rw [← inv_inv B, ← card_smul_inter, ← card_smul_inter, mul_inv_rev, inv_inv, smul_smul]

@[to_additive (attr := simp) addConvolution_op_vadd_eq_addConvolution_add_neg]
/-
**Finset.convolution_op_smul_eq_convolution_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 `F
inset`。
形式化陈述：convolution_op_smul_eq_convolution_mul_inv (A B : Finset G) (s x : G) : A.
convolution (B <• s) x = A.convolution B (x * s⁻¹)
参数：A B : Finset G；s x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `Finset.inv_op_smul_finset_distrib`：inv_op_smul_finset_distrib (a : α) (s
 : Finset α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹
· 使用引理 `Finset.card_inter_smul`：card_inter_smul (A B : Finset G) (x : G) : #(A i
nter (x • B)) = A.convolution B⁻¹ x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
-/
lemma convolution_op_smul_eq_convolution_mul_inv (A B : Finset G) (s x : G) :
    A.convolution (B <• s) x = A.convolution B (x * s⁻¹) := by
  nth_rw 2 [← inv_inv B]
  rw [← inv_inv (B <• s), inv_op_smul_finset_distrib, ← card_inter_smul, ← card_inter_smul,
    smul_smul]

variable [Fintype G]

@[to_additive (attr := simp) univ_addConvolution]
/-
**Finset.univ_convolution** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：univ_convolution (B : Finset G) (a : G) : univ.convolution B a = #B
参数：B : Finset G；a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.univ_inter`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), Finset.univ ∩ s = s
· 使用定理 `Finset.card_smul_finset`：card_smul_finset (a : α) (s : Finset β) : (a • 
s).card = s.card
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma univ_convolution (B : Finset G) (a : G) : univ.convolution B a = #B := by
  simp [← card_inter_smul_inv]

@[to_additive (attr := simp) addConvolution_univ]
/-
**Finset.convolution_univ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：convolution_univ (A : Finset G) (a : G) : A.convolution univ a = #A
参数：A : Finset G；a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.inv_univ`：inv_univ [Fintype α] : (univ : Finset α)⁻¹ = univ
· 使用定理 `Finset.smul_finset_univ`：smul_finset_univ [Fintype β] : a • (univ : Fins
et β) = univ
· 使用定理 `Finset.inter_univ`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : Decidab
leEq α] (s : Finset α), s ∩ Finset.univ = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convolution_univ (A : Finset G) (a : G) : A.convolution univ a = #A := by
  simp [← card_inter_smul_inv]

end Finset

