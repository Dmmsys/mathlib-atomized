/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Ring.Nat

/-!
# e-transforms

e-transforms are a family of transformations of pairs of finite sets that aim to reduce the size
of the sumset while keeping some invariant the same. This file defines a few of them, to be used
as internals of other proofs.

## Main declarations

* `Finset.mulDysonETransform`: The Dyson e-transform. Replaces `(s, t)` by
  `(s ∪ e • t, t ∩ e⁻¹ • s)`. The additive version preserves `|s ∩ [1, m]| + |t ∩ [1, m - e]|`.
* `Finset.mulETransformLeft`/`Finset.mulETransformRight`: Replace `(s, t)` by
  `(s ∩ s • e, t ∪ e⁻¹ • t)` and `(s ∪ s • e, t ∩ e⁻¹ • t)`. Preserve (together) the sum of
  the cardinalities (see `Finset.MulETransform.card`). In particular, one of the two transforms
  increases the sum of the cardinalities and the other one decreases it. See
  `le_or_lt_of_add_le_add` and around.

## TODO

Prove the invariance property of the Dyson e-transform.
-/

@[expose] public section


open MulOpposite

open scoped Pointwise

variable {α : Type*} [DecidableEq α]

namespace Finset

/-! ### Dyson e-transform -/


section CommGroup

variable [CommGroup α] (e : α) (x : Finset α × Finset α)

/-- The **Dyson e-transform**. Turns `(s, t)` into `(s ∪ e • t, t ∩ e⁻¹ • s)`. This reduces the
product of the two sets. -/
@[to_additive (attr := simps) /-- The **Dyson e-transform**.
Turns `(s, t)` into `(s ∪ e +ᵥ t, t ∩ -e +ᵥ s)`. This reduces the sum of the two sets. -/]
/-
**Finset.mulDysonETransform** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：mulDysonETransform : Finset α × Finset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulDysonETransform : Finset α × Finset α :=
  (x.1 ∪ e • x.2, x.2 ∩ e⁻¹ • x.1)

@[to_additive]
/-
**Finset.mulDysonETransform.subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset.mulDysonETr
ansform`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : CommGroup α] (e : α) (x 
: Finset α × Finset α),   (Finset.mulDysonETransform e x).1 * (Finset.mulDysonET
ransform e x).2 ⊆ x.1 * x.2
参数：e : α；x : Finset α × Finset α；Finset.mulDysonETransform e x；Finset.mulDysonET
ransform e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.union_mul_inter_subset_union`：union_mul_inter_subset_union : (s₁ 
union s₂) * (t₁ inter t₂) subseteq s₁ * t₁ union s₂ * t₂
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mulDysonETransform.subset :
    (mulDysonETransform e x).1 * (mulDysonETransform e x).2 ⊆ x.1 * x.2 := by
  refine union_mul_inter_subset_union.trans (union_subset Subset.rfl ?_)
  rw [mul_smul_comm, smul_mul_assoc, inv_smul_smul, mul_comm]

set_option backward.defeqAttrib.useBackward true in
@[to_additive]
/-
**Finset.mulDysonETransform.card** 是 Mathlib 中的一个定理，位于命名空间 `Finset.mulDysonETran
sform`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : CommGroup α] (e : α) (x 
: Finset α × Finset α),   (Finset.mulDysonETransform e x).1.card + (Finset.mulDy
sonETransform e x).2.card = x.1.card + x.2.card
参数：e : α；x : Finset α × Finset α；Finset.mulDysonETransform e x；Finset.mulDysonET
ransform e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_smul_finset`：card_smul_finset (a : α) (s : Finset β) : (a • 
s).card = s.card
· 使用定理 `Finset.smul_finset_inter`：smul_finset_inter : a • (s inter t) = a • s in
ter a • t
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.card_union_add_card_inter`：card_union_add_card_inter (s t : Finse
t α) : #(s union t) + #(s inter t) = #s + #t
-/
theorem mulDysonETransform.card :
    (mulDysonETransform e x).1.card + (mulDysonETransform e x).2.card = x.1.card + x.2.card := by
  dsimp
  rw [← card_smul_finset e (_ ∩ _), smul_finset_inter, smul_inv_smul, inter_comm,
    card_union_add_card_inter, card_smul_finset]

set_option backward.defeqAttrib.useBackward true in
@[to_additive (attr := simp)]
/-
**Finset.mulDysonETransform_idem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mulDysonETransform_idem : mulDysonETransform e (mulDysonETransform e x) = 
mulDysonETransform e x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.smul_finset_inter`：smul_finset_inter : a • (s inter t) = a • s in
ter a • t
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.union_eq_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fin
set α}, s ∪ t = s ↔ t ⊆ s
· 使用定理 `Finset.inter_subset_union`：inter_subset_union : s inter t subseteq s uni
on t
· 使用引理 `Finset.smul_finset_union`：smul_finset_union : a • (s₁ union s₂) = a • s₁
 union a • s₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用定理 `Finset.inter_eq_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fin
set α}, s ∩ t = s ↔ s ⊆ t
-/
theorem mulDysonETransform_idem :
    mulDysonETransform e (mulDysonETransform e x) = mulDysonETransform e x := by
  ext : 1 <;> dsimp
  · rw [smul_finset_inter, smul_inv_smul, inter_comm, union_eq_left]
    exact inter_subset_union
  · rw [smul_finset_union, inv_smul_smul, union_comm, inter_eq_left]
    exact inter_subset_union

variable {e x}

set_option backward.defeqAttrib.useBackward true in
@[to_additive]
/-
**Finset.mulDysonETransform.smul_finset_snd_subset_fst** 是 Mathlib 中的一个定理，位于命名空间
 `Finset.mulDysonETransform`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : CommGroup α] {e : α} {x 
: Finset α × Finset α},   e • (Finset.mulDysonETransform e x).2 ⊆ (Finset.mulDys
onETransform e x).1
参数：Finset.mulDysonETransform e x；Finset.mulDysonETransform e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.smul_finset_inter`：smul_finset_inter : a • (s inter t) = a • s in
ter a • t
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Finset.inter_comm`：inter_comm (s₁ s₂ : Finset α) : s₁ inter s₂ = s₂ inte
r s₁
· 使用定理 `Finset.inter_subset_union`：inter_subset_union : s inter t subseteq s uni
on t
-/
theorem mulDysonETransform.smul_finset_snd_subset_fst :
    e • (mulDysonETransform e x).2 ⊆ (mulDysonETransform e x).1 := by
  dsimp
  rw [smul_finset_inter, smul_inv_smul, inter_comm]
  exact inter_subset_union

end CommGroup

/-!
### Two unnamed e-transforms

The following two transforms both reduce the product/sum of the two sets. Further, one of them must
decrease the sum of the size of the sets (and then the other increases it).

This pair of transforms doesn't seem to be named in the literature. It is used by Sanders in his
bound on Roth numbers, and by DeVos in his proof of Cauchy-Davenport.
-/


section Group

variable [Group α] (e : α) (x : Finset α × Finset α)

/-- An **e-transform**. Turns `(s, t)` into `(s ∩ s • e, t ∪ e⁻¹ • t)`. This reduces the
product of the two sets. -/
@[to_additive (attr := simps) /-- An **e-transform**.
Turns `(s, t)` into `(s ∩ s +ᵥ e, t ∪ -e +ᵥ t)`. This reduces the sum of the two sets. -/]
/-
**Finset.mulETransformLeft** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：mulETransformLeft : Finset α × Finset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulETransformLeft : Finset α × Finset α :=
  (x.1 ∩ op e • x.1, x.2 ∪ e⁻¹ • x.2)

/-- An **e-transform**. Turns `(s, t)` into `(s ∪ s • e, t ∩ e⁻¹ • t)`. This reduces the
product of the two sets. -/
@[to_additive (attr := simps) /-- An **e-transform**.
Turns `(s, t)` into `(s ∪ s +ᵥ e, t ∩ -e +ᵥ t)`. This reduces the sum of the two sets. -/]
/-
**Finset.mulETransformRight** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：mulETransformRight : Finset α × Finset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulETransformRight : Finset α × Finset α :=
  (x.1 ∪ op e • x.1, x.2 ∩ e⁻¹ • x.2)

@[to_additive (attr := simp)]
/-
**Finset.mulETransformLeft_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mulETransformLeft_one : mulETransformLeft 1 x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.inter_self`：inter_self (s : Finset α) : s inter s = s
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Finset.union_idempotent`：union_idempotent (s : Finset α) : s union s = s
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulETransformLeft_one : mulETransformLeft 1 x = x := by simp [mulETransformLeft]

@[to_additive (attr := simp)]
/-
**Finset.mulETransformRight_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mulETransformRight_one : mulETransformRight 1 x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.union_idempotent`：union_idempotent (s : Finset α) : s union s = s
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Finset.inter_self`：inter_self (s : Finset α) : s inter s = s
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulETransformRight_one : mulETransformRight 1 x = x := by simp [mulETransformRight]

@[to_additive]
/-
**Finset.mulETransformLeft.fst_mul_snd_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset.
mulETransformLeft`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Group α] (e : α) (x : Fi
nset α × Finset α),   (Finset.mulETransformLeft e x).1 * (Finset.mulETransformLe
ft e x).2 ⊆ x.1 * x.2
参数：e : α；x : Finset α × Finset α；Finset.mulETransformLeft e x；Finset.mulETransfo
rmLeft e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.inter_mul_union_subset_union`：inter_mul_union_subset_union : s₁ i
nter s₂ * (t₁ union t₂) subseteq s₁ * t₁ union s₂ * t₂
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.op_smul_finset_mul_eq_mul_smul_finset`：op_smul_finset_mul_eq_mul_
smul_finset (a : α) (s : Finset α) (t : Finset α) : op a • s * t = s * a • t
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mulETransformLeft.fst_mul_snd_subset :
    (mulETransformLeft e x).1 * (mulETransformLeft e x).2 ⊆ x.1 * x.2 := by
  refine inter_mul_union_subset_union.trans (union_subset Subset.rfl ?_)
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul]

@[to_additive]
/-
**Finset.mulETransformRight.fst_mul_snd_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset
.mulETransformRight`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Group α] (e : α) (x : Fi
nset α × Finset α),   (Finset.mulETransformRight e x).1 * (Finset.mulETransformR
ight e x).2 ⊆ x.1 * x.2
参数：e : α；x : Finset α × Finset α；Finset.mulETransformRight e x；Finset.mulETransf
ormRight e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.union_mul_inter_subset_union`：union_mul_inter_subset_union : (s₁ 
union s₂) * (t₁ inter t₂) subseteq s₁ * t₁ union s₂ * t₂
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `Finset.Subset.rfl`：∀ {α : Type u_1} {s : Finset α}, s ⊆ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.op_smul_finset_mul_eq_mul_smul_finset`：op_smul_finset_mul_eq_mul_
smul_finset (a : α) (s : Finset α) (t : Finset α) : op a • s * t = s * a • t
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mulETransformRight.fst_mul_snd_subset :
    (mulETransformRight e x).1 * (mulETransformRight e x).2 ⊆ x.1 * x.2 := by
  refine union_mul_inter_subset_union.trans (union_subset Subset.rfl ?_)
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul]

@[to_additive]
/-
**Finset.mulETransformLeft.card** 是 Mathlib 中的一个定理，位于命名空间 `Finset.mulETransformL
eft`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Group α] (e : α) (x : Fi
nset α × Finset α),   (Finset.mulETransformLeft e x).1.card + (Finset.mulETransf
ormRight e x).1.card = 2 * x.1.card
参数：e : α；x : Finset α × Finset α；Finset.mulETransformLeft e x；Finset.mulETransfo
rmRight e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_inter_add_card_union`：card_inter_add_card_union (s t : Finse
t α) : #(s inter t) + #(s union t) = #s + #t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_smul_finset`：card_smul_finset (a : α) (s : Finset β) : (a • 
s).card = s.card
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem mulETransformLeft.card :
    (mulETransformLeft e x).1.card + (mulETransformRight e x).1.card = 2 * x.1.card :=
  (card_inter_add_card_union _ _).trans <| by rw [card_smul_finset, two_mul]

@[to_additive]
/-
**Finset.mulETransformRight.card** 是 Mathlib 中的一个定理，位于命名空间 `Finset.mulETransform
Right`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Group α] (e : α) (x : Fi
nset α × Finset α),   (Finset.mulETransformLeft e x).2.card + (Finset.mulETransf
ormRight e x).2.card = 2 * x.2.card
参数：e : α；x : Finset α × Finset α；Finset.mulETransformLeft e x；Finset.mulETransfo
rmRight e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_union_add_card_inter`：card_union_add_card_inter (s t : Finse
t α) : #(s union t) + #(s inter t) = #s + #t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_smul_finset`：card_smul_finset (a : α) (s : Finset β) : (a • 
s).card = s.card
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem mulETransformRight.card :
    (mulETransformLeft e x).2.card + (mulETransformRight e x).2.card = 2 * x.2.card :=
  (card_union_add_card_inter _ _).trans <| by rw [card_smul_finset, two_mul]

/-- This statement is meant to be combined with `le_or_lt_of_add_le_add` and similar lemmas. -/
@[to_additive AddETransform.card /-- This statement is meant to be combined with
`le_or_lt_of_add_le_add` and similar lemmas. -/]
/-
**Finset.MulETransform.card** 是 Mathlib 中的一个定理，位于命名空间 `Finset.MulETransform`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Group α] (e : α) (x : Fi
nset α × Finset α),   (Finset.mulETransformLeft e x).1.card + (Finset.mulETransf
ormLeft e x).2.card +       ((Finset.mulETransformRight e x).1.card + (Finset.mu
lETransformRight e x).2.card) =     x.1.card + x.2.card + (x.1.card + x.2.card)
参数：e : α；x : Finset α × Finset α；Finset.mulETransformLeft e x；Finset.mulETransfo
rmLeft e x；(Finset.mulETransformRight e x).1.card + (Finset.mulETransformRight e
 x).2.card；x.1.card + x.2.card。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `Finset.mulETransformLeft.card`：∀ {α : Type u_1} [inst : DecidableEq α] [
inst_1 : Group α] (e : α) (x : Finset α × Finset α),   (Finset.mulETransformLeft
 e x).1.card + (Fin…
· 使用定理 `Finset.mulETransformRight.card`：∀ {α : Type u_1} [inst : DecidableEq α] 
[inst_1 : Group α] (e : α) (x : Finset α × Finset α),   (Finset.mulETransformLef
t e x).2.card + (Fin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
protected theorem MulETransform.card :
    (mulETransformLeft e x).1.card + (mulETransformLeft e x).2.card +
        ((mulETransformRight e x).1.card + (mulETransformRight e x).2.card) =
      x.1.card + x.2.card + (x.1.card + x.2.card) := by
  rw [add_add_add_comm, mulETransformLeft.card, mulETransformRight.card, ← mul_add, two_mul]

end Group

section CommGroup

variable [CommGroup α] (e : α) (x : Finset α × Finset α)

@[to_additive (attr := simp)]
/-
**Finset.mulETransformLeft_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mulETransformLeft_inv : mulETransformLeft e⁻¹ x = (mulETransformRight e x.
swap).swap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulETransformLeft_inv : mulETransformLeft e⁻¹ x = (mulETransformRight e x.swap).swap := by
  simp [-op_inv, op_smul_eq_smul, mulETransformLeft, mulETransformRight]

@[to_additive (attr := simp)]
/-
**Finset.mulETransformRight_inv** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mulETransformRight_inv : mulETransformRight e⁻¹ x = (mulETransformLeft e x
.swap).swap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulETransformRight_inv : mulETransformRight e⁻¹ x = (mulETransformLeft e x.swap).swap := by
  simp [-op_inv, op_smul_eq_smul, mulETransformLeft, mulETransformRight]

end CommGroup

end Finset

