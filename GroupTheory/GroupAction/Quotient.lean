/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Properties of group actions involving quotient groups

This file proves properties of group actions which use the quotient group construction, notably
* the orbit-stabilizer theorem `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`
* the class formula `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'`
* Burnside's lemma `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`,

as well as their analogues for additive groups.
-/

@[expose] public section

assert_not_exists Cardinal

universe u v w

variable {G : Type u} {X : Type v}

open Function

open scoped commutatorElement

namespace MulAction

variable [Group G]

section QuotientAction

open Subgroup MulOpposite QuotientGroup

variable (X) [Monoid X] [MulAction X G] (H : Subgroup G)

/-- A typeclass for when a `MulAction X G` descends to the quotient `G ⧸ H`. -/
/-
**MulAction.QuotientAction** 是 Mathlib 中的一个归纳类型，位于命名空间 `MulAction`。
形式化陈述：{G : Type u} → (X : Type v) → [inst : Group G] → [inst_1 : Monoid X] → [Mu
lAction X G] → Subgroup G → Prop
参数：X : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for when a `MulAction X G` descends to the quotient `G ⧸ H`.
-/
class QuotientAction : Prop where
  /-- The action fulfils a normality condition on products that lie in `H`.
    This ensures that the action descends to an action on the quotient `G ⧸ H`. -/
  inv_mul_mem : ∀ (b : X) {a a' : G}, a⁻¹ * a' ∈ H → (b • a)⁻¹ * b • a' ∈ H

/-- A typeclass for when an `AddAction X G` descends to the quotient `G ⧸ H`. -/
/-
**MulAction._root_.AddAction.QuotientAction** 是 Mathlib 中的一个类，位于命名空间 `MulAction`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for when an `AddAction X G` descends to the quotient `G ⧸ H`.
-/
class _root_.AddAction.QuotientAction {G : Type u} (X : Type v) [AddGroup G] [AddMonoid X]
  [AddAction X G] (H : AddSubgroup G) : Prop where
  /-- The action fulfils a normality condition on summands that lie in `H`.
    This ensures that the action descends to an action on the quotient `G ⧸ H`. -/
  inv_mul_mem : ∀ (x : X) {g g' : G}, -g + g' ∈ H → -(x +ᵥ g) + (x +ᵥ g') ∈ H

attribute [to_additive] MulAction.QuotientAction

@[to_additive]
/-
**MulAction.left_quotientAction** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
形式化陈述：left_quotientAction : QuotientAction G H
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
-/
instance left_quotientAction : QuotientAction G H :=
  ⟨fun _ _ _ _ => by rwa [smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]⟩

@[to_additive]
/-
**MulAction.right_quotientAction** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
形式化陈述：right_quotientAction : QuotientAction (normalizer H : Subgroup G).op H
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.smul_def`：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [ins
t_1 : MulAction G α] {S : Subgroup G} (g : ↥S) (m : α),   g • m = ↑g • m
· 使用引理 `MulOpposite.smul_eq_mul_unop`：MulOpposite.smul_eq_mul_unop [Mul α] (a : 
αᵐᵒᵖ) (b : α) : a • b = b * a.unop
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_normalizer_iff'`：mem_normalizer_iff' : g in normalizer H ↔ 
forall n, n * g in H ↔ g * n in H
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
instance right_quotientAction : QuotientAction (normalizer H : Subgroup G).op H :=
  ⟨fun b c _ _ => by
    rwa [smul_def, smul_def, smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, ← mul_assoc,
      mem_normalizer_iff'.mp b.prop, mul_assoc, mul_inv_cancel_left]⟩

@[to_additive]
/-
**MulAction.right_quotientAction'** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
形式化陈述：right_quotientAction' [hH : H.Normal] : QuotientAction Gᵐᵒᵖ H
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulOpposite.smul_eq_mul_unop`：MulOpposite.smul_eq_mul_unop [Mul α] (a : 
αᵐᵒᵖ) (b : α) : a • b = b * a.unop
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Subgroup.Normal.mem_comm_iff`：mem_comm_iff (nH : H.Normal) {a b : G} : a
 * b in H ↔ b * a in H
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
-/
instance right_quotientAction' [hH : H.Normal] : QuotientAction Gᵐᵒᵖ H :=
  ⟨fun _ _ _ _ => by
    rwa [smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, mul_assoc, hH.mem_comm_iff, mul_assoc,
      mul_inv_cancel_right]⟩

@[to_additive]
/-
**MulAction.quotient** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
形式化陈述：quotient [QuotientAction X H] : MulAction X (G ⧸ H) where smul b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
-/
instance quotient [QuotientAction X H] : MulAction X (G ⧸ H) where
  smul b :=
    Quotient.map' (b • ·) fun _ _ h =>
      leftRel_apply.mpr <| QuotientAction.inv_mul_mem b <| leftRel_apply.mp h
  one_smul q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (one_smul X a)
  mul_smul b b' q := Quotient.inductionOn' q fun a => congr_arg Quotient.mk'' (mul_smul b b' a)

variable {X}

@[to_additive (attr := simp)]
/-
**MulAction.Quotient.smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Quotient`。
形式化陈述：∀ {G : Type u} {X : Type v} [inst : Group G] [inst_1 : Monoid X] [inst_2 :
 MulAction X G] (H : Subgroup G)   [inst_3 : MulAction.QuotientAction X H] (b : 
X) (g : G), b • ↑g = ↑(b • g)
参数：H : Subgroup G；b : X；g : G；b • g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.smul_mk [QuotientAction X H] (b : X) (g : G) :
    (b • QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk (b • g) :=
  rfl

@[to_additive (attr := simp)]
/-
**MulAction.Quotient.smul_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Quotient`。
形式化陈述：∀ {G : Type u} {X : Type v} [inst : Group G] [inst_1 : Monoid X] [inst_2 :
 MulAction X G] (H : Subgroup G)   [inst_3 : MulAction.QuotientAction X H] (b : 
X) (g : G), b • ↑g = ↑(b • g)
参数：H : Subgroup G；b : X；g : G；b • g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Quotient.smul_coe [QuotientAction X H] (b : X) (g : G) :
    b • (g : G ⧸ H) = (↑(b • g) : G ⧸ H) :=
  rfl

@[to_additive (attr := simp)]
/-
**MulAction.Quotient.mk_smul_out** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Quotient`。
形式化陈述：∀ {G : Type u} {X : Type v} [inst : Group G] [inst_1 : Monoid X] [inst_2 :
 MulAction X G] (H : Subgroup G)   [inst_3 : MulAction.QuotientAction X H] (b : 
X) (q : G ⧸ H), ↑(b • Quotient.out q) = b • q
参数：H : Subgroup G；b : X；q : G ⧸ H；b • Quotient.out q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.Quotient.smul_mk`：∀ {G : Type u} {X : Type v} [inst : Group G]
 [inst_1 : Monoid X] [inst_2 : MulAction X G] (H : Subgroup G)   [inst_3 : MulAc
tion.QuotientAct…
· 使用定理 `QuotientGroup.out_eq'`：out_eq' (a : α ⧸ s) : mk a.out = a
-/
theorem Quotient.mk_smul_out [QuotientAction X H] (b : X) (q : G ⧸ H) :
    QuotientGroup.mk (b • q.out) = b • q := by rw [← Quotient.smul_mk, QuotientGroup.out_eq']

@[to_additive]
/-
**MulAction.Quotient.coe_smul_out** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.Quotient`
。
形式化陈述：∀ {G : Type u} {X : Type v} [inst : Group G] [inst_1 : Monoid X] [inst_2 :
 MulAction X G] (H : Subgroup G)   [inst_3 : MulAction.QuotientAction X H] (b : 
X) (q : G ⧸ H), ↑(b • Quotient.out q) = b • q
参数：H : Subgroup G；b : X；q : G ⧸ H；b • Quotient.out q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.Quotient.mk_smul_out`：∀ {G : Type u} {X : Type v} [inst : Grou
p G] [inst_1 : Monoid X] [inst_2 : MulAction X G] (H : Subgroup G)   [inst_3 : M
ulAction.QuotientAct…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Quotient.coe_smul_out [QuotientAction X H] (b : X) (q : G ⧸ H) : ↑(b • q.out) = b • q := by
  simp
/-
**MulAction._root_.QuotientGroup.out_conj_pow_minimalPeriod_mem** 是 Mathlib 中的一个
定理，位于命名空间 `MulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.QuotientGroup.out_conj_pow_minimalPeriod_mem (g : G) (q : G ⧸ H) :
    q.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q * q.out ∈ H := by
  rw [mul_assoc, ← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, Quotient.mk_smul_out,
    eq_comm, pow_smul_eq_iff_minimalPeriod_dvd]

end QuotientAction

open QuotientGroup

/-- The canonical map to the left cosets. -/
/-
**MulAction._root_.MulActionHom.toQuotient** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map to the left cosets.
-/
def _root_.MulActionHom.toQuotient (H : Subgroup G) : G →[G] G ⧸ H where
  toFun := (↑); map_smul' := Quotient.smul_coe H

@[simp]
/-
**MulAction._root_.MulActionHom.toQuotient_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulA
ction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulActionHom.toQuotient_apply (H : Subgroup G) (g : G) :
    MulActionHom.toQuotient H g = g :=
  rfl

@[to_additive (attr := simp)]
/-
**MulAction.coe_quotient_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：coe_quotient_smul {H : Subgroup G} [H.Normal] [SMul G X] [MulAction (G ⧸ H
) X] [IsScalarTower G (G ⧸ H) X] (g : G) (x : X) : (g : G ⧸ H) • x = g • x
参数：G ⧸ H；G ⧸ H；g : G；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `QuotientGroup.mk_one`：mk_one : ((1 : G) : Q) = 1
· 使用定理 `MulAction.Quotient.smul_coe`：∀ {G : Type u} {X : Type v} [inst : Group G
] [inst_1 : Monoid X] [inst_2 : MulAction X G] (H : Subgroup G)   [inst_3 : MulA
ction.QuotientAct…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem coe_quotient_smul {H : Subgroup G} [H.Normal] [SMul G X]
    [MulAction (G ⧸ H) X] [IsScalarTower G (G ⧸ H) X] (g : G) (x : X) :
    (g : G ⧸ H) • x = g • x := by
  rw [← smul_one_smul (G ⧸ H) g x, ← QuotientGroup.mk_one, Quotient.smul_coe,
    smul_eq_mul, mul_one]

@[to_additive]
/-
**MulAction.mulLeftCosetsCompSubtypeVal** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
形式化陈述：mulLeftCosetsCompSubtypeVal (H I : Subgroup G) : MulAction I (G ⧸ H)
参数：H I : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulLeftCosetsCompSubtypeVal (H I : Subgroup G) : MulAction I (G ⧸ H) :=
  MulAction.compHom (G ⧸ H) (Subgroup.subtype I)

variable (G)
variable [MulAction G X] (x : X)

/-- The canonical map from the quotient of the stabilizer to the set. -/
@[to_additive /-- The canonical map from the quotient of the stabilizer to the set. -/]
/-
**MulAction.ofQuotientStabilizer** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：ofQuotientStabilizer (g : G ⧸ MulAction.stabilizer G x) : X
参数：g : G ⧸ MulAction.stabilizer G x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the quotient of the stabilizer to the set.
-/
def ofQuotientStabilizer (g : G ⧸ MulAction.stabilizer G x) : X :=
  Quotient.liftOn' g (· • x) fun g1 g2 H =>
    calc
      g1 • x = g1 • (g1⁻¹ * g2) • x := congr_arg _ (leftRel_apply.mp H).symm
      _ = g2 • x := by rw [smul_smul, mul_inv_cancel_left]

@[to_additive (attr := simp)]
/-
**MulAction.ofQuotientStabilizer_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：ofQuotientStabilizer_mk (g : G) : ofQuotientStabilizer G x (QuotientGroup.
mk g) = g • x
参数：g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofQuotientStabilizer_mk (g : G) : ofQuotientStabilizer G x (QuotientGroup.mk g) = g • x :=
  rfl

@[to_additive]
/-
**MulAction.ofQuotientStabilizer_mem_orbit** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`
。
形式化陈述：ofQuotientStabilizer_mem_orbit (g) : ofQuotientStabilizer G x g in orbit G
 x
参数：g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem ofQuotientStabilizer_mem_orbit (g) : ofQuotientStabilizer G x g ∈ orbit G x :=
  Quotient.inductionOn' g fun g => ⟨g, rfl⟩

@[to_additive]
/-
**MulAction.ofQuotientStabilizer_smul** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：ofQuotientStabilizer_smul (g : G) (g' : G ⧸ MulAction.stabilizer G x) : of
QuotientStabilizer G x (g • g') = g • ofQuotientStabilizer G x g'
参数：g : G；g' : G ⧸ MulAction.stabilizer G x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
theorem ofQuotientStabilizer_smul (g : G) (g' : G ⧸ MulAction.stabilizer G x) :
    ofQuotientStabilizer G x (g • g') = g • ofQuotientStabilizer G x g' :=
  Quotient.inductionOn' g' fun _ => mul_smul _ _ _

@[to_additive]
/-
**MulAction.injective_ofQuotientStabilizer** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`
。
形式化陈述：injective_ofQuotientStabilizer : Function.Injective (ofQuotientStabilizer 
G x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂'`：∀ {α : Sort u_1} {β : Sort u_2} {s₁ : Setoid α} 
{s₂ : Setoid β} {p : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q₂ 
: Quotient s…
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
theorem injective_ofQuotientStabilizer : Function.Injective (ofQuotientStabilizer G x) :=
  fun y₁ y₂ =>
  Quotient.inductionOn₂' y₁ y₂ fun g₁ g₂ (H : g₁ • x = g₂ • x) =>
    Quotient.sound' <| by
      rw [leftRel_apply]
      change (g₁⁻¹ * g₂) • x = x
      rw [mul_smul, ← H, inv_smul_smul]

/-- **Orbit-stabilizer theorem**. -/
@[to_additive /-- Orbit-stabilizer theorem. -/]
/-
**MulAction.orbitEquivQuotientStabilizer** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：orbitEquivQuotientStabilizer (b : X) : orbit G b ≃ G ⧸ stabilizer G b
参数：b : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MulAction.ofQuotientStabilizer_mem_orbit`：ofQuotientStabilizer_mem_orbit
 (g) : ofQuotientStabilizer G x g in orbit G x

--- 原说明 ---
**Orbit-stabilizer theorem**.
-/
noncomputable def orbitEquivQuotientStabilizer (b : X) : orbit G b ≃ G ⧸ stabilizer G b :=
  Equiv.symm <|
    Equiv.ofBijective (fun g => ⟨ofQuotientStabilizer G b g, ofQuotientStabilizer_mem_orbit G b g⟩)
      ⟨fun x y hxy => injective_ofQuotientStabilizer G b (by convert! congr_arg Subtype.val hxy),
        fun ⟨_, ⟨g, hgb⟩⟩ => ⟨g, Subtype.ext hgb⟩⟩

/-- Orbit-stabilizer theorem. -/
@[to_additive AddAction.orbitProdStabilizerEquivAddGroup /-- Orbit-stabilizer theorem. -/]
/-
**MulAction.orbitProdStabilizerEquivGroup** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：orbitProdStabilizerEquivGroup (b : X) : orbit G b × stabilizer G b ≃ G
参数：b : X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Orbit-stabilizer theorem.
-/
noncomputable def orbitProdStabilizerEquivGroup (b : X) : orbit G b × stabilizer G b ≃ G :=
  (Equiv.prodCongr (orbitEquivQuotientStabilizer G _) (Equiv.refl _)).trans
    Subgroup.groupEquivQuotientProdSubgroup.symm

/-- Orbit-stabilizer theorem. -/
@[to_additive AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup
/-- Orbit-stabilizer theorem. -/]
/-
**MulAction.card_orbit_mul_card_stabilizer_eq_card_group** 是 Mathlib 中的一个定理，位于命名
空间 `MulAction`。
形式化陈述：card_orbit_mul_card_stabilizer_eq_card_group (b : X) [Fintype G] [Fintype 
<| orbit G b] [Fintype <| stabilizer G b] : Fintype.card (orbit G b) * Fintype.c
ard (stabilizer G b) = Fintype.card G
参数：b : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem card_orbit_mul_card_stabilizer_eq_card_group (b : X) [Fintype G] [Fintype <| orbit G b]
    [Fintype <| stabilizer G b] :
    Fintype.card (orbit G b) * Fintype.card (stabilizer G b) = Fintype.card G := by
  rw [← Fintype.card_prod, Fintype.card_congr (orbitProdStabilizerEquivGroup G b)]

@[to_additive (attr := simp)]
/-
**MulAction.orbitEquivQuotientStabilizer_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `M
ulAction`。
形式化陈述：orbitEquivQuotientStabilizer_symm_apply (b : X) (g : G) : ((orbitEquivQuot
ientStabilizer G b).symm g : X) = g • b
参数：b : X；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem orbitEquivQuotientStabilizer_symm_apply (b : X) (g : G) :
    ((orbitEquivQuotientStabilizer G b).symm g : X) = g • b :=
  rfl

@[to_additive (attr := simp)]
/-
**MulAction.stabilizer_quotient** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：stabilizer_quotient {G} [Group G] (H : Subgroup G) : MulAction.stabilizer 
G ((1 : G) : G ⧸ H) = H
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem stabilizer_quotient {G} [Group G] (H : Subgroup G) :
    MulAction.stabilizer G ((1 : G) : G ⧸ H) = H := by
  ext
  simp [QuotientGroup.eq]

variable (X)

local notation "Ω" => Quotient <| orbitRel G X

/-- **Class formula** : let `G` be a group acting on `X` and let `φ` be a function mapping each
orbit of `X` under this action (that is, each element of the quotient of `G` by the relation
`orbitRel G X`) to an element in this orbit. We provide a  (noncomputable) bijection between `X`
and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω : Ω`. In most cases you'll want `φ`
to be `Quotient.out`, so we provide `MulAction.selfEquivSigmaOrbitsQuotientStabilizer'` as a
special case. -/
@[to_additive
    /-- **Class formula** : let `G` be an additive group acting on `X` and let `φ` be a function
    mapping each orbit of `X` under this action (that is, each element of the quotient of `X` by
    the relation `orbitRel G X`) to an element in this orbit. This definition is a (noncomputable)
    bijection between `X` and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω : Ω`. In
    most cases you'll want `φ` to be `Quotient.out`, so we provide
      `AddAction.selfEquivSigmaOrbitsQuotientStabilizer'` as a special case. -/]
/-
**MulAction.selfEquivSigmaOrbitsQuotientStabilizer'** 是 Mathlib 中的一个定义，位于命名空间 `M
ulAction`。
形式化陈述：selfEquivSigmaOrbitsQuotientStabilizer' {φ : Ω -> X} (hφ : LeftInverse Quo
tient.mk'' φ) : X ≃ Σ ω : Ω, G ⧸ stabilizer G (φ ω)
参数：hφ : LeftInverse Quotient.mk'' φ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `MulAction.orbitRel.Quotient.orbit_eq_orbit_out`：∀ {G : Type u_1} {α : Ty
pe u_2} [inst : Group G] [inst_1 : MulAction G α] (x : MulAction.orbitRel.Quotie
nt G α)   {φ : MulAction.orbitRel.Qu…
-/
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer' {φ : Ω → X}
    (hφ : LeftInverse Quotient.mk'' φ) : X ≃ Σ ω : Ω, G ⧸ stabilizer G (φ ω) :=
  calc
    X ≃ Σ ω : Ω, orbitRel.Quotient.orbit ω := selfEquivSigmaOrbits' G X
    _ ≃ Σ ω : Ω, G ⧸ stabilizer G (φ ω) :=
      Equiv.sigmaCongrRight fun ω =>
        (Equiv.setCongr <| orbitRel.Quotient.orbit_eq_orbit_out _ hφ).trans <|
          orbitEquivQuotientStabilizer G (φ ω)

/-- **Class formula**. This is a special case of
`MulAction.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = Quotient.out`. -/
@[to_additive
      /-- **Class formula**. This is a special case of
      `AddAction.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = Quotient.out`. -/]
/-
**MulAction.selfEquivSigmaOrbitsQuotientStabilizer** 是 Mathlib 中的一个定义，位于命名空间 `Mu
lAction`。
形式化陈述：selfEquivSigmaOrbitsQuotientStabilizer : X ≃ Σ ω : Ω, G ⧸ stabilizer G ω.o
ut
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def selfEquivSigmaOrbitsQuotientStabilizer : X ≃ Σ ω : Ω, G ⧸ stabilizer G ω.out :=
  selfEquivSigmaOrbitsQuotientStabilizer' G X Quotient.out_eq'

/-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × Ω`, where `G` is a group acting on `X`
and `Ω = X/G` denotes the quotient of `X` by the relation `orbitRel G X`. -/
@[to_additive AddAction.sigmaFixedByEquivOrbitsProdAddGroup
      /-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
      `{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × Ω`, where `G` is an additive group
      acting on `X` and `Ω = X/G` denotes the quotient of `X` by the relation `orbitRel G X`. -/]
/-
**MulAction.sigmaFixedByEquivOrbitsProdGroup** 是 Mathlib 中的一个定义，位于命名空间 `MulActio
n`。
形式化陈述：sigmaFixedByEquivOrbitsProdGroup : (Σ g : G, fixedBy X g) ≃ Ω × G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
noncomputable def sigmaFixedByEquivOrbitsProdGroup : (Σ g : G, fixedBy X g) ≃ Ω × G :=
  calc
    (Σ g : G, fixedBy X g) ≃ { ab : G × X // ab.1 • ab.2 = ab.2 } :=
      (Equiv.subtypeProdEquivSigmaSubtype _).symm
    _ ≃ { ba : X × G // ba.2 • ba.1 = ba.1 } := (Equiv.prodComm G X).subtypeEquiv fun _ => Iff.rfl
    _ ≃ Σ b : X, stabilizer G b :=
      Equiv.subtypeProdEquivSigmaSubtype fun (b : X) a => a ∈ stabilizer G b
    _ ≃ Σ ωb : Σ ω : Ω, orbit G ω.out, stabilizer G (ωb.2 : X) :=
      (selfEquivSigmaOrbits G X).sigmaCongrLeft'
    _ ≃ Σ ω : Ω, Σ b : orbit G ω.out, stabilizer G (b : X) :=
      Equiv.sigmaAssoc fun (ω : Ω) (b : orbit G ω.out) => stabilizer G (b : X)
    _ ≃ Σ ω : Ω, Σ _ : orbit G ω.out, stabilizer G ω.out :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.sigmaCongrRight fun ⟨_, hb⟩ => (stabilizerEquivStabilizerOfOrbitRel hb).toEquiv
    _ ≃ Σ ω : Ω, orbit G ω.out × stabilizer G ω.out :=
      Equiv.sigmaCongrRight fun _ => Equiv.sigmaEquivProd _ _
    _ ≃ Σ _ : Ω, G := Equiv.sigmaCongrRight fun ω => orbitProdStabilizerEquivGroup G ω.out
    _ ≃ Ω × G := Equiv.sigmaEquivProd Ω G

/-- **Burnside's lemma** : given a finite group `G` acting on a type `X`, the sum the orders of the
stabilisers coincides with the number of orbits multiplied by the order of `G`. -/
@[to_additive (attr := wikidata Q1330377)
      AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
      /-- **Burnside's lemma** : given a finite additive group `G` acting on a type `X`,
      the sum the orders of the stabilisers coincides with the number of orbits multiplied by the
      order of `G`. -/]
/-
**MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group** 是 Mathlib 中的一个定理，位于
命名空间 `MulAction`。
形式化陈述：sum_card_fixedBy_eq_card_orbits_mul_card_group [Fintype G] [forall g : G, 
Fintype <| fixedBy X g] [Fintype Ω] : (∑ g : G, Fintype.card (fixedBy X g)) = Fi
ntype.card Ω * Fintype.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `Fintype.card_sigma`：∀ {ι : Type u_8} {α : ι → Type u_7} [inst : Fintype 
ι] [inst_1 : (i : ι) → Fintype (α i)],   Fintype.card (Sigma α) = ∑ i, Fintype.c
ard (α i…
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem sum_card_fixedBy_eq_card_orbits_mul_card_group [Fintype G] [∀ g : G, Fintype <| fixedBy X g]
    [Fintype Ω] : (∑ g : G, Fintype.card (fixedBy X g)) = Fintype.card Ω * Fintype.card G := by
  rw [← Fintype.card_prod, ← Fintype.card_sigma,
    Fintype.card_congr (sigmaFixedByEquivOrbitsProdGroup G X)]

@[to_additive]
/-
**MulAction.isPretransitive_quotient** 是 Mathlib 中的一个实例，位于命名空间 `MulAction`。
形式化陈述：isPretransitive_quotient (G) [Group G] (H : Subgroup G) : IsPretransitive 
G (G ⧸ H) where exists_smul_eq
参数：G；H : Subgroup G。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
-/
instance isPretransitive_quotient (G) [Group G] (H : Subgroup G) : IsPretransitive G (G ⧸ H) where
  exists_smul_eq := by
    { rintro ⟨x⟩ ⟨y⟩
      refine ⟨y * x⁻¹, QuotientGroup.eq.mpr ?_⟩
      simp only [smul_eq_mul, H.one_mem, inv_mul_cancel, inv_mul_cancel_right]}

variable {G}

@[to_additive]
/-
**MulAction.finite_quotient_of_pretransitive_of_finite_quotient** 是 Mathlib 中的一个
实例，位于命名空间 `MulAction`。
形式化陈述：finite_quotient_of_pretransitive_of_finite_quotient [IsPretransitive G X] 
{H : Subgroup G} [Finite (G ⧸ H)] : Finite orbitRel.Quotient H X
参数：G ⧸ H。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.rightRel_eq`：rightRel_eq : ⇑(rightRel s) = fun x y => y * 
x⁻¹ in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finite.of_surjective`：Finite.of_surjective {α β : Sort*} [Finite α] (f :
 α -> β) (H : Surjective f) : Finite β
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.surjective_liftOn'`：∀ {α : Sort u_1} {φ : Sort u_4} {s₁ : Setoi
d α} {f : α → φ} (h : ∀ (a b : α), s₁ a b → f a = f b),   (Function.Surjective f
un x => x.liftOn'…
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
· 使用引理 `MulAction.surjective_smul`：surjective_smul (x : α) : Surjective fun c : 
M => c • x
-/
instance finite_quotient_of_pretransitive_of_finite_quotient [IsPretransitive G X] {H : Subgroup G}
    [Finite (G ⧸ H)] : Finite <| orbitRel.Quotient H X := by
  rcases isEmpty_or_nonempty X with he | ⟨⟨b⟩⟩
  · exact Quotient.finite _
  · have h' : Finite (Quotient (rightRel H)) :=
      Finite.of_equiv _ (quotientRightRelEquivQuotientLeftRel _).symm
    let f : Quotient (rightRel H) → orbitRel.Quotient H X :=
      fun a ↦ Quotient.liftOn' a (fun g ↦ ⟦g • b⟧) fun g₁ g₂ r ↦ by
        replace r := Setoid.symm' _ r
        rw [rightRel_eq] at r
        simp only [Quotient.eq, orbitRel_apply, mem_orbit_iff]
        exact ⟨⟨g₁ * g₂⁻¹, r⟩, by simp [mul_smul]⟩
    exact Finite.of_surjective f ((Quotient.surjective_liftOn' _).2
      (Quotient.mk''_surjective.comp (MulAction.surjective_smul _ _)))

variable {X} in
/-- A bijection between the quotient of the action of a subgroup `H` on an orbit, and a
corresponding quotient expressed in terms of `Setoid.comap Subtype.val`. -/
@[to_additive /-- A bijection between the quotient of the action of an additive subgroup `H` on an
orbit, and a corresponding quotient expressed in terms of `Setoid.comap Subtype.val`. -/]
/-
**MulAction.equivSubgroupOrbitsSetoidComap** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`
。
形式化陈述：equivSubgroupOrbitsSetoidComap (H : Subgroup G) (ω : Ω) : orbitRel.Quotien
t H (orbitRel.Quotient.orbit ω) ≃ Quotient ((orbitRel H X).comap (Subtype.val : 
Quotient.mk (orbitRel G X) ⁻¹' {ω} -> X)) where toFun
参数：H : Subgroup G；ω : Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def equivSubgroupOrbitsSetoidComap (H : Subgroup G) (ω : Ω) :
    orbitRel.Quotient H (orbitRel.Quotient.orbit ω) ≃
      Quotient ((orbitRel H X).comap (Subtype.val : Quotient.mk (orbitRel G X) ⁻¹' {ω} → X)) where
  toFun := fun q ↦ q.liftOn' (fun x ↦ ⟦⟨↑x, by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    have hx := x.property
    rwa [orbitRel.Quotient.mem_orbit] at hx⟩⟧) fun a b h ↦ by
      simp only [← Quotient.eq, orbitRel.Quotient.subgroup_quotient_eq_iff] at h
      simp only [Quotient.eq] at h ⊢
      exact h
  invFun := fun q ↦ q.liftOn' (fun x ↦ ⟦⟨↑x, by
    have hx := x.property
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rwa [orbitRel.Quotient.mem_orbit, @Quotient.mk''_eq_mk]⟩⟧) fun a b h ↦ by
      rw [Setoid.comap_rel, ← Quotient.eq'', @Quotient.mk''_eq_mk] at h
      simp only [orbitRel.Quotient.subgroup_quotient_eq_iff]
      exact h
  left_inv := by
    simp only [LeftInverse]
    intro q
    induction q using Quotient.inductionOn'
    rfl
  right_inv := by
    simp only [Function.RightInverse, LeftInverse]
    intro q
    induction q using Quotient.inductionOn'
    rfl

/-- A bijection between the orbits under the action of a subgroup `H` on `X`, and the orbits
under the action of `H` on each orbit under the action of `G`. -/
@[to_additive /-- A bijection between the orbits under the action of an additive subgroup `H` on
`X`, and the orbits under the action of `H` on each orbit under the action of `G`. -/]
/-
**MulAction.equivSubgroupOrbits** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：equivSubgroupOrbits (H : Subgroup G) : orbitRel.Quotient H X ≃ Σ ω : Ω, or
bitRel.Quotient H (orbitRel.Quotient.orbit ω)
参数：H : Subgroup G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `MulAction.orbitRel_subgroup_le`：orbitRel_subgroup_le (H : Subgroup G) : 
orbitRel H α <= orbitRel G α
-/
noncomputable def equivSubgroupOrbits (H : Subgroup G) :
    orbitRel.Quotient H X ≃ Σ ω : Ω, orbitRel.Quotient H (orbitRel.Quotient.orbit ω) :=
  (Setoid.sigmaQuotientEquivOfLe (orbitRel_subgroup_le H)).symm.trans
    (Equiv.sigmaCongrRight fun ω ↦ (equivSubgroupOrbitsSetoidComap H ω).symm)

variable {X}

@[to_additive]
/-
**MulAction.finite_quotient_of_finite_quotient_of_finite_quotient** 是 Mathlib 中的
一个实例，位于命名空间 `MulAction`。
形式化陈述：finite_quotient_of_finite_quotient_of_finite_quotient {H : Subgroup G} [Fi
nite (orbitRel.Quotient G X)] [Finite (G ⧸ H)] : Finite orbitRel.Quotient H X
参数：orbitRel.Quotient G X；G ⧸ H。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `MulAction.instIsPretransitiveElemOrbit_1`：∀ {G : Type u_1} {α : Type u_2
} [inst : Group G] [inst_1 : MulAction G α] (x : MulAction.orbitRel.Quotient G α
),   MulAction.IsPretransitive…
-/
instance finite_quotient_of_finite_quotient_of_finite_quotient {H : Subgroup G}
    [Finite (orbitRel.Quotient G X)] [Finite (G ⧸ H)] :
    Finite <| orbitRel.Quotient H X := by
  rw [(equivSubgroupOrbits X H).finite_iff]
  infer_instance

/-- Given a group acting freely and transitively, an equivalence between the orbits under the
action of a subgroup and the quotient of the group by the subgroup. -/
@[to_additive /-- Given an additive group acting freely and transitively, an equivalence between the
orbits under the action of an additive subgroup and the quotient of the group by the subgroup. -/]
/-
**MulAction.equivSubgroupOrbitsQuotientGroup** 是 Mathlib 中的一个定义，位于命名空间 `MulActio
n`。
形式化陈述：equivSubgroupOrbitsQuotientGroup [IsPretransitive G X] [IsCancelSMul G X] 
(H : Subgroup G) : orbitRel.Quotient H X ≃ G ⧸ H where toFun
参数：H : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def equivSubgroupOrbitsQuotientGroup [IsPretransitive G X]
    [IsCancelSMul G X] (H : Subgroup G) :
    orbitRel.Quotient H X ≃ G ⧸ H where
  toFun := fun q ↦ q.liftOn' (fun y ↦ (exists_smul_eq G y x).choose) (by
    intro y₁ y₂ h
    rw [orbitRel_apply] at h
    rw [Quotient.eq'', leftRel_eq]
    dsimp only
    rcases h with ⟨g, rfl⟩
    dsimp only
    suffices (exists_smul_eq G (g • y₂) x).choose = (exists_smul_eq G y₂ x).choose * g⁻¹ by
      simp [this]
    refine IsCancelSMul.right_cancel _ _ (g • y₂) ?_
    rw [(exists_smul_eq G (g • y₂) x).choose_spec, Subgroup.smul_def, Subgroup.coe_inv,
        smul_smul, inv_mul_cancel_right, (exists_smul_eq G y₂ x).choose_spec])
  invFun := fun q ↦ q.liftOn' (fun g ↦ ⟦g⁻¹ • x⟧) (by
    intro g₁ g₂ h
    rw [leftRel_eq] at h
    rw [← @Quotient.mk''_eq_mk, Quotient.eq'', orbitRel_apply]
    exact ⟨⟨_, h⟩, by simp [mul_smul]⟩)
  left_inv := fun y ↦ by
    cases y using Quotient.inductionOn'
    simp only [Quotient.liftOn'_mk'']
    rw [← @Quotient.mk''_eq_mk, Quotient.eq'', orbitRel_apply]
    convert! mem_orbit_self _
    rw [inv_smul_eq_iff, (exists_smul_eq G _ x).choose_spec]
  right_inv := fun g ↦ by
    cases g using Quotient.inductionOn' with | _ g
    simp only [Quotient.liftOn'_mk'', QuotientGroup.mk]
    rw [Quotient.eq'', leftRel_eq]
    simp only
    convert! one_mem H
    rw [inv_mul_eq_one, eq_comm, ← inv_mul_eq_one, ← Subgroup.mem_bot,
        ← IsCancelSMul.stabilizer_eq_bot (g⁻¹ • x), mem_stabilizer_iff, mul_smul,
        (exists_smul_eq G (g⁻¹ • x) x).choose_spec]

/-- If `G` acts on `X` with trivial stabilizers, `X` is equivalent
to the product of the quotient of `X` by `G` and `G`.
See `MulAction.selfEquivOrbitsQuotientProd` with `φ = Quotient.out`. -/
@[to_additive selfEquivOrbitsQuotientProd' /-- If `G` acts freely on `X`, `X` is equivalent
to the product of the quotient of `X` by `G` and `G`.
See `AddAction.selfEquivOrbitsQuotientProd` with `φ = Quotient.out`. -/]
/-
**MulAction.selfEquivOrbitsQuotientProd'** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：selfEquivOrbitsQuotientProd' {φ : Quotient (MulAction.orbitRel G X) -> X} 
(hφ : Function.LeftInverse Quotient.mk'' φ) (h : forall b : X, MulAction.stabili
zer G b = ⊥) : X ≃ Quotient (MulAction.orbitRel G X) × G
参数：MulAction.orbitRel G X；hφ : Function.LeftInverse Quotient.mk'' φ；h : forall b
 : X, MulAction.stabilizer G b = ⊥。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
noncomputable def selfEquivOrbitsQuotientProd'
    {φ : Quotient (MulAction.orbitRel G X) → X} (hφ : Function.LeftInverse Quotient.mk'' φ)
    (h : ∀ b : X, MulAction.stabilizer G b = ⊥) :
    X ≃ Quotient (MulAction.orbitRel G X) × G :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer' G X hφ).trans <|
    (Equiv.sigmaCongrRight <| fun _ ↦
      (Subgroup.quotientEquivOfEq (h _)).trans (QuotientGroup.quotientEquivSelf G)).trans <|
    Equiv.sigmaEquivProd _ _

/-- If `G` acts freely on `X`, `X` is equivalent to the product of the quotient of `X` by `G` and
`G`. -/
@[to_additive selfEquivOrbitsQuotientProd
  /-- If `G` acts freely on `X`, `X` is equivalent to the product of the quotient of `X` by
`G` and `G`. -/]
/-
**MulAction.selfEquivOrbitsQuotientProd** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：selfEquivOrbitsQuotientProd (h : forall b : X, MulAction.stabilizer G b = 
⊥) : X ≃ Quotient (MulAction.orbitRel G X) × G
参数：h : forall b : X, MulAction.stabilizer G b = ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def selfEquivOrbitsQuotientProd (h : ∀ b : X, MulAction.stabilizer G b = ⊥) :
    X ≃ Quotient (MulAction.orbitRel G X) × G :=
  MulAction.selfEquivOrbitsQuotientProd' Quotient.out_eq' h

end MulAction

/-
**ConjClasses.card_carrier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConjClasses.card_carrier {G : Type*} [Group G] [Fintype G] (g : G) [Fintyp
e (ConjClasses.mk g).carrier] [Fintype <| MulAction.stabilizer (ConjAct G) g] : 
Fintype.card (ConjClasses.mk g).carrier = Fintype.card G / Fintype.card (MulActi
on.stabilizer (ConjAct G) g)
参数：g : G；ConjClasses.mk g；ConjAct G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`：card_orbit_mul_c
ard_stabilizer_eq_card_group (b : X) [Fintype G] [Fintype <| orbit G b] [Fintype
 <| stabilizer G b] : Fintype.card (orbit G …
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `ConjAct.orbit_eq_carrier_conjClasses`：orbit_eq_carrier_conjClasses (g : 
G) : orbit (ConjAct G) g = (ConjClasses.mk g).carrier
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ConjClasses.card_carrier {G : Type*} [Group G] [Fintype G] (g : G)
    [Fintype (ConjClasses.mk g).carrier] [Fintype <| MulAction.stabilizer (ConjAct G) g] :
    Fintype.card (ConjClasses.mk g).carrier =
      Fintype.card G / Fintype.card (MulAction.stabilizer (ConjAct G) g) := by
  classical
  rw [Fintype.card_congr <| ConjAct.toConjAct (G := G) |>.toEquiv]
  rw [← MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) g, Nat.mul_div_cancel]
  · simp_rw [ConjAct.orbit_eq_carrier_conjClasses]
  · exact Fintype.card_pos_iff.mpr inferInstance

namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

/-
**Subgroup.normalCore_eq_ker** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normalCore_eq_ker : H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulAction.Quotient.smul_mk`：∀ {G : Type u} {X : Type v} [inst : Group G]
 [inst_1 : Monoid X] [inst_2 : MulAction X G] (H : Subgroup G)   [inst_3 : MulAc
tion.QuotientAct…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `Subgroup.normal_le_normalCore`：normal_le_normalCore {H : Subgroup G} {N 
: Subgroup G} [hN : N.Normal] : N <= H.normalCore ↔ N <= H
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `Subgroup.inv_mem_iff`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G)
 {x : G}, x⁻¹ ∈ H ↔ x ∈ H
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.ext_iff`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, σ = τ ↔ ∀ (x : 
α), σ x = τ x
-/
theorem normalCore_eq_ker : H.normalCore = (MulAction.toPermHom G (G ⧸ H)).ker := by
  apply le_antisymm
  · intro g hg
    apply Equiv.Perm.ext
    refine fun q ↦ QuotientGroup.induction_on q ?_
    refine fun g' => (MulAction.Quotient.smul_mk H g g').trans (QuotientGroup.eq.mpr ?_)
    rw [smul_eq_mul, mul_inv_rev, ← inv_inv g', inv_inv]
    exact H.normalCore.inv_mem hg g'⁻¹
  · refine (Subgroup.normal_le_normalCore.mpr fun g hg => ?_)
    rw [← H.inv_mem_iff, ← mul_one g⁻¹, ← QuotientGroup.eq, ← mul_one g]
    exact (MulAction.Quotient.smul_mk H g 1).symm.trans (Equiv.Perm.ext_iff.mp hg (1 : G))

open QuotientGroup

/-- Cosets of the centralizer of an element embed into the set of commutators. -/
/-
**Subgroup.quotientCentralizerEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientCentralizerEmbedding (g : G) : G ⧸ centralizer {g} ↪ commutatorSet
 G
参数：g : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `ConjAct.stabilizer_eq_centralizer`：stabilizer_eq_centralizer (g : G) : s
tabilizer (ConjAct G) g = centralizer {toConjAct g}

--- 原说明 ---
Cosets of the centralizer of an element embed into the set of commutators.
-/
noncomputable def quotientCentralizerEmbedding (g : G) :
    G ⧸ centralizer {g} ↪ commutatorSet G :=
  ((MulAction.orbitEquivQuotientStabilizer (ConjAct G) g).trans
            (quotientEquivOfEq (ConjAct.stabilizer_eq_centralizer g))).symm.toEmbedding.trans
    ⟨fun x =>
      ⟨x * g⁻¹,
        let ⟨_, x, rfl⟩ := x
        ⟨x, g, rfl⟩⟩,
      fun _ _ => Subtype.ext ∘ mul_right_cancel ∘ Subtype.ext_iff.mp⟩
/-
**Subgroup.quotientCentralizerEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subgrou
p`。
形式化陈述：quotientCentralizerEmbedding_apply (g : G) (x : G) : quotientCentralizerEm
bedding g x = ⟨⁅x, g⁆, x, g, rfl⟩
参数：g : G；x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientCentralizerEmbedding_apply (g : G) (x : G) :
    quotientCentralizerEmbedding g x = ⟨⁅x, g⁆, x, g, rfl⟩ :=
  rfl

/-- If `G` is generated by `S`, then the quotient by the center embeds into `S`-indexed sequences
of commutators. -/
/-
**Subgroup.quotientCenterEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Subgroup`。
形式化陈述：quotientCenterEmbedding {S : Set G} (hS : closure S = ⊤) : G ⧸ center G ↪ 
S -> commutatorSet G
参数：hS : closure S = ⊤。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.center_eq_infi'`：center_eq_infi' {s : Set G} (hs : closure s = 
⊤) : center G = ⨅ g : s, centralizer {(g : G)}

--- 原说明 ---
If `G` is generated by `S`, then the quotient by the center embeds into `S`-inde
xed sequences
of commutators.
-/
noncomputable def quotientCenterEmbedding {S : Set G} (hS : closure S = ⊤) :
    G ⧸ center G ↪ S → commutatorSet G :=
  (quotientEquivOfEq (center_eq_infi' hS)).toEmbedding.trans
    ((quotientiInfEmbedding _).trans
      (Function.Embedding.piCongrRight fun g => quotientCentralizerEmbedding (g : G)))
/-
**Subgroup.quotientCenterEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：quotientCenterEmbedding_apply {S : Set G} (hS : closure S = ⊤) (g : G) (s 
: S) : quotientCenterEmbedding hS g s = ⟨⁅g, s⁆, g, s, rfl⟩
参数：hS : closure S = ⊤；g : G；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientCenterEmbedding_apply {S : Set G} (hS : closure S = ⊤) (g : G) (s : S) :
    quotientCenterEmbedding hS g s = ⟨⁅g, s⁆, g, s, rfl⟩ :=
  rfl

end Subgroup

