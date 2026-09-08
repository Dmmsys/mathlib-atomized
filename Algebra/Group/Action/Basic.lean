/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# More lemmas about group actions

This file contains lemmas about group actions that require more imports than
`Mathlib/Algebra/Group/Action/Defs.lean` offers.
-/

@[expose] public section

assert_not_exists MonoidWithZero Equiv.Perm.permGroup

variable {G M A B α β : Type*}

section MulAction

section Group

variable [Group α] [MulAction α β]

/-- Given an action of a group `α` on `β`, each `g : α` defines a permutation of `β`. -/
@[to_additive (attr := simps)]
/-
**MulAction.toPerm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulAction.toPerm (a : α) : Equiv.Perm β
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a

--- 原说明 ---
Given an action of a group `α` on `β`, each `g : α` defines a permutation of `β`
.
-/
def MulAction.toPerm (a : α) : Equiv.Perm β :=
  ⟨fun x => a • x, fun x => a⁻¹ • x, inv_smul_smul a, smul_inv_smul a⟩

/-- Given an action of an additive group `α` on `β`, each `g : α` defines a permutation of `β`. -/
add_decl_doc AddAction.toPerm

/-- `MulAction.toPerm` is injective on faithful actions. -/
@[to_additive /-- `AddAction.toPerm` is injective on faithful actions. -/]
/-
**MulAction.toPerm_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulAction.toPerm_injective [FaithfulSMul α β] : Function.Injective (MulAct
ion.toPerm : α -> Equiv.Perm β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用引理 `smul_left_injective'`：smul_left_injective' [SMul M α] [FaithfulSMul M α]
 : Injective ((· • ·) : M -> α -> α)

--- 原说明 ---
`MulAction.toPerm` is injective on faithful actions.
-/
lemma MulAction.toPerm_injective [FaithfulSMul α β] :
    Function.Injective (MulAction.toPerm : α → Equiv.Perm β) :=
  (show Function.Injective (Equiv.toFun ∘ MulAction.toPerm) from smul_left_injective').of_comp

@[to_additive]
/-
**MulAction.bijective** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [inst_1 : MulAction α β] 
(g : α), Function.Bijective fun x => g • x
参数：g : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected lemma MulAction.bijective (g : α) : Function.Bijective (g • · : β → β) :=
  (MulAction.toPerm g).bijective

@[to_additive]
/-
**MulAction.injective** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [inst_1 : MulAction α β] 
(g : α), Function.Injective fun x => g • x
参数：g : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
-/
protected lemma MulAction.injective (g : α) : Function.Injective (g • · : β → β) :=
  (MulAction.bijective g).injective

@[to_additive]
/-
**MulAction.surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [inst_1 : MulAction α β] 
(g : α), Function.Surjective fun x => g • x
参数：g : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
-/
protected lemma MulAction.surjective (g : α) : Function.Surjective (g • · : β → β) :=
  (MulAction.bijective g).surjective

@[to_additive]
/-
**smul_left_cancel** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_left_cancel (g : α) {x y : β} (h : g • x = g • y) : x = y
参数：g : α；h : g • x = g • y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_left_cancel (g : α) {x y : β} (h : g • x = g • y) : x = y := MulAction.injective g h

@[to_additive (attr := simp)]
/-
**smul_left_cancel_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_left_cancel_iff (g : α) {x y : β} : g • x = g • y ↔ x = y
参数：g : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma smul_left_cancel_iff (g : α) {x y : β} : g • x = g • y ↔ x = y :=
  (MulAction.injective g).eq_iff

@[to_additive]
/-
**smul_eq_iff_eq_inv_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g • x = y ↔ x = g⁻¹ • y
参数：g : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `eq_inv_smul_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
-/
lemma smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g • x = y ↔ x = g⁻¹ • y :=
  eq_inv_smul_iff.symm

@[to_additive]
/-
**isCancelSMul_iff_eq_one_of_smul_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCancelSMul_iff_eq_one_of_smul_eq : IsCancelSMul α β ↔ (forall (g : α) (x
 : β), g • x = x -> g = 1)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCancelSMul.eq_one_of_smul`：IsCancelSMul.eq_one_of_smul {G P} [Monoid G
] [MulAction G P] [IsCancelSMul G P] {g : G} {x : P} (h : g • x = x) : g = 1
· 使用定理 `instIsLeftCancelSMul`：∀ (G : Type u_9) (P : Type u_10) [inst : Group G] 
[inst_1 : MulAction G P], IsLeftCancelSMul G P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_iff_eq_inv_smul`：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g •
 x = y ↔ x = g⁻¹ • y
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `inv_mul_eq_one`：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
-/
lemma isCancelSMul_iff_eq_one_of_smul_eq :
    IsCancelSMul α β ↔ (∀ (g : α) (x : β), g • x = x → g = 1) := by
  refine ⟨fun H _ _ ↦ IsCancelSMul.eq_one_of_smul, fun H ↦ ⟨fun g h x ↦ ?_⟩⟩
  rw [smul_eq_iff_eq_inv_smul, eq_comm, ← mul_smul, ← inv_mul_eq_one (G := α)]
  exact H (g⁻¹ * h) x

end Group

section Monoid
variable [Monoid α] [MulAction α β] (c : α) (x y : β) [Invertible c]

/-
**invOf_smul_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Monoid α] [inst_1 : MulAction α β]
 (c : α) (x : β) [inst_2 : Invertible c],   ⅟c • c • x = x
参数：c : α；x : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
@[simp] lemma invOf_smul_smul : ⅟c • c • x = x := inv_smul_smul (unitOfInvertible c) _
/-
**smul_invOf_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Monoid α] [inst_1 : MulAction α β]
 (c : α) (x : β) [inst_2 : Invertible c],   c • ⅟c • x = x
参数：c : α；x : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
@[simp] lemma smul_invOf_smul : c • (⅟c • x) = x := smul_inv_smul (unitOfInvertible c) _

variable {c x y}
/-
**invOf_smul_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：invOf_smul_eq_iff : ⅟c • x = y ↔ x = c • y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_smul_eq_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, g⁻¹ • a = b ↔ a = g • b
-/
lemma invOf_smul_eq_iff : ⅟c • x = y ↔ x = c • y := inv_smul_eq_iff (g := unitOfInvertible c)
/-
**smul_eq_iff_eq_invOf_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_eq_iff_eq_invOf_smul : c • x = y ↔ x = ⅟c • y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_eq_iff_eq_inv_smul`：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g •
 x = y ↔ x = g⁻¹ • y
-/
lemma smul_eq_iff_eq_invOf_smul : c • x = y ↔ x = ⅟c • y :=
  smul_eq_iff_eq_inv_smul (g := unitOfInvertible c)

end Monoid
end MulAction

section Arrow
variable {G A B : Type*} [DivisionMonoid G] [MulAction G A]

/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g • F) a = F (g⁻¹ • a)`. -/
@[to_additive (attr := instance_reducible, simps) arrowAddAction
/-- If `G` acts on `A`, then it acts also on `A → B`, by `(g +ᵥ F) a = F (g⁻¹ +ᵥ a)` -/]
/-
**arrowAction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：arrowAction : MulAction G (A -> B) where smul g F a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def arrowAction : MulAction G (A → B) where
  smul g F a := F (g⁻¹ • a)
  one_smul f := by
    change (fun x => f ((1 : G)⁻¹ • x)) = f
    simp only [inv_one, one_smul]
  mul_smul x y f := by
    change (fun a => f ((x * y)⁻¹ • a)) = (fun a => f (y⁻¹ • x⁻¹ • a))
    simp only [mul_smul, mul_inv_rev]

attribute [local instance] arrowAction

variable [Monoid M]

/-- When `M` is a monoid, `ArrowAction` is additionally a `MulDistribMulAction`. -/
@[instance_reducible]
/-
**arrowMulDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：arrowMulDistribMulAction : MulDistribMulAction G (A -> M) where smul_one _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `M` is a monoid, `ArrowAction` is additionally a `MulDistribMulAction`.
-/
def arrowMulDistribMulAction : MulDistribMulAction G (A → M) where
  smul_one _ := rfl
  smul_mul _ _ _ := rfl

end Arrow

namespace IsUnit
variable [Monoid α] [MulAction α β]

@[to_additive]
/-
**IsUnit.smul_bijective** 是 Mathlib 中的一个定理，位于命名空间 `IsUnit`。
形式化陈述：smul_bijective {m : α} (hm : IsUnit m) : Function.Bijective (fun (a : β) =
> m • a)
参数：hm : IsUnit m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
-/
theorem smul_bijective {m : α} (hm : IsUnit m) :
    Function.Bijective (fun (a : β) ↦ m • a) := by
  lift m to αˣ using hm
  exact MulAction.bijective m

@[to_additive]
/-
**IsUnit.smul_left_cancel** 是 Mathlib 中的一个引理，位于命名空间 `IsUnit`。
形式化陈述：smul_left_cancel {a : α} (ha : IsUnit a) {x y : β} : a • x = a • y ↔ x = y
参数：ha : IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_left_cancel_iff`：smul_left_cancel_iff (g : α) {x y : β} : g • x = g
 • y ↔ x = y
-/
lemma smul_left_cancel {a : α} (ha : IsUnit a) {x y : β} : a • x = a • y ↔ x = y :=
  let ⟨u, hu⟩ := ha
  hu ▸ smul_left_cancel_iff u

end IsUnit

section SMul
variable [Group α] [Monoid β] [MulAction α β] [SMulCommClass α β β] [IsScalarTower α β β]

/-
**isUnit_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [inst_1 : Monoid β] [inst
_2 : MulAction α β] [SMulCommClass α β β]   [IsScalarTower α β β] (g : α) (m : β
), IsUnit (g • m) ↔ IsUnit m
参数：g : α；m : β；g • m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.smul`：IsUnit.smul [Group G] [Monoid M] [MulAction G M] [SMulCommC
lass G M M] [IsScalarTower G M M] {m : M} (g : G) (h : IsUnit m) : IsUnit (g • m
)
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
@[simp] lemma isUnit_smul_iff (g : α) (m : β) : IsUnit (g • m) ↔ IsUnit m :=
  ⟨fun h => inv_smul_smul g m ▸ h.smul g⁻¹, IsUnit.smul g⟩

end SMul

namespace MulAction
variable [Monoid M] [MulAction M α]

variable (M α) in
/-- Embedding of `α` into functions `M → α` induced by a multiplicative action of `M` on `α`. -/
@[to_additive
/-- Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`. -/]
/-
**MulAction.toFun** 是 Mathlib 中的一个定义，位于命名空间 `MulAction`。
形式化陈述：toFun : α ↪ M -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toFun : α ↪ M → α :=
  ⟨fun y x ↦ x • y, fun y₁ y₂ H ↦ one_smul M y₁ ▸ one_smul M y₂ ▸ by convert! congr_fun H 1⟩

@[to_additive (attr := simp)]
/-
**MulAction.toFun_apply** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：toFun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y
参数：x : M；y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toFun_apply (x : M) (y : α) : MulAction.toFun M α y x = x • y := rfl

end MulAction

section MulDistribMulAction
variable [Monoid M] [Monoid A] [MulDistribMulAction M A]

/-- Pullback a multiplicative distributive multiplicative action along an injective monoid
homomorphism. -/
-- See note [reducible non-instances]
/-
**Function.Injective.mulDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Function.Inj
ective`。
形式化陈述：{M : Type u_2} →   {A : Type u_3} →     {B : Type u_4} →       [inst : Mon
oid M] →         [inst_1 : Monoid A] →           [inst_2 : MulDistribMulAction M
 A] →             [inst_3 : Monoid B] →               [inst_4 : SMul M B] →     
            (f : B →* A) →                   Function.Injective ⇑f → (∀ (c : M) 
(x : B), f (c • x) = c • f x) → MulDistribMulAction M B
参数：f : B →* A；∀ (c : M) (x : B), f (c • x) = c • f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev Function.Injective.mulDistribMulAction [Monoid B] [SMul M B] (f : B →* A)
    (hf : Injective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B where
  __ := hf.mulAction f smul
  smul_mul c x y := hf <| by simp only [smul, f.map_mul, smul_mul']
  smul_one c := hf <| by simp only [smul, f.map_one, smul_one]

/-- Pushforward a multiplicative distributive multiplicative action along a surjective monoid
homomorphism. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.mulDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Function.Su
rjective`。
形式化陈述：{M : Type u_2} →   {A : Type u_3} →     {B : Type u_4} →       [inst : Mon
oid M] →         [inst_1 : Monoid A] →           [inst_2 : MulDistribMulAction M
 A] →             [inst_3 : Monoid B] →               [inst_4 : SMul M B] →     
            (f : A →* B) →                   Function.Surjective ⇑f → (∀ (c : M)
 (x : A), f (c • x) = c • f x) → MulDistribMulAction M B
参数：f : A →* B；∀ (c : M) (x : A), f (c • x) = c • f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev Function.Surjective.mulDistribMulAction [Monoid B] [SMul M B] (f : A →* B)
    (hf : Surjective f) (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M B where
  __ := hf.mulAction f smul
  smul_mul c := by simp only [hf.forall, smul_mul', ← smul, ← f.map_mul, implies_true]
  smul_one c := by rw [← f.map_one, ← smul, smul_one]

variable (A) in
/-- Scalar multiplication by `r` as a `MonoidHom`. -/
/-
**MulDistribMulAction.toMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `MulDistribMulAction
`。
形式化陈述：{M : Type u_2} → (A : Type u_3) → [inst : Monoid M] → [inst_1 : Monoid A] 
→ [MulDistribMulAction M A] → M → A →* A
参数：A : Type u_3。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulDistribMulAction.smul_one`：∀ {M : Type u_9} {N : Type u_10} {inst : M
onoid M} {inst_1 : Monoid N} [self : MulDistribMulAction M N] (r : M),   r • 1 =
 1
· 使用引理 `smul_mul'`：smul_mul' (a : M) (b₁ b₂ : N) : a • (b₁ * b₂) = a • b₁ * a • 
b₂

--- 原说明 ---
Scalar multiplication by `r` as a `MonoidHom`.
-/
@[simps] def MulDistribMulAction.toMonoidHom (r : M) : A →* A where
  toFun := (r • ·)
  map_one' := smul_one r
  map_mul' := smul_mul' r
/-
**smul_pow'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_2} {A : Type u_3} [inst : Monoid M] [inst_1 : Monoid A] [ins
t_2 : MulDistribMulAction M A] (r : M) (x : A)   (n : ℕ), r • x ^ n = (r • x) ^ 
n
参数：r : M；x : A；n : ℕ；r • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
@[simp] lemma smul_pow' (r : M) (x : A) (n : ℕ) : r • x ^ n = (r • x) ^ n :=
  (MulDistribMulAction.toMonoidHom _ _).map_pow _ _

variable (M A) in
/-- Each element of the monoid defines a monoid homomorphism. -/
@[simps]
/-
**MulDistribMulAction.toMonoidEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulDistribMulAction.toMonoidEnd : M ->* Monoid.End A where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each element of the monoid defines a monoid homomorphism.
-/
def MulDistribMulAction.toMonoidEnd : M →* Monoid.End A where
  toFun := MulDistribMulAction.toMonoidHom A
  map_one' := MonoidHom.ext <| one_smul M
  map_mul' x y := MonoidHom.ext <| mul_smul x y

end MulDistribMulAction

section MulDistribMulAction
variable [Monoid M] [Group A] [MulDistribMulAction M A]

/-
**smul_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_2} {A : Type u_3} [inst : Monoid M] [inst_1 : Group A] [inst
_2 : MulDistribMulAction M A] (r : M) (x : A),   r • x⁻¹ = (r • x)⁻¹
参数：r : M；x : A；r • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_inv`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [ins
t_1 : DivisionMonoid β] (f : α →* β) (a : α), f a⁻¹ = (f a)⁻¹
-/
@[simp] lemma smul_inv' (r : M) (x : A) : r • x⁻¹ = (r • x)⁻¹ :=
  (MulDistribMulAction.toMonoidHom A r).map_inv x
/-
**smul_div'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_div' (r : M) (x y : A) : r • (x / y) = r • x / r • y
参数：r : M；x y : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
-/
lemma smul_div' (r : M) (x y : A) : r • (x / y) = r • x / r • y :=
  map_div (MulDistribMulAction.toMonoidHom A r) x y
/-
**smul_zpow'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_zpow' (r : M) (x : A) (z : Int) : r • (x ^ z) = (r • x) ^ z
参数：r : M；x : A；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
-/
lemma smul_zpow' (r : M) (x : A) (z : ℤ) : r • (x ^ z) = (r • x) ^ z :=
  map_zpow (MulDistribMulAction.toMonoidHom A r) x z

end MulDistribMulAction

