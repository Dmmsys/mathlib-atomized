/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Action.Pretransitive
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Tactic.ToDual

/-!
# Homomorphisms and group actions
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {M N α : Type*}

section
variable [Monoid M] [MulAction M α]

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `Function.Surjective.distribMulActionLeft` and `Function.Surjective.moduleLeft`.
-/
@[to_additive
/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →+ S`. -/]
/-
**Function.Surjective.mulActionLeft** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Function.Surjective.mulActionLeft {R S M : Type*} [Monoid R] [MulAction R 
M] [Monoid S] [SMul S M] (f : R ->* S) (hf : Surjective f) (hsmul : forall (c) (
x : M), f c • x = c • x) : MulAction S M where one_smul b
参数：f : R ->* S；hf : Surjective f；hsmul : forall (c) (x : M), f c • x = c • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Function.Surjective.mulActionLeft {R S M : Type*} [Monoid R] [MulAction R M] [Monoid S]
    [SMul S M] (f : R →* S) (hf : Surjective f) (hsmul : ∀ (c) (x : M), f c • x = c • x) :
    MulAction S M where
  one_smul b := by rw [← f.map_one, hsmul, one_smul]
  mul_smul := hf.forall₂.mpr fun a b x ↦ by simp only [← f.map_mul, hsmul, mul_smul]

namespace MulAction

variable (α)

/-- A multiplicative action of `M` on `α` and a monoid homomorphism `N → M` induce
a multiplicative action of `N` on `α`.

See note [reducible non-instances]. -/
@[to_additive]
/-
**MulAction.compHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `MulAction`。
形式化陈述：compHom [Monoid N] (g : N ->* M) : MulAction N α where smul
参数：g : N ->* M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative action of `M` on `α` and a monoid homomorphism `N → M` induce
a multiplicative action of `N` on `α`.

See note [reducible non-instances].
-/
abbrev compHom [Monoid N] (g : N →* M) : MulAction N α where
  smul := SMul.comp.smul g
  one_smul _ := by simpa [(· • ·)] using one_smul ..
  mul_smul _ _ _ := by simpa [(· • ·)] using mul_smul ..

/-- An additive action of `M` on `α` and an additive monoid homomorphism `N → M` induce
an additive action of `N` on `α`.

See note [reducible non-instances]. -/
add_decl_doc AddAction.compHom

@[to_additive]
/-
**MulAction.compHom_smul_def** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：compHom_smul_def {E F G : Type*} [Monoid E] [Monoid F] [MulAction F G] (f 
: E ->* F) (a : E) (x : G) : letI : MulAction E G
参数：f : E ->* F；a : E；x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compHom_smul_def
    {E F G : Type*} [Monoid E] [Monoid F] [MulAction F G] (f : E →* F) (a : E) (x : G) :
    letI : MulAction E G := MulAction.compHom _ f
    a • x = (f a) • x := rfl

/-- If an action is transitive, then composing this action with a surjective homomorphism gives
again a transitive action. -/
@[to_additive]
/-
**MulAction.isPretransitive_compHom** 是 Mathlib 中的一个引理，位于命名空间 `MulAction`。
形式化陈述：isPretransitive_compHom {E F G : Type*} [Monoid E] [Monoid F] [MulAction F
 G] [IsPretransitive F G] {f : E ->* F} (hf : Surjective f) : letI : MulAction E
 G
参数：hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y

--- 原说明 ---
If an action is transitive, then composing this action with a surjective homomor
phism gives
again a transitive action.
-/
lemma isPretransitive_compHom {E F G : Type*} [Monoid E] [Monoid F] [MulAction F G]
    [IsPretransitive F G] {f : E →* F} (hf : Surjective f) :
    letI : MulAction E G := MulAction.compHom _ f
    IsPretransitive E G := by
  let _ : MulAction E G := MulAction.compHom _ f
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : F, m • x = y := exists_smul_eq F x y
  obtain ⟨e, rfl⟩ : ∃ e, f e = m := hf m
  exact ⟨e, rfl⟩

@[to_additive]
/-
**MulAction.IsPretransitive.of_compHom** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.IsPr
etransitive`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} {α : Type u_6} [inst : Monoid M] [inst_1 :
 Monoid N] [inst_2 : MulAction N α]   (f : M →* N) [h : MulAction.IsPretransitiv
e M α], MulAction.IsPretransitive N α
参数：f : M →* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.of_smul_eq`：∀ {M : Type u_5} {N : Type u_6} {α
 : Type u_7} [inst : SMul M α] [inst_1 : SMul N α] [MulAction.IsPretransitive M 
α]   (f : M → N), (∀ {c : …
-/
lemma IsPretransitive.of_compHom {M N α : Type*} [Monoid M] [Monoid N] [MulAction N α]
    (f : M →* N) [h : letI := compHom α f; IsPretransitive M α] : IsPretransitive N α :=
  letI := compHom α f; h.of_smul_eq f rfl

end MulAction
end

section CompatibleScalar

/-- If the multiplicative action of `M` on `N` is compatible with multiplication on `N`, then
`fun x ↦ x • 1` is a monoid homomorphism from `M` to `N`. -/
@[to_additive (attr := simps)
/-- If the additive action of `M` on `N` is compatible with addition on `N`, then
`fun x ↦ x +ᵥ 0` is an additive monoid homomorphism from `M` to `N`. -/]
/-
**MonoidHom.smulOneHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.smulOneHom {M N} [Monoid M] [MulOneClass N] [MulAction M N] [IsS
calarTower M N N] : M ->* N where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.smulOneHom {M N} [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N] :
    M →* N where
  toFun x := x • (1 : N)
  map_one' := one_smul _ _
  map_mul' x y := by rw [smul_one_mul, smul_smul]

/-- A monoid homomorphism between two monoids M and N can be equivalently specified by a
multiplicative action of M on N that is compatible with the multiplication on N. -/
@[to_additive
/-- A monoid homomorphism between two additive monoids M and N can be equivalently
specified by an additive action of M on N that is compatible with the addition on N. -/]
/-
**monoidHomEquivMulActionIsScalarTower** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：monoidHomEquivMulActionIsScalarTower (M N) [Monoid M] [Monoid N] : (M ->* 
N) ≃ {_inst : MulAction M N // IsScalarTower M N N} where toFun f
参数：M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monoidHomEquivMulActionIsScalarTower (M N) [Monoid M] [Monoid N] :
    (M →* N) ≃ {_inst : MulAction M N // IsScalarTower M N N} where
  toFun f := ⟨MulAction.compHom N f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ ↦ MonoidHom.smulOneHom
  left_inv f := MonoidHom.ext fun m ↦ mul_one (f m)
  right_inv := fun ⟨_, _⟩ ↦ Subtype.ext <| MulAction.ext <| funext₂ <| smul_one_smul N

end CompatibleScalar

