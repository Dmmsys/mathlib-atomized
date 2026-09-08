/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# Incidence algebras

Given a locally finite order `α` the incidence algebra over `α` is the type of functions from
non-empty intervals of `α` to some algebraic codomain.

This algebra has a natural multiplication operation whereby the product of two such functions
is defined on an interval by summing over all divisions into two subintervals the product of the
values of the original pair of functions.

This structure allows us to interpret many natural invariants of the intervals (such as their
cardinality) as elements of the incidence algebra. For instance the cardinality function, viewed as
an element of the incidence algebra, is simply the square of the function that takes constant value
one on all intervals. This constant function is called the zeta function, after
its connection with the Riemann zeta function.

The incidence algebra is a good setting for proving many inclusion-exclusion type principles, these
go under the name Möbius inversion, and are essentially due to the fact that the zeta function has
a multiplicative inverse in the incidence algebra, an inductively definable function called the
Möbius function that generalizes the Möbius function in number theory.

## Main definitions

* `1 : IncidenceAlgebra 𝕜 α` is the delta function, defined analogously to the identity matrix.
* `f * g` is the incidence algebra product, defined analogously to the matrix product.
* `IncidenceAlgebra.zeta` is the zeta function, defined analogously to the upper triangular matrix
  of ones.
* `IncidenceAlgebra.mu` is the inverse of the zeta function.

## Implementation notes

One has to define `mu` as either the left or right inverse of `zeta`. We define it as the left
inverse, and prove it is also a right inverse by defining `mu'` as the right inverse and using that
left and right inverses agree if they exist.

## TODOs

Here are some additions to this file that could be made in the future:
- Generalize the construction of `mu` to invert any element of the incidence algebra `f` which has
  `f x x` a unit for all `x`.
- Give formulas for higher powers of zeta.
- A formula for the möbius function on a pi type similar to the one for products
- More examples / applications to different posets.
- Connection with Galois insertions
- Finsum version of Möbius inversion that holds even when an order doesn't have top/bot?
- Connect this theory to (infinite) matrices, giving maps of the incidence algebra to matrix rings
- Connect to the more advanced theory of arithmetic functions, and Dirichlet convolution.

## References

* [Aigner, *Combinatorial Theory, Chapter IV*][aigner1997]
* [Jacobson, *Basic Algebra I, 8.6*][jacobson1974]
* [Doubilet, Rota, Stanley, *On the foundations of Combinatorial Theory
  VI*][doubilet_rota_stanley_vi]
* [Spiegel, O'Donnell, *Incidence Algebras*][spiegel_odonnell1997]
* [Kung, Rota, Yan, *Combinatorics: The Rota Way, Chapter 3*][kung_rota_yan2009]
-/

@[expose] public section

open Finset OrderDual

variable {F 𝕜 𝕝 𝕞 α β : Type*}

/-- The `𝕜`-incidence algebra over `α`. -/
/-
**IncidenceAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_7) → (α : Type u_8) → [Zero 𝕜] → [LE α] → Type (max u_7 u_8)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `𝕜`-incidence algebra over `α`.
-/
structure IncidenceAlgebra (𝕜 α : Type*) [Zero 𝕜] [LE α] where
  /-- The underlying function of an element of the incidence algebra.

  Do not use this function directly. Instead use the coercion coming from the `FunLike`
  instance. -/
  toFun : α → α → 𝕜
  eq_zero_of_not_le' ⦃a b : α⦄ : ¬a ≤ b → toFun a b = 0

namespace IncidenceAlgebra
section Zero
variable [Zero 𝕜] [LE α] {a b : α}

/-
**IncidenceAlgebra.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instFunLike : FunLike (IncidenceAlgebra 𝕜 α) α (α -> 𝕜) where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (IncidenceAlgebra 𝕜 α) α (α → 𝕜) where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr
/-
**IncidenceAlgebra.apply_eq_zero_of_not_le** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceA
lgebra`。
形式化陈述：apply_eq_zero_of_not_le (h : ¬a <= b) (f : IncidenceAlgebra 𝕜 α) : f a b =
 0
参数：h : ¬a <= b；f : IncidenceAlgebra 𝕜 α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IncidenceAlgebra.eq_zero_of_not_le'`：∀ {𝕜 : Type u_7} {α : Type u_8} [in
st : Zero 𝕜] [inst_1 : LE α] (self : IncidenceAlgebra 𝕜 α) ⦃a b : α⦄,   ¬a ≤ b →
 self.toFun a b = 0
-/
lemma apply_eq_zero_of_not_le (h : ¬a ≤ b) (f : IncidenceAlgebra 𝕜 α) : f a b = 0 :=
  eq_zero_of_not_le' _ h
/-
**IncidenceAlgebra.le_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：le_of_ne_zero {f : IncidenceAlgebra 𝕜 α} : f a b != 0 -> a <= b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用引理 `IncidenceAlgebra.apply_eq_zero_of_not_le`：apply_eq_zero_of_not_le (h : ¬
a <= b) (f : IncidenceAlgebra 𝕜 α) : f a b = 0
-/
lemma le_of_ne_zero {f : IncidenceAlgebra 𝕜 α} : f a b ≠ 0 → a ≤ b :=
  not_imp_comm.1 fun h ↦ apply_eq_zero_of_not_le h _

section Coes

-- this must come after the `FunLike` instance
initialize_simps_projections IncidenceAlgebra (toFun → apply)

/-
**IncidenceAlgebra.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Zero 𝕜] [inst_1 : LE α] (f : Incid
enceAlgebra 𝕜 α), f.toFun = ⇑f
参数：f : IncidenceAlgebra 𝕜 α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toFun_eq_coe (f : IncidenceAlgebra 𝕜 α) : f.toFun = f := rfl
/-
**IncidenceAlgebra.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Zero 𝕜] [inst_1 : LE α] (f : α → α
 → 𝕜) (h : ∀ ⦃a b : α⦄, ¬a ≤ b → f a b = 0),   ⇑{ toFun := f, eq_zero_of_not_le'
 := h } = f
参数：f : α → α → 𝕜；h : ∀ ⦃a b : α⦄, ¬a ≤ b → f a b = 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mk (f : α → α → 𝕜) (h) : (mk f h : α → α → 𝕜) = f := rfl
/-
**IncidenceAlgebra.coe_inj** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：coe_inj {f g : IncidenceAlgebra 𝕜 α} : (f : α -> α -> 𝕜) = g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma coe_inj {f g : IncidenceAlgebra 𝕜 α} : (f : α → α → 𝕜) = g ↔ f = g :=
  DFunLike.coe_injective.eq_iff

@[ext]
/-
**IncidenceAlgebra.ext** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : forall a b, a <= b -> f a b = g a b)
 : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IncidenceAlgebra.apply_eq_zero_of_not_le`：apply_eq_zero_of_not_le (h : ¬
a <= b) (f : IncidenceAlgebra 𝕜 α) : f a b = 0
-/
lemma ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : ∀ a b, a ≤ b → f a b = g a b) : f = g := by
  refine DFunLike.coe_injective (funext₂ fun a b ↦ ?_)
  by_cases hab : a ≤ b
  · exact h _ _ hab
  · rw [apply_eq_zero_of_not_le hab, apply_eq_zero_of_not_le hab]
/-
**IncidenceAlgebra.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Zero 𝕜] [inst_1 : LE α] (f : Incid
enceAlgebra 𝕜 α)   (h : ∀ ⦃a b : α⦄, ¬a ≤ b → f a b = 0), { toFun := ⇑f, eq_zero
_of_not_le' := h } = f
参数：f : IncidenceAlgebra 𝕜 α；h : ∀ ⦃a b : α⦄, ¬a ≤ b → f a b = 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_coe (f : IncidenceAlgebra 𝕜 α) (h) : mk f h = f := rfl

end Coes

/-! ### Additive and multiplicative structure -/

/-
**IncidenceAlgebra.instZero** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instZero : Zero (IncidenceAlgebra 𝕜 α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Additive and multiplicative structure
-/
instance instZero : Zero (IncidenceAlgebra 𝕜 α) := ⟨⟨fun _ _ ↦ 0, fun _ _ _ ↦ rfl⟩⟩
/-
**IncidenceAlgebra.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instInhabited : Inhabited (IncidenceAlgebra 𝕜 α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (IncidenceAlgebra 𝕜 α) := ⟨0⟩
/-
**IncidenceAlgebra.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Zero 𝕜] [inst_1 : LE α], ⇑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zero : ⇑(0 : IncidenceAlgebra 𝕜 α) = 0 := rfl
/-
**IncidenceAlgebra.zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：zero_apply (a b : α) : (0 : IncidenceAlgebra 𝕜 α) a b = 0
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_apply (a b : α) : (0 : IncidenceAlgebra 𝕜 α) a b = 0 := rfl

end Zero

section Add
variable [AddZeroClass 𝕜] [LE α]

/-
**IncidenceAlgebra.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instAdd : Add (IncidenceAlgebra 𝕜 α) where add f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (IncidenceAlgebra 𝕜 α) where
  add f g := ⟨f + g, fun a b h ↦ by simp_rw [Pi.add_apply, apply_eq_zero_of_not_le h, zero_add]⟩
/-
**IncidenceAlgebra.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : AddZeroClass 𝕜] [inst_1 : LE α] (f
 g : IncidenceAlgebra 𝕜 α), ⇑(f + g) = ⇑f + ⇑g
参数：f g : IncidenceAlgebra 𝕜 α；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_add (f g : IncidenceAlgebra 𝕜 α) : ⇑(f + g) = f + g := rfl
/-
**IncidenceAlgebra.add_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：add_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f + g) a b = f a b + g
 a b
参数：f g : IncidenceAlgebra 𝕜 α；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f + g) a b = f a b + g a b := rfl

end Add

section Smul
variable {M : Type*} [Zero 𝕜] [LE α] [SMulZeroClass M 𝕜]

/-
**IncidenceAlgebra.instSmulZeroClassRight** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAl
gebra`。
形式化陈述：instSmulZeroClassRight : SMulZeroClass M (IncidenceAlgebra 𝕜 α) where smul
 c f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSmulZeroClassRight : SMulZeroClass M (IncidenceAlgebra 𝕜 α) where
  smul c f :=
    ⟨c • ⇑f, fun a b hab ↦ by simp_rw [Pi.smul_apply, apply_eq_zero_of_not_le hab, smul_zero]⟩
  smul_zero c := by ext; exact smul_zero _
/-
**IncidenceAlgebra.coe_constSMul** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} {M : Type u_7} [inst : Zero 𝕜] [inst_1 : L
E α] [inst_2 : SMulZeroClass M 𝕜] (c : M)   (f : IncidenceAlgebra 𝕜 α), ⇑(c • f)
 = c • ⇑f
参数：c : M；f : IncidenceAlgebra 𝕜 α；c • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_constSMul (c : M) (f : IncidenceAlgebra 𝕜 α) : ⇑(c • f) = c • ⇑f := rfl
/-
**IncidenceAlgebra.constSMul_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：constSMul_apply (c : M) (f : IncidenceAlgebra 𝕜 α) (a b : α) : (c • f) a b
 = c • f a b
参数：c : M；f : IncidenceAlgebra 𝕜 α；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma constSMul_apply (c : M) (f : IncidenceAlgebra 𝕜 α) (a b : α) : (c • f) a b = c • f a b := rfl

end Smul

/-
**IncidenceAlgebra.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instAddMonoid [AddMonoid 𝕜] [LE α] : AddMonoid (IncidenceAlgebra 𝕜 α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoid [AddMonoid 𝕜] [LE α] : AddMonoid (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addMonoid _ coe_zero coe_add fun _ _ ↦ rfl
/-
**IncidenceAlgebra.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra
`。
形式化陈述：instAddCommMonoid [AddCommMonoid 𝕜] [LE α] : AddCommMonoid (IncidenceAlgeb
ra 𝕜 α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoid [AddCommMonoid 𝕜] [LE α] : AddCommMonoid (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addCommMonoid _ coe_zero coe_add fun _ _ ↦ rfl

section AddGroup
variable [AddGroup 𝕜] [LE α]

/-
**IncidenceAlgebra.instNeg** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instNeg : Neg (IncidenceAlgebra 𝕜 α) where neg f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNeg : Neg (IncidenceAlgebra 𝕜 α) where
  neg f := ⟨-f, fun a b h ↦ by simp_rw [Pi.neg_apply, apply_eq_zero_of_not_le h, neg_zero]⟩
/-
**IncidenceAlgebra.instSub** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instSub : Sub (IncidenceAlgebra 𝕜 α) where sub f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub (IncidenceAlgebra 𝕜 α) where
  sub f g := ⟨f - g, fun a b h ↦ by simp_rw [Pi.sub_apply, apply_eq_zero_of_not_le h, sub_zero]⟩
/-
**IncidenceAlgebra.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : AddGroup 𝕜] [inst_1 : LE α] (f : I
ncidenceAlgebra 𝕜 α), ⇑(-f) = -⇑f
参数：f : IncidenceAlgebra 𝕜 α；-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_neg (f : IncidenceAlgebra 𝕜 α) : ⇑(-f) = -f := rfl
/-
**IncidenceAlgebra.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : AddGroup 𝕜] [inst_1 : LE α] (f g :
 IncidenceAlgebra 𝕜 α), ⇑(f - g) = ⇑f - ⇑g
参数：f g : IncidenceAlgebra 𝕜 α；f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_sub (f g : IncidenceAlgebra 𝕜 α) : ⇑(f - g) = f - g := rfl
/-
**IncidenceAlgebra.neg_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：neg_apply (f : IncidenceAlgebra 𝕜 α) (a b : α) : (-f) a b = -f a b
参数：f : IncidenceAlgebra 𝕜 α；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma neg_apply (f : IncidenceAlgebra 𝕜 α) (a b : α) : (-f) a b = -f a b := rfl
/-
**IncidenceAlgebra.sub_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：sub_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f - g) a b = f a b - g
 a b
参数：f g : IncidenceAlgebra 𝕜 α；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sub_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) : (f - g) a b = f a b - g a b := rfl
/-
**IncidenceAlgebra.instAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instAddGroup : AddGroup (IncidenceAlgebra 𝕜 α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IncidenceAlgebra.coe_neg`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : AddGro
up 𝕜] [inst_1 : LE α] (f : IncidenceAlgebra 𝕜 α), ⇑(-f) = -⇑f
· 使用定理 `IncidenceAlgebra.coe_sub`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : AddGro
up 𝕜] [inst_1 : LE α] (f g : IncidenceAlgebra 𝕜 α), ⇑(f - g) = ⇑f - ⇑g
-/
instance instAddGroup : AddGroup (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end AddGroup

/-
**IncidenceAlgebra.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`
。
形式化陈述：instAddCommGroup [AddCommGroup 𝕜] [LE α] : AddCommGroup (IncidenceAlgebra 
𝕜 α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [AddCommGroup 𝕜] [LE α] : AddCommGroup (IncidenceAlgebra 𝕜 α) :=
  DFunLike.coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

section One
variable [Preorder α] [DecidableEq α] [Zero 𝕜] [One 𝕜]

/-- The unit incidence algebra is the delta function, whose entries are `0` except on the diagonal
where they are `1`. -/
/-
**IncidenceAlgebra.instOne** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instOne : One (IncidenceAlgebra 𝕜 α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit incidence algebra is the delta function, whose entries are `0` except o
n the diagonal
where they are `1`.
-/
instance instOne : One (IncidenceAlgebra 𝕜 α) :=
  ⟨⟨fun a b ↦ if a = b then 1 else 0, fun _a _b h ↦ ite_eq_right_iff.2 fun H ↦ (h H.le).elim⟩⟩
/-
**IncidenceAlgebra.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Preorder α] [inst_1 : DecidableEq 
α] [inst_2 : Zero 𝕜] [inst_3 : One 𝕜]   (a b : α), 1 a b = if a = b then 1 else 
0
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_apply (a b : α) : (1 : IncidenceAlgebra 𝕜 α) a b = if a = b then 1 else 0 := rfl

end One

section Mul
variable [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [Mul 𝕜]

/--
The multiplication operation in incidence algebras is defined on an interval by summing over
all divisions into two subintervals the product of the values of the original pair of functions.
-/
/-
**IncidenceAlgebra.instMul** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instMul : Mul (IncidenceAlgebra 𝕜 α) where mul f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication operation in incidence algebras is defined on an interval by 
summing over
all divisions into two subintervals the product of the values of the original pa
ir of functions.
-/
instance instMul : Mul (IncidenceAlgebra 𝕜 α) where
  mul f g :=
    ⟨fun a b ↦ ∑ x ∈ Icc a b, f a x * g x b, fun a b h ↦ by rw [Icc_eq_empty h, sum_empty]⟩
/-
**IncidenceAlgebra.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Preorder α] [inst_1 : LocallyFinit
eOrder α] [inst_2 : AddCommMonoid 𝕜]   [inst_3 : Mul 𝕜] (f g : IncidenceAlgebra 
𝕜 α) (a b : α), (f * g) a b = ∑ x ∈ Finset.Icc a b, f a x * g x b
参数：f g : IncidenceAlgebra 𝕜 α；a b : α；f * g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mul_apply (f g : IncidenceAlgebra 𝕜 α) (a b : α) :
    (f * g) a b = ∑ x ∈ Icc a b, f a x * g x b := rfl

end Mul

/-
**IncidenceAlgebra.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Inci
denceAlgebra`。
形式化陈述：instNonUnitalNonAssocSemiring [Preorder α] [LocallyFiniteOrder α] [NonUnit
alNonAssocSemiring 𝕜] : NonUnitalNonAssocSemiring (IncidenceAlgebra 𝕜 α) where _
_
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocSemiring [Preorder α] [LocallyFiniteOrder α]
    [NonUnitalNonAssocSemiring 𝕜] : NonUnitalNonAssocSemiring (IncidenceAlgebra 𝕜 α) where
  __ := instAddCommMonoid
  zero_mul := fun f ↦ by ext; exact sum_eq_zero fun x _ ↦ zero_mul _
  mul_zero := fun f ↦ by ext; exact sum_eq_zero fun x _ ↦ mul_zero _
  left_distrib := fun f g h ↦ by
    ext; exact Eq.trans (sum_congr rfl fun x _ ↦ left_distrib _ _ _) sum_add_distrib
  right_distrib := fun f g h ↦ by
    ext; exact Eq.trans (sum_congr rfl fun x _ ↦ right_distrib _ _ _) sum_add_distrib
/-
**IncidenceAlgebra.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlge
bra`。
形式化陈述：instNonAssocSemiring [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [
NonAssocSemiring 𝕜] : NonAssocSemiring (IncidenceAlgebra 𝕜 α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocSemiring [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]
    [NonAssocSemiring 𝕜] : NonAssocSemiring (IncidenceAlgebra 𝕜 α) where
  __ := instNonUnitalNonAssocSemiring
  one_mul := fun f ↦ by ext; simp [*]
  mul_one := fun f ↦ by ext; simp [*]
/-
**IncidenceAlgebra.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instSemiring [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring
 𝕜] : Semiring (IncidenceAlgebra 𝕜 α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜] :
    Semiring (IncidenceAlgebra 𝕜 α) where
  __ := instNonAssocSemiring
  mul_assoc f g h := by
    ext a b
    simp only [mul_apply, sum_mul, mul_sum, sum_sigma']
    apply sum_nbij' (fun ⟨a, b⟩ ↦ ⟨b, a⟩) (fun ⟨a, b⟩ ↦ ⟨b, a⟩) <;>
      aesop (add simp mul_assoc) (add unsafe le_trans)
/-
**IncidenceAlgebra.instRing** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instRing [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Ring 𝕜] : Ri
ng (IncidenceAlgebra 𝕜 α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Ring 𝕜] :
    Ring (IncidenceAlgebra 𝕜 α) where
  __ := instSemiring
  __ := instAddGroup

/-! ### Scalar multiplication between incidence algebras -/

section SMul
variable [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [AddCommMonoid 𝕝] [SMul 𝕜 𝕝]

/-
**IncidenceAlgebra.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：instSMul : SMul (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) :=
  ⟨fun f g ↦
    ⟨fun a b ↦ ∑ x ∈ Icc a b, f a x • g x b, fun a b h ↦ by rw [Icc_eq_empty h, sum_empty]⟩⟩

@[simp]
/-
**IncidenceAlgebra.smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：smul_apply (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlgebra 𝕝 α) (a b : α)
 : (f • g) a b = ∑ x in Icc a b, f a x • g x b
参数：f : IncidenceAlgebra 𝕜 α；g : IncidenceAlgebra 𝕝 α；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_apply (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlgebra 𝕝 α) (a b : α) :
    (f • g) a b = ∑ x ∈ Icc a b, f a x • g x b :=
  rfl

end SMul

/-
**IncidenceAlgebra.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra
`。
形式化陈述：instIsScalarTower [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [M
onoid 𝕜] [Semiring 𝕝] [AddCommMonoid 𝕞] [SMul 𝕜 𝕝] [Module 𝕝 𝕞] [DistribMulActio
n 𝕜 𝕞] [IsScalarTower 𝕜 𝕝 𝕞] : IsScalarTower (IncidenceAlgebra 𝕜 α) (IncidenceAl
gebra 𝕝 α) (IncidenceAlgebra 𝕞 α) where smul_assoc f g h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IncidenceAlgebra.ext`：ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : forall a b, 
a <= b -> f a b = g a b) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_nbij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι
 → κ) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower [Preorder α] [LocallyFiniteOrder α] [AddCommMonoid 𝕜] [Monoid 𝕜]
    [Semiring 𝕝] [AddCommMonoid 𝕞] [SMul 𝕜 𝕝] [Module 𝕝 𝕞] [DistribMulAction 𝕜 𝕞]
    [IsScalarTower 𝕜 𝕝 𝕞] :
    IsScalarTower (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) (IncidenceAlgebra 𝕞 α) where
  smul_assoc f g h := by
    ext a b
    simp only [smul_apply, sum_smul, smul_sum, sum_sigma']
    apply sum_nbij' (fun ⟨a, b⟩ ↦ ⟨b, a⟩) (fun ⟨a, b⟩ ↦ ⟨b, a⟩) <;> aesop (add unsafe le_trans)
/-
**IncidenceAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] [LocallyFiniteOrder α] [DecidableEq α] [Semiring 𝕜] [Semiring 𝕝]
    [Module 𝕜 𝕝] : Module (IncidenceAlgebra 𝕜 α) (IncidenceAlgebra 𝕝 α) where
  one_smul f := by ext a b hab; simp [ite_smul, hab]
  mul_smul := smul_assoc
  smul_add f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ ↦ smul_add _ _ _) sum_add_distrib
  add_smul f g h := by ext; exact Eq.trans (sum_congr rfl fun x _ ↦ add_smul _ _ _) sum_add_distrib
  zero_smul f := by ext; exact sum_eq_zero fun x _ ↦ zero_smul _ _
  smul_zero f := by ext; exact sum_eq_zero fun x _ ↦ smul_zero _
/-
**IncidenceAlgebra.smulWithZeroRight** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra
`。
形式化陈述：smulWithZeroRight [Zero 𝕜] [Zero 𝕝] [SMulWithZero 𝕜 𝕝] [LE α] : SMulWithZe
ro 𝕜 (IncidenceAlgebra 𝕝 α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IncidenceAlgebra.coe_zero`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Zero 
𝕜] [inst_1 : LE α], ⇑0 = 0
-/
instance smulWithZeroRight [Zero 𝕜] [Zero 𝕝] [SMulWithZero 𝕜 𝕝] [LE α] :
    SMulWithZero 𝕜 (IncidenceAlgebra 𝕝 α) :=
  DFunLike.coe_injective.smulWithZero ⟨((⇑) : IncidenceAlgebra 𝕝 α → α → α → 𝕝), coe_zero⟩
    coe_constSMul
/-
**IncidenceAlgebra.moduleRight** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：moduleRight [Preorder α] [Semiring 𝕜] [AddCommMonoid 𝕝] [Module 𝕜 𝕝] : Mod
ule 𝕜 (IncidenceAlgebra 𝕝 α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance moduleRight [Preorder α] [Semiring 𝕜] [AddCommMonoid 𝕝] [Module 𝕜 𝕝] :
    Module 𝕜 (IncidenceAlgebra 𝕝 α) :=
  DFunLike.coe_injective.module _ ⟨⟨((⇑) : IncidenceAlgebra 𝕝 α → α → α → 𝕝), coe_zero⟩, coe_add⟩
    coe_constSMul
/-
**IncidenceAlgebra.algebraRight** 是 Mathlib 中的一个实例，位于命名空间 `IncidenceAlgebra`。
形式化陈述：algebraRight [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [Comm
Semiring 𝕜] [CommSemiring 𝕝] [Algebra 𝕜 𝕝] : Algebra 𝕜 (IncidenceAlgebra 𝕝 α) wh
ere algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebraRight [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [CommSemiring 𝕜]
    [CommSemiring 𝕝] [Algebra 𝕜 𝕝] : Algebra 𝕜 (IncidenceAlgebra 𝕝 α) where
  algebraMap :=
  { toFun c := algebraMap 𝕜 𝕝 c • (1 : IncidenceAlgebra 𝕝 α)
    map_one' := by
      ext; simp only [mul_boole, one_apply, smul_eq_mul, constSMul_apply, map_one]
    map_mul' c d := by
        ext a b
        obtain rfl | h := eq_or_ne a b
        · simp only [one_apply, smul_eq_mul, mul_apply, constSMul_apply, map_mul,
            eq_comm, Icc_self]
          simp
        · simp only [one_apply, mul_one, smul_eq_mul, mul_apply, zero_mul,
            constSMul_apply, ← ite_and, ite_mul, mul_ite, map_mul, mul_zero, if_neg h]
          refine (sum_eq_zero fun x _ ↦ ?_).symm
          exact if_neg fun hx ↦ h <| hx.2.trans hx.1
    map_zero' := by rw [map_zero, zero_smul]
    map_add' c d := by rw [map_add, add_smul] }
  commutes' c f := by classical ext a b hab; simp [if_pos hab, constSMul_apply, mul_comm]
  smul_def' c f := by classical ext a b hab; simp [if_pos hab, constSMul_apply, Algebra.smul_def]

/-! ### The Lambda function -/

section Lambda
variable (𝕜) [Zero 𝕜] [One 𝕜] [Preorder α] [DecidableRel (α := α) (· ⩿ ·)]

/-- The lambda function of the incidence algebra is the function that assigns `1` to every nonempty
interval of cardinality one or two. -/
@[simps]
/-
**IncidenceAlgebra.lambda** 是 Mathlib 中的一个定义，位于命名空间 `IncidenceAlgebra`。
形式化陈述：lambda : IncidenceAlgebra 𝕜 α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lambda function of the incidence algebra is the function that assigns `1` to
 every nonempty
interval of cardinality one or two.
-/
def lambda : IncidenceAlgebra 𝕜 α :=
  ⟨fun a b ↦ if a ⩿ b then 1 else 0, fun _a _b h ↦ if_neg fun hh ↦ h hh.le⟩

end Lambda

/-! ### The Zeta and Möbius functions -/

section Zeta
variable (𝕜) [Zero 𝕜] [One 𝕜] [LE α] [DecidableLE α] {a b : α}

/-- The zeta function of the incidence algebra is the function that assigns 1 to every nonempty
interval, convolution with this function sums functions over intervals. -/
/-
**IncidenceAlgebra.zeta** 是 Mathlib 中的一个定义，位于命名空间 `IncidenceAlgebra`。
形式化陈述：zeta : IncidenceAlgebra 𝕜 α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zeta function of the incidence algebra is the function that assigns 1 to eve
ry nonempty
interval, convolution with this function sums functions over intervals.
-/
def zeta : IncidenceAlgebra 𝕜 α := ⟨fun a b ↦ if a ≤ b then 1 else 0, fun _a _b h ↦ if_neg h⟩

variable {𝕜}
/-
**IncidenceAlgebra.zeta_apply** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Zero 𝕜] [inst_1 : One 𝕜] [inst_2 :
 LE α] [inst_3 : DecidableLE α] (a b : α),   (IncidenceAlgebra.zeta 𝕜) a b = if 
a ≤ b then 1 else 0
参数：a b : α；IncidenceAlgebra.zeta 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zeta_apply (a b : α) : zeta 𝕜 a b = if a ≤ b then 1 else 0 := rfl
/-
**IncidenceAlgebra.zeta_of_le** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：zeta_of_le (h : a <= b) : zeta 𝕜 a b = 1
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
lemma zeta_of_le (h : a ≤ b) : zeta 𝕜 a b = 1 := if_pos h

end Zeta

/-
**IncidenceAlgebra.zeta_mul_zeta** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：zeta_mul_zeta [NonAssocSemiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [De
cidableLE α] (a b : α) : (zeta 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) a b = (Icc a b
).card
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IncidenceAlgebra.mul_apply`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Preo
rder α] [inst_1 : LocallyFiniteOrder α] [inst_2 : AddCommMonoid 𝕜]   [inst_3 : M
ul 𝕜] (f g : Inc…
· 使用引理 `Finset.card_eq_sum_ones`：card_eq_sum_ones (s : Finset ι) : #s = ∑ _ in s
, 1
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `IncidenceAlgebra.zeta_of_le`：zeta_of_le (h : a <= b) : zeta 𝕜 a b = 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma zeta_mul_zeta [NonAssocSemiring 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableLE α]
    (a b : α) : (zeta 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) a b = (Icc a b).card := by
  rw [mul_apply, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine sum_congr rfl fun x hx ↦ ?_
  rw [mem_Icc] at hx
  rw [zeta_of_le hx.1, zeta_of_le hx.2, one_mul]

section Mu
variable (𝕜) [AddCommGroup 𝕜] [One 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]

set_option backward.privateInPublic true in
/-- The Möbius function of the incidence algebra as a bare function defined recursively. -/
/-
**IncidenceAlgebra.muFun** 是 Mathlib 中的一个定义，位于命名空间 `IncidenceAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Möbius function of the incidence algebra as a bare function defined recursiv
ely.
-/
private def muFun (a : α) : α → 𝕜
  | b =>
    if a = b then 1
    else
      -∑ x ∈ (Ico a b).attach,
          let h := mem_Ico.1 x.2
          have : (Icc a x).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_right (h.1.trans h.2.le) le_rfl h.2)
          muFun a x
termination_by b => (Icc a b).card
/-
**IncidenceAlgebra.muFun_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma muFun_apply (a b : α) :
    muFun 𝕜 a b = if a = b then 1 else -∑ x ∈ (Ico a b).attach, muFun 𝕜 a x := by rw [muFun]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The Möbius function which inverts `zeta` as an element of the incidence algebra. -/
/-
**IncidenceAlgebra.mu** 是 Mathlib 中的一个定义，位于命名空间 `IncidenceAlgebra`。
形式化陈述：mu : IncidenceAlgebra 𝕜 α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Möbius function which inverts `zeta` as an element of the incidence algebra.
-/
def mu : IncidenceAlgebra 𝕜 α :=
  ⟨muFun 𝕜, fun a b ↦ not_imp_comm.1 fun h ↦ by
    rw [muFun_apply] at h
    split_ifs at h with hab
    · exact hab.le
    · rw [neg_eq_zero] at h
      obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
      exact (nonempty_Ico.1 ⟨x, hx⟩).le⟩

variable {𝕜} {a b : α}
/-
**IncidenceAlgebra.mu_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：mu_apply (a b : α) : mu 𝕜 a b = if a = b then 1 else -∑ x in Ico a b, mu 𝕜
 a x
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IncidenceAlgebra.mu.eq_1`：∀ (𝕜 : Type u_2) {α : Type u_5} [inst : AddCom
mGroup 𝕜] [inst_1 : One 𝕜] [inst_2 : Preorder α]   [inst_3 : LocallyFiniteOrder 
α] [inst_4 : D…
· 使用定理 `IncidenceAlgebra.coe_mk`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Zero 𝕜]
 [inst_1 : LE α] (f : α → α → 𝕜) (h : ∀ ⦃a b : α⦄, ¬a ≤ b → f a b = 0),   ⇑{ toF
un := f, eq_z…
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.IncidenceAlgebra.0.IncidenceA
lgebra.muFun_apply`：∀ (𝕜 : Type u_2) {α : Type u_5} [inst : AddCommGroup 𝕜] [ins
t_1 : One 𝕜] [inst_2 : Preorder α]   [inst_3 : LocallyFiniteOrder α] [inst_4 : D
…
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
-/
lemma mu_apply (a b : α) : mu 𝕜 a b = if a = b then 1 else -∑ x ∈ Ico a b, mu 𝕜 a x := by
  rw [mu, coe_mk, muFun_apply, sum_attach]
/-
**IncidenceAlgebra.mu_self** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : AddCommGroup 𝕜] [inst_1 : One 𝕜] [
inst_2 : Preorder α]   [inst_3 : LocallyFiniteOrder α] [inst_4 : DecidableEq α] 
(a : α), (IncidenceAlgebra.mu 𝕜) a a = 1
参数：a : α；IncidenceAlgebra.mu 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IncidenceAlgebra.mu_apply`：mu_apply (a b : α) : mu 𝕜 a b = if a = b then
 1 else -∑ x in Ico a b, mu 𝕜 a x
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma mu_self (a : α) : mu 𝕜 a a = 1 := by simp [mu_apply]
/-
**IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceA
lgebra`。
形式化陈述：mu_eq_neg_sum_Ico_of_ne (hab : a != b) : mu 𝕜 a b = -∑ x in Ico a b, mu 𝕜 
a x
参数：hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IncidenceAlgebra.mu_apply`：mu_apply (a b : α) : mu 𝕜 a b = if a = b then
 1 else -∑ x in Ico a b, mu 𝕜 a x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma mu_eq_neg_sum_Ico_of_ne (hab : a ≠ b) :
    mu 𝕜 a b = -∑ x ∈ Ico a b, mu 𝕜 a x := by rw [mu_apply, if_neg hab]

variable (𝕜 α)
/-- The Euler characteristic of a finite bounded order. -/
/-
**IncidenceAlgebra.eulerChar** 是 Mathlib 中的一个定义，位于命名空间 `IncidenceAlgebra`。
形式化陈述：eulerChar [BoundedOrder α] : 𝕜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Euler characteristic of a finite bounded order.
-/
def eulerChar [BoundedOrder α] : 𝕜 := mu 𝕜 (⊥ : α) ⊤

end Mu

section MuSpec
variable [AddCommGroup 𝕜] [One 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

/-
**IncidenceAlgebra.sum_Icc_mu_right** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`
。
形式化陈述：sum_Icc_mu_right (a b : α) : ∑ x in Icc a b, mu 𝕜 a x = if a = b then 1 el
se 0
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `IncidenceAlgebra.mu_self`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : AddCom
mGroup 𝕜] [inst_1 : One 𝕜] [inst_2 : Preorder α]   [inst_3 : LocallyFiniteOrder 
α] [inst_4 : D…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.right_notMem_Ico`：right_notMem_Ico : b ∉ Ico a b
· 使用定理 `Finset.Icc_eq_cons_Ico`：Icc_eq_cons_Ico (h : a <= b) : Icc a b = (Ico a 
b).cons b right_notMem_Ico
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne`：mu_eq_neg_sum_Ico_of_ne (hab :
 a != b) : mu 𝕜 a b = -∑ x in Ico a b, mu 𝕜 a x
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用引理 `IncidenceAlgebra.apply_eq_zero_of_not_le`：apply_eq_zero_of_not_le (h : ¬
a <= b) (f : IncidenceAlgebra 𝕜 α) : f a b = 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
-/
lemma sum_Icc_mu_right (a b : α) : ∑ x ∈ Icc a b, mu 𝕜 a x = if a = b then 1 else 0 := by
  split_ifs with hab
  · simp [hab]
  by_cases hab : a ≤ b
  · simp [Icc_eq_cons_Ico hab, mu_eq_neg_sum_Ico_of_ne ‹_›]
  · exact sum_eq_zero fun x hx ↦ apply_eq_zero_of_not_le
      (fun hax ↦ hab <| hax.trans (mem_Icc.1 hx).2) _

end MuSpec

section Mu'
variable (𝕜) [AddCommGroup 𝕜] [One 𝕜] [Preorder α] [LocallyFiniteOrder α] [DecidableEq α]

/-- `mu'` as a bare function defined recursively. -/
/-
**IncidenceAlgebra.muFun'** 是 Mathlib 中的一个定义，位于命名空间 `IncidenceAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mu'` as a bare function defined recursively.
-/
private def muFun' (b : α) : α → 𝕜
  | a =>
    if a = b then 1
    else
      -∑ x ∈ (Ioc a b).attach,
          let h := mem_Ioc.1 x.2
          have : (Icc ↑x b).card < (Icc a b).card :=
            card_lt_card (Icc_ssubset_Icc_left (h.1.le.trans h.2) h.1 le_rfl)
          muFun' b x
termination_by a => (Icc a b).card
/-
**IncidenceAlgebra.muFun'_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma muFun'_apply (a b : α) :
    muFun' 𝕜 b a = if a = b then 1 else -∑ x ∈ (Ioc a b).attach, muFun' 𝕜 b x := by
  rw [muFun']

/-- This is the reversed definition of `mu`, which is equal to `mu` but easiest to prove equal by
showing that `zeta * mu = 1` and `mu' * zeta = 1`. -/
/-
**IncidenceAlgebra.mu'** 是 Mathlib 中的一个定义，位于命名空间 `IncidenceAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the reversed definition of `mu`, which is equal to `mu` but easiest to p
rove equal by
showing that `zeta * mu = 1` and `mu' * zeta = 1`.
-/
private def mu' : IncidenceAlgebra 𝕜 α :=
  ⟨fun a b ↦ muFun' 𝕜 b a, fun a b ↦
    not_imp_comm.1 fun h ↦ by
      rw [muFun'_apply] at h
      split_ifs at h with hab
      · exact hab.le
      · rw [neg_eq_zero] at h
        obtain ⟨⟨x, hx⟩, -⟩ := exists_ne_zero_of_sum_ne_zero h
        exact (nonempty_Ioc.1 ⟨x, hx⟩).le⟩

variable {𝕜} {a b : α}
/-
**IncidenceAlgebra.mu'_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mu'_apply (a b : α) : mu' 𝕜 a b = if a = b then 1 else -∑ x ∈ Ioc a b, mu' 𝕜 x b := by
  rw [mu', coe_mk, muFun'_apply, sum_attach]
/-
**IncidenceAlgebra.mu'_apply_self** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma mu'_apply_self (a : α) : mu' 𝕜 a a = 1 := by simp [mu'_apply]
/-
**IncidenceAlgebra.mu'_eq_sum_Ioc_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlge
bra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mu'_eq_sum_Ioc_of_ne (h : a ≠ b) : mu' 𝕜 a b = -∑ x ∈ Ioc a b, mu' 𝕜 x b := by
  rw [mu'_apply, if_neg h]

end Mu'

section Mu'Spec
variable [AddCommGroup 𝕜] [One 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

/-
**IncidenceAlgebra.sum_Icc_mu'_left** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma sum_Icc_mu'_left (a b : α) : ∑ x ∈ Icc a b, mu' 𝕜 x b = if a = b then 1 else 0 := by
  split_ifs with hab
  · simp [hab]
  by_cases hab : a ≤ b
  · simp [Icc_eq_cons_Ioc hab, mu'_eq_sum_Ioc_of_ne ‹_›]
  · exact sum_eq_zero fun x hx ↦ apply_eq_zero_of_not_le
      (fun hxb ↦ hab <| (mem_Icc.1 hx).1.trans hxb) _

end Mu'Spec

section MuZeta
variable (𝕜 α) [AddCommGroup 𝕜] [MulOneClass 𝕜] [PartialOrder α] [LocallyFiniteOrder α]
  [DecidableEq α] [DecidableLE α]

/-
**IncidenceAlgebra.mu_mul_zeta** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：mu_mul_zeta : (mu 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IncidenceAlgebra.ext`：ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : forall a b, 
a <= b -> f a b = g a b) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IncidenceAlgebra.mul_apply`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Preo
rder α] [inst_1 : LocallyFiniteOrder α] [inst_2 : AddCommMonoid 𝕜]   [inst_3 : M
ul 𝕜] (f g : Inc…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IncidenceAlgebra.sum_Icc_mu_right`：sum_Icc_mu_right (a b : α) : ∑ x in I
cc a b, mu 𝕜 a x = if a = b then 1 else 0
-/
lemma mu_mul_zeta : (mu 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  ext a b
  calc
    _ = ∑ x ∈ Icc a b, mu 𝕜 a x := by rw [mul_apply]; congr! with x hx; simp [(mem_Icc.1 hx).2]
    _ = (1 : IncidenceAlgebra 𝕜 α) a b := sum_Icc_mu_right ..
/-
**IncidenceAlgebra.zeta_mul_mu'** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma zeta_mul_mu' : (zeta 𝕜 * mu' 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  ext a b
  calc
    _ = ∑ x ∈ Icc a b, mu' 𝕜 x b := by rw [mul_apply]; congr! with x hx; simp [(mem_Icc.1 hx).1]
    _ = (1 : IncidenceAlgebra 𝕜 α) a b := sum_Icc_mu'_left ..

end MuZeta

section MuEqMu'
variable [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] {a b : α}

/-
**IncidenceAlgebra.mu_eq_mu'** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mu_eq_mu' : (mu 𝕜 : IncidenceAlgebra 𝕜 α) = mu' 𝕜 := by
  classical
  exact left_inv_eq_right_inv (mu_mul_zeta _ _) (zeta_mul_mu' _ _)
/-
**IncidenceAlgebra.mu_eq_neg_sum_Ioc_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceA
lgebra`。
形式化陈述：mu_eq_neg_sum_Ioc_of_ne (hab : a != b) : mu 𝕜 a b = -∑ x in Ioc a b, mu 𝕜 
x b
参数：hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.IncidenceAlgebra.0.IncidenceA
lgebra.mu_eq_mu'`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Ring 𝕜] [inst_1 : Part
ialOrder α] [inst_2 : LocallyFiniteOrder α]   [inst_3 : DecidableEq α], Incide…
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.IncidenceAlgebra.0.IncidenceA
lgebra.mu'_eq_sum_Ioc_of_ne`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : AddCommGrou
p 𝕜] [inst_1 : One 𝕜] [inst_2 : Preorder α]   [inst_3 : LocallyFiniteOrder α] [i
nst_4 : D…
-/
lemma mu_eq_neg_sum_Ioc_of_ne (hab : a ≠ b) : mu 𝕜 a b = -∑ x ∈ Ioc a b, mu 𝕜 x b := by
  rw [mu_eq_mu', mu'_eq_sum_Ioc_of_ne hab]
/-
**IncidenceAlgebra.zeta_mul_mu** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：zeta_mul_mu [DecidableLE α] : (zeta 𝕜 * mu 𝕜 : IncidenceAlgebra 𝕜 α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.IncidenceAlgebra.0.IncidenceA
lgebra.mu_eq_mu'`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Ring 𝕜] [inst_1 : Part
ialOrder α] [inst_2 : LocallyFiniteOrder α]   [inst_3 : DecidableEq α], Incide…
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.IncidenceAlgebra.0.IncidenceA
lgebra.zeta_mul_mu'`：∀ (𝕜 : Type u_2) (α : Type u_5) [inst : AddCommGroup 𝕜] [in
st_1 : MulOneClass 𝕜] [inst_2 : PartialOrder α]   [inst_3 : LocallyFiniteOrder α
]…
-/
lemma zeta_mul_mu [DecidableLE α] : (zeta 𝕜 * mu 𝕜 : IncidenceAlgebra 𝕜 α) = 1 := by
  rw [mu_eq_mu', zeta_mul_mu']
/-
**IncidenceAlgebra.sum_Icc_mu_left** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：sum_Icc_mu_left (a b : α) : ∑ x in Icc a b, mu 𝕜 x b = if a = b then 1 els
e 0
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.IncidenceAlgebra.0.IncidenceA
lgebra.mu_eq_mu'`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Ring 𝕜] [inst_1 : Part
ialOrder α] [inst_2 : LocallyFiniteOrder α]   [inst_3 : DecidableEq α], Incide…
· 使用定理 `_private.Mathlib.Combinatorics.Enumerative.IncidenceAlgebra.0.IncidenceA
lgebra.sum_Icc_mu'_left`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : AddCommGroup 𝕜]
 [inst_1 : One 𝕜] [inst_2 : PartialOrder α]   [inst_3 : LocallyFiniteOrder α] [i
nst_4…
-/
lemma sum_Icc_mu_left (a b : α) : ∑ x ∈ Icc a b, mu 𝕜 x b = if a = b then 1 else 0 := by
  rw [mu_eq_mu', sum_Icc_mu'_left]

end MuEqMu'

section OrderDual
variable (𝕜) [Ring 𝕜] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

@[simp]
/-
**IncidenceAlgebra.mu_toDual** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：mu_toDual (a b : α) : mu 𝕜 (toDual a) (toDual b) = mu 𝕜 b a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IncidenceAlgebra.apply_eq_zero_of_not_le`：apply_eq_zero_of_not_le (h : ¬
a <= b) (f : IncidenceAlgebra 𝕜 α) : f a b = 0
· 使用引理 `IncidenceAlgebra.ext`：ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : forall a b, 
a <= b -> f a b = g a b) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Icc`：mem_Icc : x in Icc a b ↔ a <= x ∧ x <= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.Icc_orderDual_def`：Finset.Icc_orderDual_def (a b : αᵒᵈ) : Icc a b
 = (Icc (ofDual b) (ofDual a)).map toDual.toEmbedding
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IncidenceAlgebra.sum_Icc_mu_left`：sum_Icc_mu_left (a b : α) : ∑ x in Icc
 a b, mu 𝕜 x b = if a = b then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `IncidenceAlgebra.zeta_mul_mu`：zeta_mul_mu [DecidableLE α] : (zeta 𝕜 * mu
 𝕜 : IncidenceAlgebra 𝕜 α) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `IncidenceAlgebra.mu_mul_zeta`：mu_mul_zeta : (mu 𝕜 * zeta 𝕜 : IncidenceAl
gebra 𝕜 α) = 1
-/
lemma mu_toDual (a b : α) : mu 𝕜 (toDual a) (toDual b) = mu 𝕜 b a := by
  let : DecidableLE α := Classical.decRel _
  let mud : IncidenceAlgebra 𝕜 αᵒᵈ :=
    { toFun := fun a b ↦ mu 𝕜 (ofDual b) (ofDual a)
      eq_zero_of_not_le' := fun a b hab ↦ apply_eq_zero_of_not_le (by exact hab) _ }
  suffices mu 𝕜 = mud by simp_rw [this, mud, coe_mk, ofDual_toDual]
  suffices mud * zeta 𝕜 = 1 by
    rw [← mu_mul_zeta] at this
    apply_fun (· * mu 𝕜) at this
    symm
    simpa [mul_assoc, zeta_mul_mu] using this
  clear a b
  ext a b
  simp only [mul_boole, one_apply, mul_apply, zeta_apply]
  calc
    ∑ x ∈ Icc a b, (if x ≤ b then mud a x else 0) = ∑ x ∈ Icc a b, mud a x := by
      congr! with x hx; exact if_pos (mem_Icc.1 hx).2
    _ = ∑ x ∈ Icc (ofDual b) (ofDual a), mu 𝕜 x (ofDual a) := by simp [Icc_orderDual_def, mud]
    _ = if ofDual b = ofDual a then 1 else 0 := sum_Icc_mu_left ..
    _ = if a = b then 1 else 0 := by simp [eq_comm]
/-
**IncidenceAlgebra.mu_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ (𝕜 : Type u_2) {α : Type u_5} [inst : Ring 𝕜] [inst_1 : PartialOrder α] 
[inst_2 : LocallyFiniteOrder α]   [inst_3 : DecidableEq α] (a b : αᵒᵈ),   (Incid
enceAlgebra.mu 𝕜) (OrderDual.ofDual a) (OrderDual.ofDual b) = (IncidenceAlgebra.
mu 𝕜) b a
参数：𝕜 : Type u_2；a b : αᵒᵈ；IncidenceAlgebra.mu 𝕜；OrderDual.ofDual a；OrderDual.ofD
ual b；IncidenceAlgebra.mu 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IncidenceAlgebra.mu_toDual`：mu_toDual (a b : α) : mu 𝕜 (toDual a) (toDua
l b) = mu 𝕜 b a
-/
@[simp] lemma mu_ofDual (a b : αᵒᵈ) : mu 𝕜 (ofDual a) (ofDual b) = mu 𝕜 b a := (mu_toDual ..).symm

@[simp]
/-
**IncidenceAlgebra.eulerChar_orderDual** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgeb
ra`。
形式化陈述：eulerChar_orderDual [BoundedOrder α] : eulerChar 𝕜 αᵒᵈ = eulerChar 𝕜 α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IncidenceAlgebra.mu_toDual`：mu_toDual (a b : α) : mu 𝕜 (toDual a) (toDua
l b) = mu 𝕜 b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eulerChar_orderDual [BoundedOrder α] : eulerChar 𝕜 αᵒᵈ = eulerChar 𝕜 α := by
  simp [eulerChar, ← mu_toDual 𝕜 (α := α)]

end OrderDual

section InversionTop
variable [Ring 𝕜] [PartialOrder α] [OrderTop α] [LocallyFiniteOrder α] [DecidableEq α] {a b : α}

/-- A general form of Möbius inversion. Based on lemma 2.1.2 of Incidence Algebras by Spiegel and
O'Donnell. -/
/-
**IncidenceAlgebra.moebius_inversion_top** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlg
ebra`。
形式化陈述：moebius_inversion_top (f g : α -> 𝕜) (h : forall x, g x = ∑ y in Ici x, f 
y) (x : α) : f x = ∑ y in Ici x, mu 𝕜 x y * g y
参数：f g : α -> 𝕜；h : forall x, g x = ∑ y in Ici x, f y；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IncidenceAlgebra.zeta_apply`：∀ {𝕜 : Type u_2} {α : Type u_5} [inst : Zer
o 𝕜] [inst_1 : One 𝕜] [inst_2 : LE α] [inst_3 : DecidableLE α] (a b : α),   (Inc
idenceAlgebra.zet…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ici`：mem_Ici : x in Ici a ↔ a <= x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `Finset.sum_nbij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst :
 AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι
 → κ) …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Sigma.eta`：∀ {α : Type u_1} {β : α → Type u_4} (x : (a : α) × β a), ⟨x.f
st, x.snd⟩ = x
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
A general form of Möbius inversion. Based on lemma 2.1.2 of Incidence Algebras b
y Spiegel and
O'Donnell.
-/
lemma moebius_inversion_top (f g : α → 𝕜) (h : ∀ x, g x = ∑ y ∈ Ici x, f y) (x : α) :
    f x = ∑ y ∈ Ici x, mu 𝕜 x y * g y := by
  let : DecidableLE α := Classical.decRel _
  symm
  calc
    ∑ y ∈ Ici x, mu 𝕜 x y * g y = ∑ y ∈ Ici x, mu 𝕜 x y * ∑ z ∈ Ici y, f z := by simp_rw [h]
    _ = ∑ y ∈ Ici x, mu 𝕜 x y * ∑ z ∈ Ici y, zeta 𝕜 y z * f z := by
      congr with y
      rw [sum_congr rfl fun z hz ↦ ?_]
      rw [zeta_apply, if_pos (mem_Ici.mp ‹_›), one_mul]
    _ = ∑ y ∈ Ici x, ∑ z ∈ Ici y, mu 𝕜 x y * zeta 𝕜 y z * f z := by simp [mul_sum]
    _ = ∑ z ∈ Ici x, ∑ y ∈ Icc x z, mu 𝕜 x y * zeta 𝕜 y z * f z := by
      rw [sum_sigma' (Ici x) fun y ↦ Ici y]
      rw [sum_sigma' (Ici x) fun z ↦ Icc x z]
      simp only [mul_boole, zero_mul, ite_mul, zeta_apply]
      apply sum_nbij' (fun ⟨a, b⟩ ↦ ⟨b, a⟩) (fun ⟨a, b⟩ ↦ ⟨b, a⟩) <;>
        aesop (add simp mul_assoc) (add unsafe le_trans)
    _ = ∑ z ∈ Ici x, (mu 𝕜 * zeta 𝕜 : IncidenceAlgebra 𝕜 α) x z * f z := by
      simp_rw [mul_apply, sum_mul]
    _ = ∑ y ∈ Ici x, ∑ z ∈ Ici y, (1 : IncidenceAlgebra 𝕜 α) x z * f z := by
      simp only [mu_mul_zeta 𝕜, one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_Ici, le_refl,
        ↓reduceIte, ← add_sum_Ioi_eq_sum_Ici, left_eq_add]
      exact sum_eq_zero fun y hy ↦ if_neg (mem_Ioi.mp hy).not_ge
    _ = f x := by
      simp only [one_apply, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_Ici,
        ← add_sum_Ioi_eq_sum_Ici, le_refl, ↓reduceIte, add_eq_left]
      exact sum_eq_zero fun y hy ↦ if_neg (mem_Ioi.mp hy).not_ge

end InversionTop

section InversionBot
variable [Ring 𝕜] [PartialOrder α] [OrderBot α] [LocallyFiniteOrder α] [DecidableEq α]

set_option backward.isDefEq.respectTransparency false in
/-- A general form of Möbius inversion. Based on lemma 2.1.3 of Incidence Algebras by Spiegel and
O'Donnell. -/
/-
**IncidenceAlgebra.moebius_inversion_bot** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlg
ebra`。
形式化陈述：moebius_inversion_bot (f g : α -> 𝕜) (h : forall x, g x = ∑ y in Iic x, f 
y) (x : α) : f x = ∑ y in Iic x, mu 𝕜 y x * g y
参数：f g : α -> 𝕜；h : forall x, g x = ∑ y in Iic x, f y；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IncidenceAlgebra.mu_toDual`：mu_toDual (a b : α) : mu 𝕜 (toDual a) (toDua
l b) = mu 𝕜 b a
· 使用引理 `IncidenceAlgebra.moebius_inversion_top`：moebius_inversion_top (f g : α -
> 𝕜) (h : forall x, g x = ∑ y in Ici x, f y) (x : α) : f x = ∑ y in Ici x, mu 𝕜 
x y * g y

--- 原说明 ---
A general form of Möbius inversion. Based on lemma 2.1.3 of Incidence Algebras b
y Spiegel and
O'Donnell.
-/
lemma moebius_inversion_bot (f g : α → 𝕜) (h : ∀ x, g x = ∑ y ∈ Iic x, f y) (x : α) :
    f x = ∑ y ∈ Iic x, mu 𝕜 y x * g y := by
  convert! moebius_inversion_top (α := αᵒᵈ) f g h x using 3
  rw [← mu_toDual]; rfl

end InversionBot

section Prod

section Preorder

section Ring
variable (𝕜) [Ring 𝕜] [Preorder α] [Preorder β]

section DecidableLe
variable [DecidableLE α] [DecidableLE β]

/-
**IncidenceAlgebra.zeta_prod_apply** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：zeta_prod_apply (a b : α × β) : zeta 𝕜 a b = zeta 𝕜 a.1 b.1 * zeta 𝕜 a.2 b
.2
参数：a b : α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zeta_prod_apply (a b : α × β) : zeta 𝕜 a b = zeta 𝕜 a.1 b.1 * zeta 𝕜 a.2 b.2 := by
  simp [← ite_and, Prod.le_def, and_comm]
/-
**IncidenceAlgebra.zeta_prod_mk** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：zeta_prod_mk (a₁ a₂ : α) (b₁ b₂ : β) : zeta 𝕜 (a₁, b₁) (a₂, b₂) = zeta 𝕜 a
₁ a₂ * zeta 𝕜 b₁ b₂
参数：a₁ a₂ : α；b₁ b₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IncidenceAlgebra.zeta_prod_apply`：zeta_prod_apply (a b : α × β) : zeta 𝕜
 a b = zeta 𝕜 a.1 b.1 * zeta 𝕜 a.2 b.2
-/
lemma zeta_prod_mk (a₁ a₂ : α) (b₁ b₂ : β) :
    zeta 𝕜 (a₁, b₁) (a₂, b₂) = zeta 𝕜 a₁ a₂ * zeta 𝕜 b₁ b₂ := zeta_prod_apply _ _ _

end DecidableLe

variable {𝕜} (f f₁ f₂ : IncidenceAlgebra 𝕜 α) (g g₁ g₂ : IncidenceAlgebra 𝕜 β)

/-- The Cartesian product of two incidence algebras. -/
/-
**IncidenceAlgebra.prod** 是 Mathlib 中的一个定义，位于命名空间 `IncidenceAlgebra`。
形式化陈述：{𝕜 : Type u_2} →   {α : Type u_5} →     {β : Type u_6} →       [inst : Rin
g 𝕜] →         [inst_1 : Preorder α] →           [inst_2 : Preorder β] → Inciden
ceAlgebra 𝕜 α → IncidenceAlgebra 𝕜 β → IncidenceAlgebra 𝕜 (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Cartesian product of two incidence algebras.
-/
protected def prod : IncidenceAlgebra 𝕜 (α × β) where
  toFun x y := f x.1 y.1 * g x.2 y.2
  eq_zero_of_not_le' x y hxy := by
    rw [Prod.le_def, not_and_or] at hxy
    obtain hxy | hxy := hxy <;> simp [apply_eq_zero_of_not_le hxy]
/-
**IncidenceAlgebra.prod_mk** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：prod_mk (a₁ a₂ : α) (b₁ b₂ : β) : f.prod g (a₁, b₁) (a₂, b₂) = f a₁ a₂ * g
 b₁ b₂
参数：a₁ a₂ : α；b₁ b₂ : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_mk (a₁ a₂ : α) (b₁ b₂ : β) : f.prod g (a₁, b₁) (a₂, b₂) = f a₁ a₂ * g b₁ b₂ := rfl
/-
**IncidenceAlgebra.prod_apply** 是 Mathlib 中的一个定理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：∀ {𝕜 : Type u_2} {α : Type u_5} {β : Type u_6} [inst : Ring 𝕜] [inst_1 : P
reorder α] [inst_2 : Preorder β]   (f : IncidenceAlgebra 𝕜 α) (g : IncidenceAlge
bra 𝕜 β) (x y : α × β), (f.prod g) x y = f x.1 y.1 * g x.2 y.2
参数：f : IncidenceAlgebra 𝕜 α；g : IncidenceAlgebra 𝕜 β；x y : α × β；f.prod g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma prod_apply (x y : α × β) : f.prod g x y = f x.1 y.1 * g x.2 y.2 := rfl

/-- This is a version of `IncidenceAlgebra.prod_mul_prod` that works over non-commutative rings. -/
/-
**IncidenceAlgebra.prod_mul_prod'** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：prod_mul_prod' [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableLE 
(α × β)] (h : forall a₁ a₂ a₃ b₁ b₂ b₃, f₁ a₁ a₂ * g₁ b₁ b₂ * (f₂ a₂ a₃ * g₂ b₂ 
b₃) = f₁ a₁ a₂ * f₂ a₂ a₃ * (g₁ b₁ b₂ * g₂ b₂ b₃)) : f₁.prod g₁ * f₂.prod g₂ = (
f₁ * f₂).prod (g₁ * g₂)
参数：α × β；h : forall a₁ a₂ a₃ b₁ b₂ b₃, f₁ a₁ a₂ * g₁ b₁ b₂ * (f₂ a₂ a₃ * g₂ b₂ b
₃) = f₁ a₁ a₂ * f₂ a₂ a₃ * (g₁ b₁ b₂ * g₂ b₂ b₃)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IncidenceAlgebra.ext`：ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : forall a b, 
a <= b -> f a b = g a b) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_product`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst
 : AddCommMonoid β] (s : Finset γ) (t : Finset α) (f : γ × α → β),   ∑ x ∈ s ×ˢ 
t, f x =…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.sum_mul_sum`：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> 
R) (g : κ -> R) : (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g 
j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This is a version of `IncidenceAlgebra.prod_mul_prod` that works over non-commut
ative rings.
-/
lemma prod_mul_prod' [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableLE (α × β)]
    (h : ∀ a₁ a₂ a₃ b₁ b₂ b₃,
        f₁ a₁ a₂ * g₁ b₁ b₂ * (f₂ a₂ a₃ * g₂ b₂ b₃) = f₁ a₁ a₂ * f₂ a₂ a₃ * (g₁ b₁ b₂ * g₂ b₂ b₃)) :
    f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂) := by
  ext x y; simp [Icc_prod_def, sum_mul_sum, h, sum_product]

@[simp]
/-
**IncidenceAlgebra.one_prod_one** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：one_prod_one [DecidableEq α] [DecidableEq β] : (.prod 1 1 : IncidenceAlgeb
ra 𝕜 (α × β)) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IncidenceAlgebra.ext`：ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : forall a b, 
a <= b -> f a b = g a b) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_prod_one [DecidableEq α] [DecidableEq β] :
    (.prod 1 1 : IncidenceAlgebra 𝕜 (α × β)) = 1 := by
  ext x y; simp [Prod.ext_iff, ← ite_and, and_comm]

@[simp]
/-
**IncidenceAlgebra.zeta_prod_zeta** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：zeta_prod_zeta [DecidableLE α] [DecidableLE β] : (zeta 𝕜).prod (zeta 𝕜) = 
(zeta 𝕜 : IncidenceAlgebra 𝕜 (α × β))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IncidenceAlgebra.ext`：ext ⦃f g : IncidenceAlgebra 𝕜 α⦄ (h : forall a b, 
a <= b -> f a b = g a b) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zeta_prod_zeta [DecidableLE α] [DecidableLE β] :
    (zeta 𝕜).prod (zeta 𝕜) = (zeta 𝕜 : IncidenceAlgebra 𝕜 (α × β)) := by
  ext x y hxy; simp [hxy, hxy.1, hxy.2]

end Ring

section CommRing
variable [CommRing 𝕜] [Preorder α] [Preorder β] [LocallyFiniteOrder α] [LocallyFiniteOrder β]
  [DecidableLE (α × β)] (f₁ f₂ : IncidenceAlgebra 𝕜 α) (g₁ g₂ : IncidenceAlgebra 𝕜 β)

@[simp]
/-
**IncidenceAlgebra.prod_mul_prod** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：prod_mul_prod : f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IncidenceAlgebra.prod_mul_prod'`：prod_mul_prod' [LocallyFiniteOrder α] [
LocallyFiniteOrder β] [DecidableLE (α × β)] (h : forall a₁ a₂ a₃ b₁ b₂ b₃, f₁ a₁
 a₂ * g₁ b₁ b₂ * (f₂ …
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
-/
lemma prod_mul_prod : f₁.prod g₁ * f₂.prod g₂ = (f₁ * f₂).prod (g₁ * g₂) :=
  prod_mul_prod' _ _ _ _ fun _ _ _ _ _ _ ↦ mul_mul_mul_comm ..

end CommRing
end Preorder

section PartialOrder
variable (𝕜) [Ring 𝕜] [PartialOrder α] [PartialOrder β] [LocallyFiniteOrder α]
  [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β] [DecidableLE α] [DecidableLE β]

/-- The Möbius function on a product order. Based on lemma 2.1.13 of Incidence Algebras by Spiegel
and O'Donnell. -/
@[simp]
/-
**IncidenceAlgebra.mu_prod_mu** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：mu_prod_mu : (mu 𝕜).prod (mu 𝕜) = (mu 𝕜 : IncidenceAlgebra 𝕜 (α × β))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IncidenceAlgebra.zeta_prod_zeta`：zeta_prod_zeta [DecidableLE α] [Decidab
leLE β] : (zeta 𝕜).prod (zeta 𝕜) = (zeta 𝕜 : IncidenceAlgebra 𝕜 (α × β))
· 使用引理 `IncidenceAlgebra.prod_mul_prod'`：prod_mul_prod' [LocallyFiniteOrder α] [
LocallyFiniteOrder β] [DecidableLE (α × β)] (h : forall a₁ a₂ a₃ b₁ b₂ b₃, f₁ a₁
 a₂ * g₁ b₁ b₂ * (f₂ …
· 使用定理 `Commute.mul_mul_mul_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S
}, Commute b c → ∀ (a d : S), a * b * (c * d) = a * c * (b * d)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IncidenceAlgebra.mu_mul_zeta`：mu_mul_zeta : (mu 𝕜 * zeta 𝕜 : IncidenceAl
gebra 𝕜 α) = 1
· 使用引理 `IncidenceAlgebra.one_prod_one`：one_prod_one [DecidableEq α] [DecidableEq
 β] : (.prod 1 1 : IncidenceAlgebra 𝕜 (α × β)) = 1
· 使用引理 `IncidenceAlgebra.zeta_mul_mu`：zeta_mul_mu [DecidableLE α] : (zeta 𝕜 * mu
 𝕜 : IncidenceAlgebra 𝕜 α) = 1

--- 原说明 ---
The Möbius function on a product order. Based on lemma 2.1.13 of Incidence Algeb
ras by Spiegel
and O'Donnell.
-/
lemma mu_prod_mu : (mu 𝕜).prod (mu 𝕜) = (mu 𝕜 : IncidenceAlgebra 𝕜 (α × β)) := by
  refine left_inv_eq_right_inv ?_ zeta_mul_mu
  rw [← zeta_prod_zeta, prod_mul_prod', mu_mul_zeta, mu_mul_zeta, one_prod_one]
  exact fun _ _ _ _ _ _ ↦ Commute.mul_mul_mul_comm (by simp : _ = _) _ _

@[simp]
/-
**IncidenceAlgebra.eulerChar_prod** 是 Mathlib 中的一个引理，位于命名空间 `IncidenceAlgebra`。
形式化陈述：eulerChar_prod [BoundedOrder α] [BoundedOrder β] : eulerChar 𝕜 (α × β) = e
ulerChar 𝕜 α * eulerChar 𝕜 β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eulerChar_prod [BoundedOrder α] [BoundedOrder β] :
    eulerChar 𝕜 (α × β) = eulerChar 𝕜 α * eulerChar 𝕜 β := by simp [eulerChar, ← mu_prod_mu]

end PartialOrder
end Prod
end IncidenceAlgebra

