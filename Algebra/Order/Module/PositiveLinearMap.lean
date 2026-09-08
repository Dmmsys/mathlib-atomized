/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-! # Positive linear maps

This file defines positive linear maps as a linear map that is also an order homomorphism.

## Implementation notes

We do not define `PositiveLinearMapClass` to avoid adding a class that mixes order and algebra.
One can achieve the same effect by using a combination of `LinearMapClass` and `OrderHomClass`.
We nevertheless use the namespace for lemmas using that combination of typeclasses.

## Notes

More substantial results on positive maps such as their continuity can be found in
the `Analysis/CStarAlgebra` folder.
-/

@[expose] public section

/-- A positive linear map is a linear map that is also an order homomorphism. -/
/-
**PositiveLinearMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (E₁ : Type u_2) →     (E₂ : Type u_3) →       [inst : S
emiring R] →         [inst_1 : AddCommMonoid E₁] →           [PartialOrder E₁] →
             [inst_3 : AddCommMonoid E₂] →               [PartialOrder E₂] → [_r
oot_.Module R E₁] → [_root_.Module R E₂] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A positive linear map is a linear map that is also an order homomorphism.
-/
structure PositiveLinearMap (R E₁ E₂ : Type*) [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
    [Module R E₁] [Module R E₂] extends E₁ →ₗ[R] E₂, E₁ →o E₂

/-- The `OrderHom` underlying a `PositiveLinearMap`. -/
add_decl_doc PositiveLinearMap.toOrderHom

/-- Notation for a `PositiveLinearMap`. -/
notation:25 E " →ₚ[" R:25 "] " F:0 => PositiveLinearMap R E F

section PositiveLinearMapClass

variable {F R E₁ E₂ : Type*} [Semiring R]
  [AddCommMonoid E₁] [PartialOrder E₁] [AddCommMonoid E₂] [PartialOrder E₂]
  [Module R E₁] [Module R E₂] [FunLike F E₁ E₂] [LinearMapClass F R E₁ E₂]
  [OrderHomClass F E₁ E₂]

/-- Reinterpret an element of a type of positive linear maps as a positive linear map. -/
/-
**PositiveLinearMap.ofClass** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PositiveLinearMap.ofClass (f : F) : E₁ ->ₚ[R] E₂
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an element of a type of positive linear maps as a positive linear ma
p.
-/
def PositiveLinearMap.ofClass (f : F) : E₁ →ₚ[R] E₂ :=
  { (f : E₁ →ₗ[R] E₂), (f : E₁ →o E₂) with }

@[deprecated (since := "2026-06-10")]
alias PositiveLinearMapClass.toPositiveLinearMap := PositiveLinearMap.ofClass

/-- A type of additive group homomorphisms that map nonnegative elements to nonnegative elements
is also a type of order homomorphisms. -/
/-
**OrderHomClass.of_addMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：OrderHomClass.of_addMonoidHom {F' E₁' E₂' : Type*} [FunLike F' E₁' E₂'] [A
ddGroup E₁'] [LE E₁'] [AddRightMono E₁'] [AddGroup E₂'] [LE E₂'] [AddRightMono E
₂'] [AddMonoidHomClass F' E₁' E₂'] (h : forall f : F', forall x, 0 <= x -> 0 <= 
f x) : OrderHomClass F' E₁' E₂' where map_rel f a b hab
参数：h : forall f : F', forall x, 0 <= x -> 0 <= f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a

--- 原说明 ---
A type of additive group homomorphisms that map nonnegative elements to nonnegat
ive elements
is also a type of order homomorphisms.
-/
lemma OrderHomClass.of_addMonoidHom {F' E₁' E₂' : Type*} [FunLike F' E₁' E₂'] [AddGroup E₁']
    [LE E₁'] [AddRightMono E₁'] [AddGroup E₂'] [LE E₂'] [AddRightMono E₂']
    [AddMonoidHomClass F' E₁' E₂']
    (h : ∀ f : F', ∀ x, 0 ≤ x → 0 ≤ f x) : OrderHomClass F' E₁' E₂' where
  map_rel f a b hab := by simpa using h f (b - a) (sub_nonneg.mpr hab)

end PositiveLinearMapClass

namespace PositiveLinearMap

section general

variable {R E₁ E₂ E₃ : Type*} [Semiring R]
    [AddCommMonoid E₁] [PartialOrder E₁]
    [AddCommMonoid E₂] [PartialOrder E₂]
    [AddCommMonoid E₃] [PartialOrder E₃]
    [Module R E₁] [Module R E₂] [Module R E₃]

/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (E₁ →ₚ[R] E₂) E₁ E₂ where
  coe f := f.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
    apply DFunLike.coe_injective
    exact h

initialize_simps_projections PositiveLinearMap (toFun → apply, as_prefix toLinearMap)

@[ext]
/-
**PositiveLinearMap.ext** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMap`。
形式化陈述：ext {f g : E₁ ->ₚ[R] E₂} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
lemma ext {f g : E₁ →ₚ[R] E₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

variable (R E₁) in
/-- The identity as a positive linear map. -/
/-
**PositiveLinearMap.id** 是 Mathlib 中的一个定义，位于命名空间 `PositiveLinearMap`。
形式化陈述：(R : Type u_1) →   (E₁ : Type u_2) →     [inst : Semiring R] →       [inst
_1 : AddCommMonoid E₁] → [inst_2 : PartialOrder E₁] → [inst_3 : _root_.Module R 
E₁] → E₁ →ₚ[R] E₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a positive linear map.
-/
@[simps! apply toLinearMap] protected def id : E₁ →ₚ[R] E₁ where
  __ := LinearMap.id
  __ := OrderHom.id
/-
**PositiveLinearMap.toOrderHom_id** 是 Mathlib 中的一个定理，位于命名空间 `PositiveLinearMap`。
形式化陈述：∀ {R : Type u_1} {E₁ : Type u_2} [inst : Semiring R] [inst_1 : AddCommMono
id E₁] [inst_2 : PartialOrder E₁]   [inst_3 : _root_.Module R E₁], (PositiveLine
arMap.id R E₁).toOrderHom = OrderHom.id
参数：PositiveLinearMap.id R E₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toOrderHom_id : (PositiveLinearMap.id R E₁).toOrderHom = .id := rfl

/-- The composition of positive linear maps is again a positive linear map. -/
@[simps! apply toLinearMap]
/-
**PositiveLinearMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `PositiveLinearMap`。
形式化陈述：comp (g : E₂ ->ₚ[R] E₃) (f : E₁ ->ₚ[R] E₂) : E₁ ->ₚ[R] E₃ where toLinearMa
p
参数：g : E₂ ->ₚ[R] E₃；f : E₁ ->ₚ[R] E₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of positive linear maps is again a positive linear map.
-/
def comp (g : E₂ →ₚ[R] E₃) (f : E₁ →ₚ[R] E₂) : E₁ →ₚ[R] E₃ where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  monotone' := g.monotone'.comp f.monotone'
/-
**PositiveLinearMap.toOrderHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `PositiveLinearMap
`。
形式化陈述：∀ {R : Type u_1} {E₁ : Type u_2} {E₂ : Type u_3} {E₃ : Type u_4} [inst : S
emiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : PartialOrder E₁] [inst_3 : Ad
dCommMonoid E₂] [inst_4 : PartialOrder E₂] [inst_5 : AddCommMonoid E₃]   [inst_6
 : PartialOrder E₃] [inst_7 : _root_.Module R E₁] [inst_8 : _root_.Module R E₂] 
[inst_9 : _root_.Module R E₃]   (g : E₂ →ₚ[R] E₃) (f : E₁ →ₚ[R] E₂), (g.comp f).
toOrderHom = g.toOrderHom.comp f.toOrderHom
参数：g : E₂ →ₚ[R] E₃；f : E₁ →ₚ[R] E₂；g.comp f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toOrderHom_comp (g : E₂ →ₚ[R] E₃) (f : E₁ →ₚ[R] E₂) :
    (g.comp f).toOrderHom = g.toOrderHom.comp f.toOrderHom :=
  rfl
/-
**PositiveLinearMap.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `PositiveLinearMap`。
形式化陈述：∀ {R : Type u_1} {E₁ : Type u_2} {E₂ : Type u_3} [inst : Semiring R] [inst
_1 : AddCommMonoid E₁]   [inst_2 : PartialOrder E₁] [inst_3 : AddCommMonoid E₂] 
[inst_4 : PartialOrder E₂] [inst_5 : _root_.Module R E₁]   [inst_6 : _root_.Modu
le R E₂] (f : E₁ →ₚ[R] E₂), f.comp (PositiveLinearMap.id R E₁) = f
参数：f : E₁ →ₚ[R] E₂；PositiveLinearMap.id R E₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma comp_id (f : E₁ →ₚ[R] E₂) : f.comp (.id R E₁) = f := rfl
/-
**PositiveLinearMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `PositiveLinearMap`。
形式化陈述：∀ {R : Type u_1} {E₁ : Type u_2} {E₂ : Type u_3} [inst : Semiring R] [inst
_1 : AddCommMonoid E₁]   [inst_2 : PartialOrder E₁] [inst_3 : AddCommMonoid E₂] 
[inst_4 : PartialOrder E₂] [inst_5 : _root_.Module R E₁]   [inst_6 : _root_.Modu
le R E₂] (f : E₁ →ₚ[R] E₂), (PositiveLinearMap.id R E₂).comp f = f
参数：f : E₁ →ₚ[R] E₂；PositiveLinearMap.id R E₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma id_comp (f : E₁ →ₚ[R] E₂) : (PositiveLinearMap.id R E₂).comp f = f := rfl
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearMapClass (E₁ →ₚ[R] E₂) R E₁ E₂ where
  map_add f := map_add f.toLinearMap
  map_smulₛₗ f := f.toLinearMap.map_smul'
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderHomClass (E₁ →ₚ[R] E₂) E₁ E₂ where
  map_rel f := fun {_ _} hab => f.monotone' hab

@[simp]
/-
**PositiveLinearMap.map_smul_of_tower** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearM
ap`。
形式化陈述：map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂] [LinearMap.Compatibl
eSMul E₁ E₂ S R] (f : E₁ ->ₚ[R] E₂) (c : S) (x : E₁) : f (c • x) = c • f x
参数：f : E₁ ->ₚ[R] E₂；c : S；x : E₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMapClass.map_smul_of_tower`：∀ {M : Type u_8} {M₂ : Type u_10} [ins
t : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type u_15}
   [inst_2 : Semiring …
· 使用定理 `PositiveLinearMap.instLinearMapClass`：∀ {R : Type u_1} {E₁ : Type u_2} {
E₂ : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : Parti
alOrder E₁] [inst_3 : AddC…
-/
lemma map_smul_of_tower {S : Type*} [SMul S E₁] [SMul S E₂]
    [LinearMap.CompatibleSMul E₁ E₂ S R] (f : E₁ →ₚ[R] E₂) (c : S) (x : E₁) :
    f (c • x) = c • f x := LinearMapClass.map_smul_of_tower f _ _

-- We add the more specific lemma here purely for the aesop tag.
@[aesop safe apply (rule_sets := [CStarAlgebra])]
/-
**PositiveLinearMap.map_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `PositiveLinearMap`。
形式化陈述：∀ {R : Type u_1} {E₁ : Type u_2} {E₂ : Type u_3} [inst : Semiring R] [inst
_1 : AddCommMonoid E₁]   [inst_2 : PartialOrder E₁] [inst_3 : AddCommMonoid E₂] 
[inst_4 : PartialOrder E₂] [inst_5 : _root_.Module R E₁]   [inst_6 : _root_.Modu
le R E₂] (f : E₁ →ₚ[R] E₂) {x : E₁}, 0 ≤ x → 0 ≤ f x
参数：f : E₁ →ₚ[R] E₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nonneg`：map_nonneg (ha : 0 <= a) : 0 <= f a
· 使用定理 `PositiveLinearMap.instOrderHomClass`：∀ {R : Type u_1} {E₁ : Type u_2} {E
₂ : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : Partia
lOrder E₁] [inst_3 : AddC…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PositiveLinearMap.instLinearMapClass`：∀ {R : Type u_1} {E₁ : Type u_2} {
E₂ : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoid E₁]   [inst_2 : Parti
alOrder E₁] [inst_3 : AddC…
-/
protected lemma map_nonneg (f : E₁ →ₚ[R] E₂) {x : E₁} (hx : 0 ≤ x) : 0 ≤ f x :=
  _root_.map_nonneg f hx

@[simp]
/-
**PositiveLinearMap.coe_toLinearMap** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMap
`。
形式化陈述：coe_toLinearMap (f : E₁ ->ₚ[R] E₂) : (f.toLinearMap : E₁ -> E₂) = f
参数：f : E₁ ->ₚ[R] E₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toLinearMap (f : E₁ →ₚ[R] E₂) : (f.toLinearMap : E₁ → E₂) = f :=
  rfl
/-
**PositiveLinearMap.toLinearMap_injective** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLin
earMap`。
形式化陈述：toLinearMap_injective : Function.Injective (toLinearMap : (E₁ ->ₚ[R] E₂) -
> (E₁ ->ₗ[R] E₂))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PositiveLinearMap.ext`：ext {f g : E₁ ->ₚ[R] E₂} (h : forall x, f x = g x
) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma toLinearMap_injective : Function.Injective (toLinearMap : (E₁ →ₚ[R] E₂) → (E₁ →ₗ[R] E₂)) :=
  fun _ _ h ↦ by ext x; congrm($h x)

@[simp]
/-
**PositiveLinearMap.toLinearMap_inj** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMap
`。
形式化陈述：toLinearMap_inj {f g : E₁ ->ₚ[R] E₂} : f.toLinearMap = g.toLinearMap ↔ f =
 g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `PositiveLinearMap.toLinearMap_injective`：toLinearMap_injective : Functio
n.Injective (toLinearMap : (E₁ ->ₚ[R] E₂) -> (E₁ ->ₗ[R] E₂))
-/
lemma toLinearMap_inj {f g : E₁ →ₚ[R] E₂} : f.toLinearMap = g.toLinearMap ↔ f = g :=
  toLinearMap_injective.eq_iff
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (E₁ →ₚ[R] E₂) where
  zero := .mk (0 : E₁ →ₗ[R] E₂) fun _ ↦ by simp

@[simp]
/-
**PositiveLinearMap.toLinearMap_zero** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMa
p`。
形式化陈述：toLinearMap_zero : (0 : E₁ ->ₚ[R] E₂).toLinearMap = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_zero : (0 : E₁ →ₚ[R] E₂).toLinearMap = 0 :=
  rfl

@[simp]
/-
**PositiveLinearMap.zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMap`。
形式化陈述：zero_apply (x : E₁) : (0 : E₁ ->ₚ[R] E₂) x = 0
参数：x : E₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_apply (x : E₁) : (0 : E₁ →ₚ[R] E₂) x = 0 :=
  rfl

variable [IsOrderedAddMonoid E₂]
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (E₁ →ₚ[R] E₂) where
  add f g := .mk (f.toLinearMap + g.toLinearMap) fun _ _ h ↦
    add_le_add (OrderHomClass.mono f h) (OrderHomClass.mono g h)

@[simp]
/-
**PositiveLinearMap.toLinearMap_add** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMap
`。
形式化陈述：toLinearMap_add (f g : E₁ ->ₚ[R] E₂) : (f + g).toLinearMap = f.toLinearMap
 + g.toLinearMap
参数：f g : E₁ ->ₚ[R] E₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_add (f g : E₁ →ₚ[R] E₂) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := by
  rfl

@[simp]
/-
**PositiveLinearMap.add_apply** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMap`。
形式化陈述：add_apply (f g : E₁ ->ₚ[R] E₂) (x : E₁) : (f + g) x = f x + g x
参数：f g : E₁ ->ₚ[R] E₂；x : E₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_apply (f g : E₁ →ₚ[R] E₂) (x : E₁) :
    (f + g) x = f x + g x := by
  rfl
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (E₁ →ₚ[R] E₂) where
  smul n f := .mk (n • f.toLinearMap) fun x y h ↦ by
    induction n with
    | zero => simp
    | succ n ih => simpa [add_nsmul] using add_le_add ih (OrderHomClass.mono f h)

@[simp]
/-
**PositiveLinearMap.toLinearMap_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearM
ap`。
形式化陈述：toLinearMap_nsmul (f : E₁ ->ₚ[R] E₂) (n : Nat) : (n • f).toLinearMap = n •
 f.toLinearMap
参数：f : E₁ ->ₚ[R] E₂；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearMap_nsmul (f : E₁ →ₚ[R] E₂) (n : ℕ) :
    (n • f).toLinearMap = n • f.toLinearMap :=
  rfl

@[simp]
/-
**PositiveLinearMap.nsmul_apply** 是 Mathlib 中的一个引理，位于命名空间 `PositiveLinearMap`。
形式化陈述：nsmul_apply (f : E₁ ->ₚ[R] E₂) (n : Nat) (x : E₁) : (n • f) x = n • (f x)
参数：f : E₁ ->ₚ[R] E₂；n : Nat；x : E₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nsmul_apply (f : E₁ →ₚ[R] E₂) (n : ℕ) (x : E₁) :
    (n • f) x = n • (f x) :=
  rfl
/-
**PositiveLinearMap.** 是 Mathlib 中的一个实例，位于命名空间 `PositiveLinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (E₁ →ₚ[R] E₂) :=
  toLinearMap_injective.addCommMonoid _ toLinearMap_zero toLinearMap_add
    toLinearMap_nsmul

end general

section addgroup

variable {R E₁ E₂ : Type*} [Semiring R]
  [AddCommGroup E₁] [PartialOrder E₁] [IsOrderedAddMonoid E₁]
  [AddCommGroup E₂] [PartialOrder E₂] [IsOrderedAddMonoid E₂]
  [Module R E₁] [Module R E₂]

/-- Define a positive map from a linear map that maps nonnegative elements to nonnegative
elements -/
/-
**PositiveLinearMap.mk** 是 Mathlib 中的一个ctor，位于命名空间 `PositiveLinearMap`。
形式化陈述：{R : Type u_1} →   {E₁ : Type u_2} →     {E₂ : Type u_3} →       [inst : S
emiring R] →         [inst_1 : AddCommMonoid E₁] →           [inst_2 : PartialOr
der E₁] →             [inst_3 : AddCommMonoid E₂] →               [inst_4 : Part
ialOrder E₂] →                 [inst_5 : _root_.Module R E₁] →                  
 [inst_6 : _root_.Module R E₂] → (toLinearMap : E₁ →ₗ[R] E₂) → Monotone toLinear
Map.toFun → E₁ →ₚ[R] E₂
参数：toLinearMap : E₁ →ₗ[R] E₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a positive map from a linear map that maps nonnegative elements to nonneg
ative
elements
-/
def mk₀ (f : E₁ →ₗ[R] E₂) (hf : ∀ x, 0 ≤ x → 0 ≤ f x) : E₁ →ₚ[R] E₂ :=
  { f with
    monotone' := by
      intro a b hab
      rw [← sub_nonneg] at hab ⊢
      have : 0 ≤ f (b - a) := hf _ hab
      simpa using this }

end addgroup

end PositiveLinearMap

