/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.LinearMap
public import Mathlib.Topology.Algebra.Module.Star

/-! # Intrinsic star operation on continuous linear maps

This file defines the star operation on continuous linear maps: `(star f) x = star (f (star x))`.
This corresponds to a map being star-preserving, i.e., a map is self-adjoint iff it
is star-preserving.

This is the continuous version of the intrinsic star on linear maps (see
`Mathlib/Algebra/Star/LinearMap.lean`).

## Implementation notes

Because there is a global `star` instance on `H →L[𝕜] H` (defined as the linear map adjoint on
Hilbert spaces), which is mathematically distinct from this `star`, we provide
this instance on `WithConv (E →L[R] F)`. -/

public section

namespace ContinuousLinearMap
variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]
  [TopologicalSpace E] [TopologicalSpace F] [ContinuousStar E] [ContinuousStar F]

open WithConv

/-- The intrinsic star operation on continuous linear maps defined by
`(star f) x = star (f (star x))`. -/
/-
**ContinuousLinearMap.intrinsicStar** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousLinearM
ap`。
形式化陈述：intrinsicStar : Star (WithConv (E ->L[R] F)) where star f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intrinsic star operation on continuous linear maps defined by
`(star f) x = star (f (star x))`.
-/
instance intrinsicStar : Star (WithConv (E →L[R] F)) where star f := toConv <|
  { (star (toConv f.ofConv.toLinearMap)).ofConv with }
/-
**ContinuousLinearMap.intrinsicStar_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semiring R] [inst_1
 : InvolutiveStar R]   [inst_2 : AddCommMonoid E] [inst_3 : _root_.Module R E] [
inst_4 : StarAddMonoid E] [inst_5 : StarModule R E]   [inst_6 : AddCommMonoid F]
 [inst_7 : _root_.Module R F] [inst_8 : StarAddMonoid F] [inst_9 : StarModule R 
F]   [inst_10 : TopologicalSpace E] [inst_11 : TopologicalSpace F] [inst_12 : Co
ntinuousStar E]   [inst_13 : ContinuousStar F] (f : WithConv (E →L[R] F)) (x : E
), (star f).ofConv x = star (f.ofConv (star x))
参数：f : WithConv (E →L[R] F)；x : E；star f；f.ofConv (star x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem intrinsicStar_apply (f : WithConv (E →L[R] F)) (x : E) :
    star f x = star (f (star x)) := rfl
/-
**ContinuousLinearMap.toLinearMap_intrinsicStar** 是 Mathlib 中的一个定理，位于命名空间 `Conti
nuousLinearMap`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semiring R] [inst_1
 : InvolutiveStar R]   [inst_2 : AddCommMonoid E] [inst_3 : _root_.Module R E] [
inst_4 : StarAddMonoid E] [inst_5 : StarModule R E]   [inst_6 : AddCommMonoid F]
 [inst_7 : _root_.Module R F] [inst_8 : StarAddMonoid F] [inst_9 : StarModule R 
F]   [inst_10 : TopologicalSpace E] [inst_11 : TopologicalSpace F] [inst_12 : Co
ntinuousStar E]   [inst_13 : ContinuousStar F] (f : WithConv (E →L[R] F)), ↑(sta
r f).ofConv = (star (WithConv.toConv ↑f.ofConv)).ofConv
参数：f : WithConv (E →L[R] F)；star f；star (WithConv.toConv ↑f.ofConv)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toLinearMap_intrinsicStar (f : WithConv (E →L[R] F)) :
    (star f).ofConv.toLinearMap = (star (toConv f.ofConv.toLinearMap)).ofConv := rfl
/-
**ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star** 是 Mathlib 中的一个定
理，位于命名空间 `ContinuousLinearMap.IntrinsicStar`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semiring R] [inst_1
 : InvolutiveStar R]   [inst_2 : AddCommMonoid E] [inst_3 : _root_.Module R E] [
inst_4 : StarAddMonoid E] [inst_5 : StarModule R E]   [inst_6 : AddCommMonoid F]
 [inst_7 : _root_.Module R F] [inst_8 : StarAddMonoid F] [inst_9 : StarModule R 
F]   [inst_10 : TopologicalSpace E] [inst_11 : TopologicalSpace F] [inst_12 : Co
ntinuousStar E]   [inst_13 : ContinuousStar F] (f : WithConv (E →L[R] F)),   IsS
elfAdjoint f ↔ ∀ (x : E), f.ofConv (star x) = star (f.ofConv x)
参数：f : WithConv (E →L[R] F)；x : E；star x；f.ofConv x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IntrinsicStar.isSelfAdjoint_iff_map_star (f : WithConv (E →L[R] F)) :
    IsSelfAdjoint f ↔ ∀ x, f (star x) = star (f x) := by
  simp [IsSelfAdjoint, WithConv.ext_iff, ContinuousLinearMap.ext_iff, star_eq_iff_star_eq,
    eq_comm (a := f _)]
/-
**ContinuousLinearMap.IntrinsicStar.isSelfAdjoint_toLinearMap_iff** 是 Mathlib 中的
一个定理，位于命名空间 `ContinuousLinearMap.IntrinsicStar`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semiring R] [inst_1
 : InvolutiveStar R]   [inst_2 : AddCommMonoid E] [inst_3 : _root_.Module R E] [
inst_4 : StarAddMonoid E] [inst_5 : StarModule R E]   [inst_6 : AddCommMonoid F]
 [inst_7 : _root_.Module R F] [inst_8 : StarAddMonoid F] [inst_9 : StarModule R 
F]   [inst_10 : TopologicalSpace E] [inst_11 : TopologicalSpace F] [inst_12 : Co
ntinuousStar E]   [inst_13 : ContinuousStar F] (f : WithConv (E →L[R] F)), IsSel
fAdjoint (WithConv.toConv ↑f.ofConv) ↔ IsSelfAdjoint f
参数：f : WithConv (E →L[R] F)；WithConv.toConv ↑f.ofConv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IntrinsicStar.isSelfAdjoint_toLinearMap_iff (f : WithConv (E →L[R] F)) :
    IsSelfAdjoint (toConv f.ofConv.toLinearMap) ↔ IsSelfAdjoint f := by
  simp [isSelfAdjoint_iff_map_star, LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star]

/-- The involutive intrinsic star structure on continuous linear maps. -/
/-
**ContinuousLinearMap.intrinsicInvolutiveStar** 是 Mathlib 中的一个实例，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：intrinsicInvolutiveStar : InvolutiveStar (WithConv (E ->L[R] F)) where sta
r_involutive x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The involutive intrinsic star structure on continuous linear maps.
-/
instance intrinsicInvolutiveStar : InvolutiveStar (WithConv (E →L[R] F)) where
  star_involutive x := by ext; simp

/-- The intrinsic star additive monoid structure on continuous linear maps. -/
/-
**ContinuousLinearMap.intrinsicStarAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Continuo
usLinearMap`。
形式化陈述：intrinsicStarAddMonoid [ContinuousAdd F] : StarAddMonoid (WithConv (E ->L[
R] F)) where star_add x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intrinsic star additive monoid structure on continuous linear maps.
-/
instance intrinsicStarAddMonoid [ContinuousAdd F] : StarAddMonoid (WithConv (E →L[R] F)) where
  star_add x y := by ext; simp
/-
**ContinuousLinearMap.intrinsicStar_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：intrinsicStar_comp {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMono
id G] [StarModule R G] [TopologicalSpace G] [ContinuousStar G] (f : WithConv (E 
->L[R] F)) (g : WithConv (G ->L[R] E)) : star (toConv (f.ofConv ∘L g.ofConv)) = 
toConv ((star f).ofConv ∘L (star g).ofConv)
参数：f : WithConv (E ->L[R] F)；g : WithConv (G ->L[R] E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_comp {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
    [StarModule R G] [TopologicalSpace G] [ContinuousStar G] (f : WithConv (E →L[R] F))
    (g : WithConv (G →L[R] E)) :
    star (toConv (f.ofConv ∘L g.ofConv)) = toConv ((star f).ofConv ∘L (star g).ofConv) := by
  ext; simp
/-
**ContinuousLinearMap.intrinsicStar_comp'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：intrinsicStar_comp' {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMon
oid G] [StarModule R G] [TopologicalSpace G] [ContinuousStar G] (f : E ->L[R] F)
 (g : G ->L[R] E) : star (toConv (f ∘L g)) = toConv ((star (toConv f)).ofConv ∘L
 (star (toConv g)).ofConv)
参数：f : E ->L[R] F；g : G ->L[R] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_comp' {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G]
    [StarModule R G] [TopologicalSpace G] [ContinuousStar G] (f : E →L[R] F) (g : G →L[R] E) :
    star (toConv (f ∘L g)) = toConv ((star (toConv f)).ofConv ∘L (star (toConv g)).ofConv) := by
  ext; simp
/-
**ContinuousLinearMap.intrinsicStar_id** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLine
arMap`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [inst_1 : InvolutiveSt
ar R] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module R E] [inst_4 : StarAd
dMonoid E] [inst_5 : StarModule R E] [inst_6 : TopologicalSpace E]   [inst_7 : C
ontinuousStar E],   star (WithConv.toConv (ContinuousLinearMap.id R E)) = WithCo
nv.toConv (ContinuousLinearMap.id R E)
参数：WithConv.toConv (ContinuousLinearMap.id R E)；ContinuousLinearMap.id R E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem intrinsicStar_id :
    star (toConv (ContinuousLinearMap.id R E)) = toConv (.id R E) := by ext; simp
/-
**ContinuousLinearMap.intrinsicStar_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLi
nearMap`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semiring R] [inst_1
 : InvolutiveStar R]   [inst_2 : AddCommMonoid E] [inst_3 : _root_.Module R E] [
inst_4 : StarAddMonoid E] [inst_5 : StarModule R E]   [inst_6 : AddCommMonoid F]
 [inst_7 : _root_.Module R F] [inst_8 : StarAddMonoid F] [inst_9 : StarModule R 
F]   [inst_10 : TopologicalSpace E] [inst_11 : TopologicalSpace F] [inst_12 : Co
ntinuousStar E]   [inst_13 : ContinuousStar F], star (WithConv.toConv 0) = WithC
onv.toConv 0
参数：WithConv.toConv 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem intrinsicStar_zero : star (toConv (0 : E →L[R] F)) = toConv 0 := by ext; simp

section starAddMonoidSemiring
variable {S : Type*} [Semiring S] [StarAddMonoid S] [StarModule S S] [Module S E] [StarModule S E]
  [TopologicalSpace S] [ContinuousStar S]

/-
**ContinuousLinearMap.intrinsicStar_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：∀ {E : Type u_2} [inst : AddCommMonoid E] [inst_1 : StarAddMonoid E] [inst
_2 : TopologicalSpace E]   [inst_3 : ContinuousStar E] {S : Type u_4} [inst_4 : 
Semiring S] [inst_5 : StarAddMonoid S] [inst_6 : StarModule S S]   [inst_7 : _ro
ot_.Module S E] [inst_8 : StarModule S E] [inst_9 : TopologicalSpace S] [inst_10
 : ContinuousStar S]   [inst_11 : ContinuousSMul S E] (a : E),   star (WithConv.
toConv (ContinuousLinearMap.toSpanSingleton S a)) =     WithConv.toConv (Continu
ousLinearMap.toSpanSingleton S (star a))
参数：a : E；WithConv.toConv (ContinuousLinearMap.toSpanSingleton S a)；ContinuousLin
earMap.toSpanSingleton S (star a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `ContinuousLinearMap.ext_ring`：ext_ring [TopologicalSpace R₁] {f g : R₁ -
>L[R₁] M₁} (h : f 1 = g 1) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem intrinsicStar_toSpanSingleton [ContinuousSMul S E] (a : E) :
    star (toConv (toSpanSingleton S a)) = toConv (toSpanSingleton S (star a)) := by ext; simp
/-
**ContinuousLinearMap.intrinsicStar_smulRight** 是 Mathlib 中的一个定理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：intrinsicStar_smulRight [Module S F] [StarModule S F] [ContinuousSMul S F]
 (f : WithConv (E ->L[S] S)) (x : F) : star (toConv (f.ofConv.smulRight x)) = to
Conv ((star f).ofConv.smulRight (star x))
参数：f : WithConv (E ->L[S] S)；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_smulRight [Module S F] [StarModule S F] [ContinuousSMul S F]
    (f : WithConv (E →L[S] S)) (x : F) :
    star (toConv (f.ofConv.smulRight x)) = toConv ((star f).ofConv.smulRight (star x)) := by
  ext; simp

end starAddMonoidSemiring

/-
**ContinuousLinearMap.intrinsicStarModule** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousL
inearMap`。
形式化陈述：intrinsicStarModule [SMulCommClass R R F] [ContinuousConstSMul R F] : Star
Module R (WithConv (E ->L[R] F)) where star_smul _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance intrinsicStarModule [SMulCommClass R R F] [ContinuousConstSMul R F] :
    StarModule R (WithConv (E →L[R] F)) where star_smul _ _ := by ext; simp
/-
**ContinuousLinearMap.intrinsicStar_eq_comp** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：intrinsicStar_eq_comp {R : Type*} [CommSemiring R] [StarRing R] [Module R 
E] [StarModule R E] [Module R F] [StarModule R F] (f : WithConv (E ->L[R] F)) : 
star f = toConv ((starL R).toContinuousLinearMap.comp (f.ofConv.comp (starL R).t
oContinuousLinearMap))
参数：f : WithConv (E ->L[R] F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma intrinsicStar_eq_comp {R : Type*} [CommSemiring R] [StarRing R] [Module R E] [StarModule R E]
    [Module R F] [StarModule R F] (f : WithConv (E →L[R] F)) :
    star f = toConv
      ((starL R).toContinuousLinearMap.comp (f.ofConv.comp (starL R).toContinuousLinearMap)) := rfl

end ContinuousLinearMap

