/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.WithConv
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Coalgebra.Convolution

/-! # Intrinsic star operation on linear maps

This file defines the star operation on linear maps: `(star f) x = star (f (star x))`.
This corresponds to a map being star-preserving, i.e., a map is self-adjoint iff it
is star-preserving.

## Implementation notes

Because there is a global `star` instance on `H →ₗ[𝕜] H` (defined as the linear map adjoint on
finite-dimensional Hilbert spaces), which is mathematically distinct from this `star`, we provide
this instance on `WithConv (E →ₗ[R] F)`.

The reason we chose `WithConv` is because together with the convolution product from
`Mathlib/RingTheory/Coalgebra/Convolution.lean`, we get a ⋆-algebra when
`star (WithConv.toConv comul) = WithConv.toConv (comm ∘ comul)`. -/

public section

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

open WithConv

namespace LinearMap

/-- The intrinsic star operation on linear maps `E →ₗ F` defined by
`(star f) x = star (f (star x))`. -/
/-
**LinearMap.intrinsicStar** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar : Star (WithConv (E ->ₗ[R] F)) where star f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intrinsic star operation on linear maps `E →ₗ F` defined by
`(star f) x = star (f (star x))`.
-/
instance intrinsicStar : Star (WithConv (E →ₗ[R] F)) where
  star f := toConv <|
  { toFun x := star (f (star x))
    map_add' := by simp
    map_smul' := by simp }
/-
**LinearMap.intrinsicStar_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semiring R] [inst_1
 : InvolutiveStar R]   [inst_2 : AddCommMonoid E] [inst_3 : _root_.Module R E] [
inst_4 : StarAddMonoid E] [inst_5 : StarModule R E]   [inst_6 : AddCommMonoid F]
 [inst_7 : _root_.Module R F] [inst_8 : StarAddMonoid F] [inst_9 : StarModule R 
F]   (f : WithConv (E →ₗ[R] F)) (x : E), (star f).ofConv x = star (f.ofConv (sta
r x))
参数：f : WithConv (E →ₗ[R] F)；x : E；star f；f.ofConv (star x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem intrinsicStar_apply (f : WithConv (E →ₗ[R] F)) (x : E) :
    (star f) x = star (f (star x)) := rfl

/-- The involutive intrinsic star structure on linear maps. -/
/-
**LinearMap.intrinsicInvolutiveStar** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：intrinsicInvolutiveStar : InvolutiveStar (WithConv (E ->ₗ[R] F)) where sta
r_involutive x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The involutive intrinsic star structure on linear maps.
-/
instance intrinsicInvolutiveStar : InvolutiveStar (WithConv (E →ₗ[R] F)) where
  star_involutive x := by ext; simp

/-- The intrinsic star additive monoid structure on linear maps. -/
/-
**LinearMap.intrinsicStarAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStarAddMonoid : StarAddMonoid (WithConv (E ->ₗ[R] F)) where star_
add x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intrinsic star additive monoid structure on linear maps.
-/
instance intrinsicStarAddMonoid : StarAddMonoid (WithConv (E →ₗ[R] F)) where
  star_add x y := by ext; simp

/-- A linear map is self-adjoint (with respect to the intrinsic star) iff it is star-preserving. -/
/-
**LinearMap.IntrinsicStar.isSelfAdjoint_iff_map_star** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap.IntrinsicStar`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semiring R] [inst_1
 : InvolutiveStar R]   [inst_2 : AddCommMonoid E] [inst_3 : _root_.Module R E] [
inst_4 : StarAddMonoid E] [inst_5 : StarModule R E]   [inst_6 : AddCommMonoid F]
 [inst_7 : _root_.Module R F] [inst_8 : StarAddMonoid F] [inst_9 : StarModule R 
F]   (f : WithConv (E →ₗ[R] F)), IsSelfAdjoint f ↔ ∀ (x : E), f.ofConv (star x) 
= star (f.ofConv x)
参数：f : WithConv (E →ₗ[R] F)；x : E；star x；f.ofConv x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A linear map is self-adjoint (with respect to the intrinsic star) iff it is star
-preserving.
-/
theorem IntrinsicStar.isSelfAdjoint_iff_map_star (f : WithConv (E →ₗ[R] F)) :
    IsSelfAdjoint f ↔ ∀ x, f (star x) = star (f x) := by
  simp_rw [IsSelfAdjoint, WithConv.ext_iff, LinearMap.ext_iff, intrinsicStar_apply,
    star_eq_iff_star_eq, eq_comm]

/-- A star-preserving linear map is self-adjoint (with respect to the intrinsic star). -/
@[simp]
/-
**LinearMap._root_.IntrinsicStar.StarHomClass.isSelfAdjoint** 是 Mathlib 中的一个定理，位
于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A star-preserving linear map is self-adjoint (with respect to the intrinsic star
).
-/
protected theorem _root_.IntrinsicStar.StarHomClass.isSelfAdjoint {S : Type*} [FunLike S E F]
    [LinearMapClass S R E F] [StarHomClass S E F] {f : S} :
    IsSelfAdjoint (toConv (f : E →ₗ[R] F) : WithConv (E →ₗ[R] F)) :=
  IntrinsicStar.isSelfAdjoint_iff_map_star _ |>.mpr (map_star f)

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]
/-
**LinearMap.intrinsicStar_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_comp (f : WithConv (E ->ₗ[R] F)) (g : WithConv (G ->ₗ[R] E))
 : star (toConv (f.ofConv ∘ₗ g.ofConv)) = toConv ((star f).ofConv ∘ₗ (star g).of
Conv)
参数：f : WithConv (E ->ₗ[R] F)；g : WithConv (G ->ₗ[R] E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_comp (f : WithConv (E →ₗ[R] F)) (g : WithConv (G →ₗ[R] E)) :
    star (toConv (f.ofConv ∘ₗ g.ofConv)) = toConv ((star f).ofConv ∘ₗ (star g).ofConv) := by
  ext; simp
/-
**LinearMap.intrinsicStar_comp'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_comp' (f : E ->ₗ[R] F) (g : G ->ₗ[R] E) : star (toConv (f ∘ₗ
 g)) = toConv ((star (toConv f)).ofConv ∘ₗ (star (toConv g)).ofConv)
参数：f : E ->ₗ[R] F；g : G ->ₗ[R] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.intrinsicStar_comp`：intrinsicStar_comp (f : WithConv (E ->ₗ[R]
 F)) (g : WithConv (G ->ₗ[R] E)) : star (toConv (f.ofConv ∘ₗ g.ofConv)) = toConv
 ((star f).ofConv …
-/
theorem intrinsicStar_comp' (f : E →ₗ[R] F) (g : G →ₗ[R] E) :
    star (toConv (f ∘ₗ g)) = toConv ((star (toConv f)).ofConv ∘ₗ (star (toConv g)).ofConv) := by
  simpa using intrinsicStar_comp _ _
/-
**LinearMap.intrinsicStar_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [inst_1 : InvolutiveSt
ar R] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module R E] [inst_4 : StarAd
dMonoid E] [inst_5 : StarModule R E],   star (WithConv.toConv LinearMap.id) = Wi
thConv.toConv LinearMap.id
参数：WithConv.toConv LinearMap.id。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
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
    star (toConv (LinearMap.id (R := R) (M := E))) = toConv LinearMap.id := by ext; simp
/-
**LinearMap.intrinsicStar_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_zero : star (0 : WithConv (E ->ₗ[R] F)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_zero : star (0 : WithConv (E →ₗ[R] F)) = 0 := by simp

section NonUnitalNonAssocSemiring
variable {R' E : Type*} [CommSemiring R'] [StarRing R']
  [NonUnitalNonAssocSemiring E] [StarRing E] [Module R E] [Module R' E]
  [StarModule R E] [StarModule R' E] [SMulCommClass R E E] [IsScalarTower R E E]

/-
**LinearMap.intrinsicStar_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_mulLeft (x : E) : star (toConv (mulLeft R x)) = toConv (mulR
ight R (star x))
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_mulLeft (x : E) :
    star (toConv (mulLeft R x)) = toConv (mulRight R (star x)) := by ext; simp
/-
**LinearMap.intrinsicStar_mulRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_mulRight (x : E) : star (toConv (mulRight R x)) = toConv (mu
lLeft R (star x))
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_eq_iff_star_eq`：star_eq_iff_star_eq [InvolutiveStar R] {r s : R} : 
star r = s ↔ star s = r
· 使用定理 `LinearMap.intrinsicStar_mulLeft`：intrinsicStar_mulLeft (x : E) : star (t
oConv (mulLeft R x)) = toConv (mulRight R (star x))
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem intrinsicStar_mulRight (x : E) :
    star (toConv (mulRight R x)) = toConv (mulLeft R (star x)) := by
  rw [star_eq_iff_star_eq, intrinsicStar_mulLeft, star_star]
/-
**LinearMap.intrinsicStar_mul'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_mul' [SMulCommClass R' E E] [IsScalarTower R' E E] : star (t
oConv (mul' R' E)) = toConv (mul' R' E ∘ₗ TensorProduct.comm R' E E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `TensorProduct.instStarModule`：∀ {R : Type u_1} {A : Type u_2} {B : Type 
u_3} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : AddCommMonoid A]   
[inst_3 : StarAddM…
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_mul' [SMulCommClass R' E E] [IsScalarTower R' E E] :
    star (toConv (mul' R' E)) = toConv (mul' R' E ∘ₗ TensorProduct.comm R' E E) :=
  WithConv.ext <| TensorProduct.ext' fun _ _ ↦ by simp

end NonUnitalNonAssocSemiring

variable [SMulCommClass R R F] in
/-
**LinearMap.intrinsicStarModule** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStarModule : StarModule R (WithConv (E ->ₗ[R] F)) where star_smul
 _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
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
instance intrinsicStarModule : StarModule R (WithConv (E →ₗ[R] F)) where
  star_smul _ _ := by ext; simp

section CommSemiring
variable {R E F G H : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid E] [StarAddMonoid E] [Module R E] [StarModule R E]
  [AddCommMonoid F] [StarAddMonoid F] [Module R F] [StarModule R F]
  [AddCommMonoid G] [StarAddMonoid G] [Module R G] [StarModule R G]
  [AddCommMonoid H] [StarAddMonoid H] [Module R H] [StarModule R H]

/-
**LinearMap._root_.TensorProduct.intrinsicStar_map** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.TensorProduct.intrinsicStar_map
    (f : WithConv (E →ₗ[R] F)) (g : WithConv (G →ₗ[R] H)) :
    star (toConv (TensorProduct.map f.ofConv g.ofConv)) =
      toConv (TensorProduct.map (star f).ofConv (star g).ofConv) :=
  WithConv.ext <| TensorProduct.ext' fun _ _ ↦ by simp
/-
**LinearMap._root_.TensorProduct.star_map_apply_eq_map_intrinsicStar** 是 Mathlib
 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.TensorProduct.star_map_apply_eq_map_intrinsicStar
    (f : WithConv (E →ₗ[R] F)) (g : WithConv (G →ₗ[R] H)) (x) :
    star (TensorProduct.map f.ofConv g.ofConv x) =
      TensorProduct.map (star f).ofConv (star g).ofConv (star x) := by
  simpa using congr($(TensorProduct.intrinsicStar_map f g) (star x))
/-
**LinearMap.intrinsicStar_lTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_lTensor (f : WithConv (F ->ₗ[R] G)) : star (toConv (lTensor 
E f.ofConv)) = toConv (lTensor E (star f).ofConv)
参数：f : WithConv (F ->ₗ[R] G)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `TensorProduct.instStarModule`：∀ {R : Type u_1} {A : Type u_2} {B : Type 
u_3} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : AddCommMonoid A]   
[inst_3 : StarAddM…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_lTensor (f : WithConv (F →ₗ[R] G)) :
    star (toConv (lTensor E f.ofConv)) = toConv (lTensor E (star f).ofConv) := by ext; simp
/-
**LinearMap.intrinsicStar_rTensor** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_rTensor (f : WithConv (E ->ₗ[R] F)) : star (toConv (rTensor 
G f.ofConv)) = toConv (rTensor G (star f).ofConv)
参数：f : WithConv (E ->ₗ[R] F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `TensorProduct.instStarModule`：∀ {R : Type u_1} {A : Type u_2} {B : Type 
u_3} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : AddCommMonoid A]   
[inst_3 : StarAddM…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_rTensor (f : WithConv (E →ₗ[R] F)) :
    star (toConv (rTensor G f.ofConv)) = toConv (rTensor G (star f).ofConv) := by ext; simp
/-
**LinearMap.intrinsicStar_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_eq_comp (f : WithConv (E ->ₗ[R] F)) : star f = toConv ((star
LinearEquiv R).toLinearMap ∘ₛₗ f.ofConv ∘ₛₗ (starLinearEquiv R).toLinearMap)
参数：f : WithConv (E ->ₗ[R] F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intrinsicStar_eq_comp (f : WithConv (E →ₗ[R] F)) :
    star f =
      toConv ((starLinearEquiv R).toLinearMap ∘ₛₗ f.ofConv ∘ₛₗ (starLinearEquiv R).toLinearMap) :=
  rfl
/-
**LinearMap.IntrinsicStar.starLinearEquiv_eq_arrowCongr** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap.IntrinsicStar`。
形式化陈述：∀ {R : Type u_5} {E : Type u_6} {F : Type u_7} [inst : CommSemiring R] [in
st_1 : StarRing R] [inst_2 : AddCommMonoid E]   [inst_3 : StarAddMonoid E] [inst
_4 : _root_.Module R E] [inst_5 : StarModule R E] [inst_6 : AddCommMonoid F]   [
inst_7 : StarAddMonoid F] [inst_8 : _root_.Module R F] [inst_9 : StarModule R F]
,   starLinearEquiv R =     (WithConv.linearEquiv R (E →ₗ[R] F)).trans       (((
starLinearEquiv R).arrowCongr (starLinearEquiv R)).trans (WithConv.linearEquiv R
 (E →ₗ[R] F)).symm)
参数：WithConv.linearEquiv R (E →ₗ[R] F)；((starLinearEquiv R).arrowCongr (starLinea
rEquiv R)).trans (WithConv.linearEquiv R (E →ₗ[R] F)).symm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
-/
theorem IntrinsicStar.starLinearEquiv_eq_arrowCongr :
    starLinearEquiv R (A := WithConv (E →ₗ[R] F)) =
      (WithConv.linearEquiv R _).trans
      (((starLinearEquiv R).arrowCongr (starLinearEquiv R)).trans
        (WithConv.linearEquiv R _).symm) := rfl

end CommSemiring

section starAddMonoidSemiring
variable {S : Type*} [Semiring S] [StarAddMonoid S] [StarModule S S] [Module S E] [StarModule S E]

/-
**LinearMap.intrinsicStar_toSpanSingleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {E : Type u_2} [inst : AddCommMonoid E] [inst_1 : StarAddMonoid E] {S : 
Type u_5} [inst_2 : Semiring S]   [inst_3 : StarAddMonoid S] [inst_4 : StarModul
e S S] [inst_5 : _root_.Module S E] [inst_6 : StarModule S E] (a : E),   star (W
ithConv.toConv (LinearMap.toSpanSingleton S E a)) = WithConv.toConv (LinearMap.t
oSpanSingleton S E (star a))
参数：a : E；WithConv.toConv (LinearMap.toSpanSingleton S E a)；LinearMap.toSpanSingl
eton S E (star a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem intrinsicStar_toSpanSingleton (a : E) :
    star (toConv (toSpanSingleton S E a)) = toConv (toSpanSingleton S E (star a)) := by ext; simp
/-
**LinearMap.intrinsicStar_smulRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_smulRight [Module S F] [StarModule S F] (f : WithConv (E ->ₗ
[S] S)) (x : F) : star (toConv (f.ofConv.smulRight x)) = toConv ((star f).ofConv
.smulRight (star x))
参数：f : WithConv (E ->ₗ[S] S)；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
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
theorem intrinsicStar_smulRight [Module S F] [StarModule S F] (f : WithConv (E →ₗ[S] S)) (x : F) :
    star (toConv (f.ofConv.smulRight x)) = toConv ((star f).ofConv.smulRight (star x)) := by
  ext; simp

end starAddMonoidSemiring

section convRing
variable {R A C : Type*} [CommSemiring R] [StarRing R] [NonUnitalNonAssocSemiring A]
  [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] [StarRing A] [StarModule R A]
  [AddCommMonoid C] [Module R C] [StarAddMonoid C] [StarModule R C]

open Coalgebra TensorProduct

/-
**LinearMap.intrinsicStar_convMul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：intrinsicStar_convMul [CoalgebraStruct R C] (h : star (toConv comul) = toC
onv ((TensorProduct.comm R C C).toLinearMap ∘ₗ comul)) (f g : WithConv (C ->ₗ[R]
 A)) : star (f * g) = star g * star f
参数：h : star (toConv comul) = toConv ((TensorProduct.comm R C C).toLinearMap ∘ₗ c
omul)；f g : WithConv (C ->ₗ[R] A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.instStarModule`：∀ {R : Type u_1} {A : Type u_2} {B : Type 
u_3} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : AddCommMonoid A]   
[inst_3 : StarAddM…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.intrinsicStar_comp'`：intrinsicStar_comp' (f : E ->ₗ[R] F) (g :
 G ->ₗ[R] E) : star (toConv (f ∘ₗ g)) = toConv ((star (toConv f)).ofConv ∘ₗ (sta
r (toConv g)).ofCon…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.intrinsicStar_mul'`：intrinsicStar_mul' [SMulCommClass R' E E] 
[IsScalarTower R' E E] : star (toConv (mul' R' E)) = toConv (mul' R' E ∘ₗ Tensor
Product.comm R' E …
· 使用定理 `TensorProduct.intrinsicStar_map`：∀ {R : Type u_5} {E : Type u_6} {F : Ty
pe u_7} {G : Type u_8} {H : Type u_9} [inst : CommSemiring R]   [inst_1 : StarRi
ng R] [inst_2 : AddCo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用引理 `TensorProduct.map_comp_comm_eq`：map_comp_comm_eq (f : M ->ₛₗ[σ₁₂] M₂) (g
 : N ->ₛₗ[σ₁₂] N₂) : map f g ∘ₛₗ (TensorProduct.comm R N M).toLinearMap = (Tenso
rProduct.comm R₂ N₂ …
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `TensorProduct.comm_comm`：∀ (R : Type u_1) [inst : CommSemiring R] (M : T
ype u_7) (N : Type u_8) [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] 
[inst_3 : _ro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_convMul [CoalgebraStruct R C]
    (h : star (toConv comul) = toConv ((TensorProduct.comm R C C).toLinearMap ∘ₗ comul))
    (f g : WithConv (C →ₗ[R] A)) : star (f * g) = star g * star f := by
  simp_rw [convMul_def, intrinsicStar_comp', intrinsicStar_mul', intrinsicStar_map,
    h, comp_assoc, ← comp_assoc _ _ (map _ _), map_comp_comm_eq,
    ← comp_assoc _ (TensorProduct.comm R A A).toLinearMap]
  ext; simp

/-- The convolutive intrinsic star ring on linear maps from coalgebras
to ⋆-algebras, given that `star (toConv comul) = toConv (comm ∘ₗ comul)`.

In finite-dimensional C⋆-algebras, under the GNS construction, and the adjoint
coalgebra, we get this hypothesis.

See note [reducible non-instances]. -/
/-
**LinearMap.convIntrinsicStarRing** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearMap`。
形式化陈述：convIntrinsicStarRing [Coalgebra R C] (h : star (toConv comul) = toConv ((
TensorProduct.comm R C C).toLinearMap ∘ₗ comul)) : StarRing (WithConv (C ->ₗ[R] 
A)) where __
参数：h : star (toConv comul) = toConv ((TensorProduct.comm R C C).toLinearMap ∘ₗ c
omul)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.instStarModule`：∀ {R : Type u_1} {A : Type u_2} {B : Type 
u_3} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : AddCommMonoid A]   
[inst_3 : StarAddM…

--- 原说明 ---
The convolutive intrinsic star ring on linear maps from coalgebras
to ⋆-algebras, given that `star (toConv comul) = toConv (comm ∘ₗ comul)`.

In finite-dimensional C⋆-algebras, under the GNS construction, and the adjoint
coalgebra, we get this hypothesis.

See note [reducible non-instances].
-/
abbrev convIntrinsicStarRing [Coalgebra R C]
    (h : star (toConv comul) = toConv ((TensorProduct.comm R C C).toLinearMap ∘ₗ comul)) :
    StarRing (WithConv (C →ₗ[R] A)) where
  __ := intrinsicStarAddMonoid
  star_mul := intrinsicStar_convMul h

variable {n : Type*} [DecidableEq n] {B : n → Type*} [Π i, AddCommMonoid (B i)]
  [Π i, Module R (B i)] [Π i, StarAddMonoid (B i)] [∀ i, StarModule R (B i)]
/-
**LinearMap.intrinsicStar_single** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_5} [inst : CommSemiring R] [inst_1 : StarRing R] {n : Type u
_8} [inst_2 : DecidableEq n]   {B : n → Type u_9} [inst_3 : (i : n) → AddCommMon
oid (B i)] [inst_4 : (i : n) → _root_.Module R (B i)]   [inst_5 : (i : n) → Star
AddMonoid (B i)] [inst_6 : ∀ (i : n), StarModule R (B i)] (i : n),   star (WithC
onv.toConv (LinearMap.single R B i)) = WithConv.toConv (LinearMap.single R B i)
参数：i : n；B i；i : n；B i；i : n；B i；i : n；B i；i : n；WithConv.toConv (LinearMap.sing
le R B i)；LinearMap.single R B i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithConv.ext`：∀ {A : Type u_2} {x y : WithConv A}, x.ofConv = y.ofConv →
 x = y
· 使用定理 `Pi.instStarModuleForall`：∀ {I : Type u} {f : I → Type v} {R : Type w} [i
nst : (i : I) → SMul R (f i)] [inst_1 : Star R]   [inst_2 : (i : I) → Star (f i)
] [∀ (i : I),…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
@[simp] theorem intrinsicStar_single (i : n) :
    star (toConv (single R B i)) = toConv (single R B i) := by
  aesop (add simp [Pi.single, Function.update])

variable [Fintype n]
/-
**LinearMap._root_.Pi.intrinsicStar_comul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pi.intrinsicStar_comul [Π i, CoalgebraStruct R (B i)]
    (h : ∀ i, star (toConv (comul (R := R) (A := B i))) =
      toConv (TensorProduct.comm R (B i) (B i) ∘ₗ comul)) :
    star (toConv (comul (R := R) (A := Π i, B i))) =
      toConv (TensorProduct.comm R (Π i, B i) (Π i, B i) ∘ₗ comul) := by
  ext i x
  have := by simpa using congr($(h i) x)
  simp only [coe_comp, coe_single, Function.comp_apply, intrinsicStar_apply, Pi.star_single,
    Pi.comul_single, LinearEquiv.coe_coe]
  rw [star_map_apply_eq_map_intrinsicStar, this, map_comm]
  simp
/-
**LinearMap._root_.Pi.intrinsicStar_comul_commSemiring** 是 Mathlib 中的一个定理，位于命名空间
 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.Pi.intrinsicStar_comul_commSemiring :
    star (toConv (comul (R := R) (A := n → R))) =
      toConv (TensorProduct.comm R (n → R) (n → R) ∘ₗ comul) :=
  Pi.intrinsicStar_comul fun _ ↦ by ext; simp

/-- The intrinsic star convolutive ring on linear maps from `n → R` to `m → R`. -/
/-
**LinearMap._root_.Pi.convIntrinsicStarRingCommSemiring** 是 Mathlib 中的一个实例，位于命名空
间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The intrinsic star convolutive ring on linear maps from `n → R` to `m → R`.
-/
instance _root_.Pi.convIntrinsicStarRingCommSemiring {m : Type*} :
    StarRing (WithConv ((n → R) →ₗ[R] m → R)) := convIntrinsicStarRing (by simp)

end convRing

end LinearMap

section matrix
variable {R m n : Type*} [CommSemiring R] [StarRing R] [Fintype m] [DecidableEq m]

namespace LinearMap

/-
**LinearMap.toMatrix'_intrinsicStar** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_4} {m : Type u_5} {n : Type u_6} [inst : CommSemiring R] [in
st_1 : StarRing R] [inst_2 : Fintype m]   [inst_3 : DecidableEq m] (f : WithConv
 ((m → R) →ₗ[R] n → R)),   LinearMap.toMatrix' (star f).ofConv = (LinearMap.toMa
trix' f.ofConv).map star
参数：f : WithConv ((m → R) →ₗ[R] n → R)；star f；LinearMap.toMatrix' f.ofConv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `Pi.instStarModuleForall`：∀ {I : Type u} {f : I → Type v} {R : Type w} [i
nst : (i : I) → SMul R (f i)] [inst_1 : Star R]   [inst_2 : (i : I) → Star (f i)
] [∀ (i : I),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.star_single`：Pi.star_single {ι : Type*} {R : ι -> Type*} [DecidableEq
 ι] [forall i, AddMonoid (R i)] [forall i, StarAddMonoid (R i)] (i : ι) (r : R i
) : …
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix'_intrinsicStar (f : WithConv ((m → R) →ₗ[R] (n → R))) :
    (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star := by
  ext; simp

/-- A linear map `f : (m → R) →ₗ (n → R)` is self-adjoint (with respect to the intrinsic star)
iff its corresponding matrix `f.toMatrix'` has all self-adjoint elements.
So star-preserving maps correspond to their matrices containing only self-adjoint elements. -/
/-
**LinearMap.IntrinsicStar.isSelfAdjoint_iff_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap.IntrinsicStar`。
形式化陈述：∀ {R : Type u_4} {m : Type u_5} {n : Type u_6} [inst : CommSemiring R] [in
st_1 : StarRing R] [inst_2 : Fintype m]   [inst_3 : DecidableEq m] (f : WithConv
 ((m → R) →ₗ[R] n → R)),   IsSelfAdjoint f ↔ ∀ (i : n) (j : m), IsSelfAdjoint (L
inearMap.toMatrix' f.ofConv i j)
参数：f : WithConv ((m → R) →ₗ[R] n → R)；i : n；j : m；LinearMap.toMatrix' f.ofConv i
 j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Pi.instStarModuleForall`：∀ {I : Type u} {f : I → Type v} {R : Type w} [i
nst : (i : I) → SMul R (f i)] [inst_1 : Star R]   [inst_2 : (i : I) → Star (f i)
] [∀ (i : I),…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `LinearMap.toMatrix'_intrinsicStar`：∀ {R : Type u_4} {m : Type u_5} {n : 
Type u_6} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : Fintype m]   [
inst_3 : DecidableEq m]…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A linear map `f : (m → R) →ₗ (n → R)` is self-adjoint (with respect to the intri
nsic star)
iff its corresponding matrix `f.toMatrix'` has all self-adjoint elements.
So star-preserving maps correspond to their matrices containing only self-adjoin
t elements.
-/
theorem IntrinsicStar.isSelfAdjoint_iff_toMatrix' (f : WithConv ((m → R) →ₗ[R] (n → R))) :
    IsSelfAdjoint f ↔ ∀ i j, IsSelfAdjoint (f.ofConv.toMatrix' i j) := by
  simp [IsSelfAdjoint, ← toMatrix'.injective.eq_iff, toMatrix'_intrinsicStar, ← Matrix.ext_iff,
    WithConv.ext_iff]

end LinearMap

namespace Matrix

/-
**Matrix.intrinsicStar_toLin'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：intrinsicStar_toLin' (A : Matrix n m R) : star (toConv A.toLin') = toConv 
(A.map star).toLin'
参数：A : Matrix n m R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Pi.instStarModuleForall`：∀ {I : Type u} {f : I → Type v} {R : Type w} [i
nst : (i : I) → SMul R (f i)] [inst_1 : Star R]   [inst_2 : (i : I) → Star (f i)
] [∀ (i : I),…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix'_intrinsicStar`：∀ {R : Type u_4} {m : Type u_5} {n : 
Type u_6} [inst : CommSemiring R] [inst_1 : StarRing R] [inst_2 : Fintype m]   [
inst_3 : DecidableEq m]…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.toMatrix'_toLin'`：∀ {R : Type u_1} [inst : CommSemiring R] {m 
: Type u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (M : 
Matrix m n R), L…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intrinsicStar_toLin' (A : Matrix n m R) :
    star (toConv A.toLin') = toConv (A.map star).toLin' := by
  simp [← LinearMap.toMatrix'.injective.eq_iff, LinearMap.toMatrix'_intrinsicStar, WithConv.ext_iff]

/-- Given a matrix `A`, `A.toLin'` is self-adjoint (with respect to the intrinsic star)
iff all its elements are self-adjoint. -/
/-
**Matrix.IntrinsicStar.isSelfAdjoint_toLin'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matri
x.IntrinsicStar`。
形式化陈述：∀ {R : Type u_4} {m : Type u_5} {n : Type u_6} [inst : CommSemiring R] [in
st_1 : StarRing R] [inst_2 : Fintype m]   [inst_3 : DecidableEq m] (A : Matrix n
 m R),   IsSelfAdjoint (WithConv.toConv (Matrix.toLin' A)) ↔ ∀ (i : n) (j : m), 
IsSelfAdjoint (A i j)
参数：A : Matrix n m R；WithConv.toConv (Matrix.toLin' A)；i : n；j : m；A i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Pi.instStarModuleForall`：∀ {I : Type u} {f : I → Type v} {R : Type w} [i
nst : (i : I) → SMul R (f i)] [inst_1 : Star R]   [inst_2 : (i : I) → Star (f i)
] [∀ (i : I),…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.intrinsicStar_toLin'`：intrinsicStar_toLin' (A : Matrix n m R) : s
tar (toConv A.toLin') = toConv (A.map star).toLin'
· 使用定理 `WithConv.toConv.injEq`：∀ {A : Sort u_1} (ofConv ofConv_1 : A), (WithConv
.toConv ofConv = WithConv.toConv ofConv_1) = (ofConv = ofConv_1)
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given a matrix `A`, `A.toLin'` is self-adjoint (with respect to the intrinsic st
ar)
iff all its elements are self-adjoint.
-/
theorem IntrinsicStar.isSelfAdjoint_toLin'_iff (A : Matrix n m R) :
    IsSelfAdjoint (toConv A.toLin') ↔ ∀ i j, IsSelfAdjoint (A i j) := by
  simp [IsSelfAdjoint, intrinsicStar_toLin', ← ext_iff]

end Matrix
end matrix

namespace Module.End

/-- Intrinsic star operation for `(End R E)ˣ`. -/
/-
**Module.End.Units.intrinsicStar** 是 Mathlib 中的一个定义，位于命名空间 `Module.End.Units`。
形式化陈述：{R : Type u_1} →   {E : Type u_2} →     [inst : Semiring R] →       [inst_
1 : InvolutiveStar R] →         [inst_2 : AddCommMonoid E] →           [inst_3 :
 _root_.Module R E] →             [inst_4 : StarAddMonoid E] → [StarModule R E] 
→ Star (WithConv (Module.End R E)ˣ)
参数：WithConv (Module.End R E)ˣ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Intrinsic star operation for `(End R E)ˣ`.
-/
instance Units.intrinsicStar : Star (WithConv (End R E)ˣ) where
  star f := toConv <| by
    refine ⟨(star (toConv ↑f.ofConv : WithConv (End R E))).ofConv,
      (star (toConv ↑(f.ofConv⁻¹ : (End R E)ˣ))).ofConv, ?_, ?_⟩
    all_goals
      rw [mul_eq_comp, ← toConv_injective.eq_iff, ← LinearMap.intrinsicStar_comp']
      simp [← mul_eq_comp, one_eq_id]
/-
**Module.End.IsUnit.intrinsicStar** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.IsUnit`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [inst_1 : InvolutiveSt
ar R] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module R E] [inst_4 : StarAd
dMonoid E] [inst_5 : StarModule R E] {f : WithConv (Module.End R E)},   IsUnit f
.ofConv → IsUnit (star f).ofConv
参数：Module.End R E；star f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem IsUnit.intrinsicStar {f : WithConv (End R E)} (hf : IsUnit f.ofConv) :
    IsUnit (star f).ofConv := by
  have ⟨u, hu⟩ := hf
  have : IsUnit (star (toConv (u : End R E))).ofConv := (star (toConv u)).ofConv.isUnit
  simpa [hu] using this

open Module.End in
/-
**Module.End.isUnit_intrinsicStar_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} [inst : Semiring R] [inst_1 : InvolutiveSt
ar R] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module R E] [inst_4 : StarAd
dMonoid E] [inst_5 : StarModule R E] {f : WithConv (Module.End R E)},   IsUnit (
star f).ofConv ↔ IsUnit f.ofConv
参数：Module.End R E；star f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.IsUnit.intrinsicStar`：∀ {R : Type u_1} {E : Type u_2} [inst :
 Semiring R] [inst_1 : InvolutiveStar R] [inst_2 : AddCommMonoid E]   [inst_3 : 
_root_.Module R E] [i…
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
@[simp] theorem isUnit_intrinsicStar_iff {f : WithConv (End R E)} :
    IsUnit (star f).ofConv ↔ IsUnit f.ofConv :=
  ⟨fun h ↦ star_star f ▸ h.intrinsicStar, fun h ↦ h.intrinsicStar⟩

section eigenspace
variable {R V : Type*} [CommRing R] [InvolutiveStar R] [AddCommGroup V] [StarAddMonoid V]
  [Module R V] [StarModule R V]

open LinearMap

/-
**Module.End.mem_eigenspace_intrinsicStar_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.
End`。
形式化陈述：mem_eigenspace_intrinsicStar_iff (f : WithConv (End R V)) (α : R) (x : V) 
: x in (star f).ofConv.eigenspace α ↔ star x in f.ofConv.eigenspace (star α)
参数：f : WithConv (End R V)；α : R；x : V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_eigenspace_intrinsicStar_iff (f : WithConv (End R V)) (α : R) (x : V) :
    x ∈ (star f).ofConv.eigenspace α ↔ star x ∈ f.ofConv.eigenspace (star α) := by
  simp_rw [mem_eigenspace_iff, intrinsicStar_apply, star_eq_iff_star_eq, star_smul, eq_comm]

@[simp]
/-
**Module.End.spectrum_intrinsicStar** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：spectrum_intrinsicStar (f : WithConv (End R V)) : spectrum R (star f).ofCo
nv = star (spectrum R f.ofConv)
参数：f : WithConv (End R V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.isUnit_intrinsicStar_iff`：∀ {R : Type u_1} {E : Type u_2} [in
st : Semiring R] [inst_1 : InvolutiveStar R] [inst_2 : AddCommMonoid E]   [inst_
3 : _root_.Module R E] [i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `star_sub`：star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - 
s) = star r - star s
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `LinearMap.intrinsicStar_id`：∀ {R : Type u_1} {E : Type u_2} [inst : Semi
ring R] [inst_1 : InvolutiveStar R] [inst_2 : AddCommMonoid E]   [inst_3 : _root
_.Module R E] [i…
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem spectrum_intrinsicStar (f : WithConv (End R V)) :
    spectrum R (star f).ofConv = star (spectrum R f.ofConv) := by
  ext x
  simp_rw [Set.mem_star, spectrum.mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one]
  rw [← isUnit_intrinsicStar_iff]
  simp [one_eq_id]

end eigenspace
end Module.End

