/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Star.Rat

/-!
# Self-adjoint, skew-adjoint and normal elements of a star additive group

This file defines `selfAdjoint R` (resp. `skewAdjoint R`), where `R` is a star additive group,
as the additive subgroup containing the elements that satisfy `star x = x` (resp. `star x = -x`).
This includes, for instance, (skew-)Hermitian operators on Hilbert spaces.

We also define `IsStarNormal R`, a `Prop` that states that an element `x` satisfies
`star x * x = x * star x`.

## Implementation notes

* When `R` is a `StarModule R₂ R`, then `selfAdjoint R` has a natural
  `Module (selfAdjoint R₂) (selfAdjoint R)` structure. However, doing this literally would be
  undesirable since in the main case of interest (`R₂ = ℂ`) we want `Module ℝ (selfAdjoint R)`
  and not `Module (selfAdjoint ℂ) (selfAdjoint R)`. We solve this issue by adding the typeclass
  `[TrivialStar R₃]`, of which `ℝ` is an instance (registered in `Data/Real/Basic`), and then
  add a `[Module R₃ (selfAdjoint R)]` instance whenever we have
  `[Module R₃ R] [TrivialStar R₃]`. (Another approach would have been to define
  `[StarInvariantScalars R₃ R]` to express the fact that `star (x • v) = x • star v`, but
  this typeclass would have the disadvantage of taking two type arguments.)

## TODO

* Define `IsSkewAdjoint` to match `IsSelfAdjoint`.
* Define `fun z x => z * x * star z` (i.e. conjugation by `z`) as a monoid action of `R` on `R`
  (similar to the existing `ConjAct` for groups), and then state the fact that `selfAdjoint R` is
  invariant under it.

-/

@[expose] public section

open Function

variable {R A : Type*}

/-- An element is self-adjoint if it is equal to its star. -/
/-
**IsSelfAdjoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSelfAdjoint [Star R] (x : R) : Prop
参数：x : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element is self-adjoint if it is equal to its star.
-/
def IsSelfAdjoint [Star R] (x : R) : Prop :=
  star x = x

/-- An element of a star monoid is normal if it commutes with its adjoint. -/
@[mk_iff]
/-
**IsStarNormal** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [Mul R] → [Star R] → R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of a star monoid is normal if it commutes with its adjoint.
-/
class IsStarNormal [Mul R] [Star R] (x : R) : Prop where
  /-- A normal element of a star monoid commutes with its adjoint. -/
  star_comm_self : Commute (star x) x

export IsStarNormal (star_comm_self)

attribute [grind →] star_comm_self
/-
**star_comm_self'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal x] : star x * x = x
 * star x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStarNormal.star_comm_self`：∀ {R : Type u_1} {inst : Mul R} {inst_1 : S
tar R} {x : R} [self : IsStarNormal x], Commute (star x) x
-/
theorem star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal x] : star x * x = x * star x :=
  IsStarNormal.star_comm_self

namespace IsSelfAdjoint

-- named to match `Commute.allₓ`
/-- All elements are self-adjoint when `star` is trivial. -/
/-
**IsSelfAdjoint.all** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：all [Star R] [TrivialStar R] (r : R) : IsSelfAdjoint r
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r

--- 原说明 ---
All elements are self-adjoint when `star` is trivial.
-/
theorem all [Star R] [TrivialStar R] (r : R) : IsSelfAdjoint r :=
  star_trivial _
/-
**IsSelfAdjoint.star_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) : star x = x
参数：hx : IsSelfAdjoint x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) : star x = x :=
  hx

grind_pattern star_eq => IsSelfAdjoint x, star x
/-
**IsSelfAdjoint._root_.isSelfAdjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoin
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isSelfAdjoint_iff [Star R] {x : R} : IsSelfAdjoint x ↔ star x = x :=
  Iff.rfl

@[simp]
/-
**IsSelfAdjoint.star_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：star_iff [InvolutiveStar R] {x : R} : IsSelfAdjoint (star x) ↔ IsSelfAdjoi
nt x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem star_iff [InvolutiveStar R] {x : R} : IsSelfAdjoint (star x) ↔ IsSelfAdjoint x := by
  simpa only [IsSelfAdjoint, star_star] using eq_comm

@[simp]
/-
**IsSelfAdjoint.star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：star_mul_self [Mul R] [StarMul R] (x : R) : IsSelfAdjoint (star x * x)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
theorem star_mul_self [Mul R] [StarMul R] (x : R) : IsSelfAdjoint (star x * x) := by
  simp only [IsSelfAdjoint, star_mul, star_star]

@[simp]
/-
**IsSelfAdjoint.mul_star_self** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：mul_star_self [Mul R] [StarMul R] (x : R) : IsSelfAdjoint (x * star x)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `IsSelfAdjoint.star_mul_self`：star_mul_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (star x * x)
-/
theorem mul_star_self [Mul R] [StarMul R] (x : R) : IsSelfAdjoint (x * star x) := by
  simpa only [star_star] using star_mul_self (star x)

/-- Self-adjoint elements commute if and only if their product is self-adjoint. -/
/-
**IsSelfAdjoint.commute_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：commute_iff {R : Type*} [Mul R] [StarMul R] {x y : R} (hx : IsSelfAdjoint 
x) (hy : IsSelfAdjoint y) : Commute x y ↔ IsSelfAdjoint (x * y)
参数：hx : IsSelfAdjoint x；hy : IsSelfAdjoint y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSelfAdjoint_iff`：∀ {R : Type u_1} [inst : Star R] {x : R}, IsSelfAdjoi
nt x ↔ star x = x
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Self-adjoint elements commute if and only if their product is self-adjoint.
-/
lemma commute_iff {R : Type*} [Mul R] [StarMul R] {x y : R}
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : Commute x y ↔ IsSelfAdjoint (x * y) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [isSelfAdjoint_iff, star_mul, hx.star_eq, hy.star_eq, h.eq]
  · simpa only [star_mul, hx.star_eq, hy.star_eq] using! h.symm
/-
**IsSelfAdjoint.commute_of_mul_eq_isSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `IsSel
fAdjoint`。
形式化陈述：commute_of_mul_eq_isSelfAdjoint {R : Type*} [Mul R] [StarMul R] (x y z : R
) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) (hz : IsSelfAdjoint z) (hxyz : x
 * y = z) : Commute x y
参数：x y z : R；hx : IsSelfAdjoint x；hy : IsSelfAdjoint y；hz : IsSelfAdjoint z；hxyz
 : x * y = z。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma commute_of_mul_eq_isSelfAdjoint {R : Type*} [Mul R] [StarMul R] (x y z : R)
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) (hz : IsSelfAdjoint z) (hxyz : x * y = z) :
    Commute x y := by
  grind [commute_iff hx hy]

/-- Functions in a `StarHomClass` preserve self-adjoint elements. -/
@[aesop 10% apply]
/-
**IsSelfAdjoint.map** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：map {F R S : Type*} [Star R] [Star S] [FunLike F R S] [StarHomClass F R S]
 {x : R} (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f x)
参数：hx : IsSelfAdjoint x；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…

--- 原说明 ---
Functions in a `StarHomClass` preserve self-adjoint elements.
-/
theorem map {F R S : Type*} [Star R] [Star S] [FunLike F R S] [StarHomClass F R S]
    {x : R} (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f x) :=
  show star (f x) = f x from map_star f x ▸ congr_arg f hx

/- note: this lemma is *not* marked as `simp` so that Lean doesn't look for a `[TrivialStar R]`
/-
**IsSelfAdjoint.every** 是 Mathlib 中的一个实例，位于命名空间 `IsSelfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance every time it sees `⊢ IsSelfAdjoint (f x)`, which will likely occur relatively often. -/
/-
**IsSelfAdjoint._root_.isSelfAdjoint_map** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoin
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
note: this lemma is *not* marked as `simp` so that Lean doesn't look for a `[Tri
vialStar R]`
instance every time it sees `⊢ IsSelfAdjoint (f x)`, which will likely occur rel
atively often.
-/
theorem _root_.isSelfAdjoint_map {F R S : Type*} [Star R] [Star S] [FunLike F R S]
    [StarHomClass F R S] [TrivialStar R] (f : F) (x : R) : IsSelfAdjoint (f x) :=
  (IsSelfAdjoint.all x).map f

@[aesop 10% apply]
/-
**IsSelfAdjoint.isStarNormal** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：isStarNormal {R : Type*} [Mul R] [Star R] {x : R} (hx : IsSelfAdjoint x) :
 IsStarNormal x
参数：hx : IsSelfAdjoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isStarNormal {R : Type*} [Mul R] [Star R] {x : R} (hx : IsSelfAdjoint x) :
    IsStarNormal x := ⟨by simp only [Commute, SemiconjBy, hx.star_eq]⟩

section AddMonoid

variable [AddMonoid R] [StarAddMonoid R]

variable (R) in
/-
**IsSelfAdjoint.zero** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ (R : Type u_1) [inst : AddMonoid R] [inst_1 : StarAddMonoid R], IsSelfAd
joint 0
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
@[simp, grind .] protected theorem zero : IsSelfAdjoint (0 : R) := star_zero R

@[aesop 90% apply]
/-
**IsSelfAdjoint.add** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoin
t (x + y)
参数：hx : IsSelfAdjoint x；hy : IsSelfAdjoint y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x + y) := by
  simp only [isSelfAdjoint_iff, star_add, hx.star_eq, hy.star_eq]

end AddMonoid

section AddGroup

variable [AddGroup R] [StarAddMonoid R]

@[aesop safe apply]
/-
**IsSelfAdjoint.neg** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-x)
参数：hx : IsSelfAdjoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_neg`：star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = 
-star r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-x) := by
  simp only [isSelfAdjoint_iff, star_neg, hx.star_eq]

@[aesop 90% apply]
/-
**IsSelfAdjoint.sub** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoin
t (x - y)
参数：hx : IsSelfAdjoint x；hy : IsSelfAdjoint y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_sub`：star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - 
s) = star r - star s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x - y) := by
  simp only [isSelfAdjoint_iff, star_sub, hx.star_eq, hy.star_eq]

end AddGroup

section AddCommMonoid

variable [AddCommMonoid R] [StarAddMonoid R]

@[simp]
/-
**IsSelfAdjoint.add_star_self** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：add_star_self (x : R) : IsSelfAdjoint (x + star x)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_star_self (x : R) : IsSelfAdjoint (x + star x) := by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

@[simp]
/-
**IsSelfAdjoint.star_add_self** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：star_add_self (x : R) : IsSelfAdjoint (star x + x)
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem star_add_self (x : R) : IsSelfAdjoint (star x + x) := by
  simp only [isSelfAdjoint_iff, add_comm, star_add, star_star]

end AddCommMonoid

section Semigroup

variable [Semigroup R] [StarMul R]

@[aesop safe apply]
/-
**IsSelfAdjoint.conjugate** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：conjugate {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (z * x * 
star z)
参数：hx : IsSelfAdjoint x；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjugate {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (z * x * star z) := by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

@[aesop safe apply]
/-
**IsSelfAdjoint.conjugate'** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：conjugate' {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (star z 
* x * z)
参数：hx : IsSelfAdjoint x；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjugate' {x : R} (hx : IsSelfAdjoint x) (z : R) : IsSelfAdjoint (star z * x * z) := by
  simp only [isSelfAdjoint_iff, star_mul, star_star, mul_assoc, hx.star_eq]

@[aesop 90% apply]
/-
**IsSelfAdjoint.conjugate_self** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：conjugate_self {x : R} (hx : IsSelfAdjoint x) {z : R} (hz : IsSelfAdjoint 
z) : IsSelfAdjoint (z * x * z)
参数：hx : IsSelfAdjoint x；hz : IsSelfAdjoint z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSelfAdjoint.conjugate`：conjugate {x : R} (hx : IsSelfAdjoint x) (z : R
) : IsSelfAdjoint (z * x * star z)
-/
theorem conjugate_self {x : R} (hx : IsSelfAdjoint x) {z : R} (hz : IsSelfAdjoint z) :
    IsSelfAdjoint (z * x * z) := by nth_rewrite 2 [← hz]; exact conjugate hx z

end Semigroup

section MulOneClass

variable [MulOneClass R] [StarMul R]
variable (R)

/-
**IsSelfAdjoint.one** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ (R : Type u_1) [inst : MulOneClass R] [inst_1 : StarMul R], IsSelfAdjoin
t 1
参数：R : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
-/
@[simp, grind .] protected theorem one : IsSelfAdjoint (1 : R) :=
  star_one R

end MulOneClass

section Monoid

variable [Monoid R] [StarMul R]

@[aesop safe apply]
/-
**IsSelfAdjoint.pow** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：pow {x : R} (hx : IsSelfAdjoint x) (n : Nat) : IsSelfAdjoint (x ^ n)
参数：hx : IsSelfAdjoint x；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_pow`：star_pow [Monoid R] [StarMul R] (x : R) (n : Nat) : star (x ^ 
n) = star x ^ n
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow {x : R} (hx : IsSelfAdjoint x) (n : ℕ) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_pow, hx.star_eq]

@[simp]
/-
**IsSelfAdjoint.invOf_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：invOf_iff (x : R) [Invertible x] : IsSelfAdjoint ⅟x ↔ IsSelfAdjoint x
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSelfAdjoint_iff`：∀ {R : Type u_1} [inst : Star R] {x : R}, IsSelfAdjoi
nt x ↔ star x = x
· 使用定理 `star_invOf`：star_invOf {R : Type*} [Monoid R] [StarMul R] (r : R) [Inver
tible r] [Invertible (star r)] : star (⅟r) = ⅟(star r)
· 使用定理 `invOf_inj`：invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] 
: ⅟a = ⅟b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem invOf_iff (x : R) [Invertible x] : IsSelfAdjoint ⅟x ↔ IsSelfAdjoint x := by
  rw [isSelfAdjoint_iff, isSelfAdjoint_iff, star_invOf, invOf_inj]

alias ⟨_, invOf⟩ := invOf_iff

@[grind =]
/-
**IsSelfAdjoint._root_.IsUnit.isSelfAdjoint_conjugate_iff** 是 Mathlib 中的一个引理，位于命
名空间 `IsSelfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsUnit.isSelfAdjoint_conjugate_iff {a u : R} (hu : IsUnit u) :
    IsSelfAdjoint (u * a * star u) ↔ IsSelfAdjoint a := by
  simp [IsSelfAdjoint, mul_assoc, hu.mul_right_inj, hu.star.mul_left_inj]

@[grind =]
/-
**IsSelfAdjoint._root_.IsUnit.isSelfAdjoint_conjugate_iff'** 是 Mathlib 中的一个引理，位于
命名空间 `IsSelfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsUnit.isSelfAdjoint_conjugate_iff' {a u : R} (hu : IsUnit u) :
    IsSelfAdjoint (star u * a * u) ↔ IsSelfAdjoint a := by
  simpa using hu.star.isSelfAdjoint_conjugate_iff

end Monoid

section Semiring

open Ring

variable [NonAssocSemiring R] [StarRing R]

@[simp]
/-
**IsSelfAdjoint.natCast** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {R : Type u_1} [inst : NonAssocSemiring R] [inst_1 : StarRing R] (n : ℕ)
, IsSelfAdjoint ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_natCast`：star_natCast [NonAssocSemiring R] [StarRing R] (n : Nat) :
 star (n : R) = n
-/
protected theorem natCast (n : ℕ) : IsSelfAdjoint (n : R) :=
  star_natCast _

@[simp, grind .]
/-
**IsSelfAdjoint.ofNat** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {R : Type u_1} [inst : NonAssocSemiring R] [inst_1 : StarRing R] (n : ℕ)
 [inst_2 : n.AtLeastTwo],   IsSelfAdjoint (OfNat.ofNat n)
参数：n : ℕ；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.natCast`：∀ {R : Type u_1} [inst : NonAssocSemiring R] [ins
t_1 : StarRing R] (n : ℕ), IsSelfAdjoint ↑n
-/
protected theorem ofNat (n : ℕ) [n.AtLeastTwo] : IsSelfAdjoint (ofNat(n) : R) :=
  .natCast n

@[aesop safe apply, grind ←]
/-
**IsSelfAdjoint.ringInverse** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {A : Type u_2} {a : A} [inst : Semiring A] [inst_1 : StarRing A], IsSelf
Adjoint a → IsSelfAdjoint (Ring.inverse a)
参数：Ring.inverse a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isSelfAdjoint_iff`：∀ {R : Type u_1} [inst : Star R] {x : R}, IsSelfAdjoi
nt x ↔ star x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_star`：Ring.inverse_star [Semiring R] [StarRing R] (a : R) :
 (star a)⁻¹ʳ = star (a⁻¹ʳ)
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
-/
protected theorem ringInverse {a : A} [Semiring A] [StarRing A]
    (ha : IsSelfAdjoint a) : IsSelfAdjoint a⁻¹ʳ := by
  rw [isSelfAdjoint_iff, ← Ring.inverse_star, ha.star_eq]
/-
**IsSelfAdjoint._root_.isSelfAdjoint_ringInverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `
IsSelfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isSelfAdjoint_ringInverse_iff {a : A} [Semiring A] [StarRing A] (ha : IsUnit a) :
    IsSelfAdjoint a⁻¹ʳ ↔ IsSelfAdjoint a :=
  ⟨fun h => by grind [h.ringInverse], fun h => h.ringInverse⟩

end Semiring

section CommSemigroup

variable [CommSemigroup R] [StarMul R]

/-
**IsSelfAdjoint.mul** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：mul {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoin
t (x * y)
参数：hx : IsSelfAdjoint x；hy : IsSelfAdjoint y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_mul'`：star_mul' [CommMagma R] [StarMul R] (x y : R) : star (x * y) 
= star x * star y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x * y) := by
  simp only [isSelfAdjoint_iff, star_mul', hx.star_eq, hy.star_eq]

end CommSemigroup

section CommSemiring
variable {α : Type*} [CommSemiring α] [StarRing α] {a : α}

open scoped ComplexConjugate

/-
**IsSelfAdjoint.conj_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：conj_eq (ha : IsSelfAdjoint a) : conj a = a
参数：ha : IsSelfAdjoint a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
-/
lemma conj_eq (ha : IsSelfAdjoint a) : conj a = a := ha.star_eq

end CommSemiring

section Ring

variable [Ring R] [StarRing R]

@[simp]
/-
**IsSelfAdjoint.intCast** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] [inst_1 : StarRing R] (z : ℤ), IsSelfAdjo
int ↑z
参数：z : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_intCast`：star_intCast [NonAssocRing R] [StarRing R] (z : Int) : sta
r (z : R) = z
-/
protected theorem intCast (z : ℤ) : IsSelfAdjoint (z : R) :=
  star_intCast _

end Ring

section Group

variable [Group R] [StarMul R]

@[aesop safe apply]
/-
**IsSelfAdjoint.inv** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：inv {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹
参数：hx : IsSelfAdjoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_inv`：star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹ := by
  simp only [isSelfAdjoint_iff, star_inv, hx.star_eq]

@[simp]
/-
**IsSelfAdjoint.inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：inv_iff (x : R) : IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_inv`：star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inv_iff (x : R) : IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x := by
  simp [isSelfAdjoint_iff]

@[aesop safe apply]
/-
**IsSelfAdjoint.zpow** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：zpow {x : R} (hx : IsSelfAdjoint x) (n : Int) : IsSelfAdjoint (x ^ n)
参数：hx : IsSelfAdjoint x；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_zpow`：star_zpow [Group R] [StarMul R] (x : R) (z : Int) : star (x ^
 z) = star x ^ z
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zpow {x : R} (hx : IsSelfAdjoint x) (n : ℤ) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_zpow, hx.star_eq]

end Group

section GroupWithZero

variable [GroupWithZero R] [StarMul R]

@[aesop safe apply]
/-
**IsSelfAdjoint.inv** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：inv {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹
参数：hx : IsSelfAdjoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_inv`：star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv₀ {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹ := by
  simp only [isSelfAdjoint_iff, star_inv₀, hx.star_eq]

@[simp]
/-
**IsSelfAdjoint.inv** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：inv {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻¹
参数：hx : IsSelfAdjoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_inv`：star_inv [Group R] [StarMul R] (x : R) : star x⁻¹ = (star x)⁻¹
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv₀_iff (x : R) : IsSelfAdjoint x⁻¹ ↔ IsSelfAdjoint x := by
  simp [isSelfAdjoint_iff]

@[aesop safe apply]
/-
**IsSelfAdjoint.zpow** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：zpow {x : R} (hx : IsSelfAdjoint x) (n : Int) : IsSelfAdjoint (x ^ n)
参数：hx : IsSelfAdjoint x；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_zpow`：star_zpow [Group R] [StarMul R] (x : R) (z : Int) : star (x ^
 z) = star x ^ z
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zpow₀ {x : R} (hx : IsSelfAdjoint x) (n : ℤ) : IsSelfAdjoint (x ^ n) := by
  simp only [isSelfAdjoint_iff, star_zpow₀, hx.star_eq]

end GroupWithZero

@[simp]
/-
**IsSelfAdjoint.nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionSemiring R] [inst_1 : StarRing R] (q : ℚ≥
0), IsSelfAdjoint ↑q
参数：q : ℚ≥0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `star_nnratCast`：star_nnratCast [DivisionSemiring R] [StarRing R] (q : Ra
t>=0) : star (q : R) = q
-/
protected lemma nnratCast [DivisionSemiring R] [StarRing R] (q : ℚ≥0) :
    IsSelfAdjoint (q : R) :=
  star_nnratCast _

section DivisionRing

variable [DivisionRing R] [StarRing R]

@[simp]
/-
**IsSelfAdjoint.ratCast** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：∀ {R : Type u_1} [inst : DivisionRing R] [inst_1 : StarRing R] (x : ℚ), Is
SelfAdjoint ↑x
参数：x : ℚ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `star_ratCast`：star_ratCast [DivisionRing R] [StarRing R] (r : Rat) : sta
r (r : R) = r
-/
protected theorem ratCast (x : ℚ) : IsSelfAdjoint (x : R) :=
  star_ratCast _

end DivisionRing

section Semifield

variable [Semifield R] [StarRing R]

/-
**IsSelfAdjoint.div** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：div {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoin
t (x / y)
参数：hx : IsSelfAdjoint x；hy : IsSelfAdjoint y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_div₀`：star_div₀ [CommGroupWithZero R] [StarMul R] (x y : R) : star 
(x / y) = star x / star y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem div {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) : IsSelfAdjoint (x / y) := by
  simp only [isSelfAdjoint_iff, star_div₀, hx.star_eq, hy.star_eq]

end Semifield

section SMul

@[aesop safe apply]
/-
**IsSelfAdjoint.smul** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：smul [Star R] [Star A] [SMul R A] [StarModule R A] {r : R} (hr : IsSelfAdj
oint r) {x : A} (hx : IsSelfAdjoint x) : IsSelfAdjoint (r • x)
参数：hr : IsSelfAdjoint r；hx : IsSelfAdjoint x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul [Star R] [Star A] [SMul R A] [StarModule R A]
    {r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (r • x) := by
  simp only [isSelfAdjoint_iff, star_smul, hr.star_eq, hx.star_eq]
/-
**IsSelfAdjoint.smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSelfAdjoint`。
形式化陈述：smul_iff [Monoid R] [StarMul R] [Star A] [MulAction R A] [StarModule R A] 
{r : R} (hr : IsSelfAdjoint r) (hu : IsUnit r) {x : A} : IsSelfAdjoint (r • x) ↔
 IsSelfAdjoint x
参数：hr : IsSelfAdjoint r；hu : IsUnit r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `IsSelfAdjoint.smul`：smul [Star R] [Star A] [SMul R A] [StarModule R A] {
r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) : IsSelfAdjoint (r 
• x)
· 使用定理 `Units.instStarModule`：∀ {R : Type u} [inst : Monoid R] [inst_1 : StarMul
 R] {A : Type u_1} [inst_2 : Star A] [inst_3 : SMul R A]   [StarModule R A], Sta
rModule Rˣ…
· 使用定理 `IsSelfAdjoint.inv`：inv {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint x⁻
¹
-/
theorem smul_iff [Monoid R] [StarMul R] [Star A]
    [MulAction R A] [StarModule R A] {r : R} (hr : IsSelfAdjoint r) (hu : IsUnit r) {x : A} :
    IsSelfAdjoint (r • x) ↔ IsSelfAdjoint x := by
  refine ⟨fun hrx ↦ ?_, .smul hr⟩
  lift r to Rˣ using hu
  rw [← inv_smul_smul r x]
  replace hr : IsSelfAdjoint r := Units.ext hr.star_eq
  exact hr.inv.smul hrx

end SMul

end IsSelfAdjoint

variable (R)

/-- The self-adjoint elements of a star additive group, as an additive subgroup. -/
/-
**selfAdjoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：selfAdjoint [AddGroup R] [StarAddMonoid R] : AddSubgroup R where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.neg`：neg {x : R} (hx : IsSelfAdjoint x) : IsSelfAdjoint (-
x)

--- 原说明 ---
The self-adjoint elements of a star additive group, as an additive subgroup.
-/
def selfAdjoint [AddGroup R] [StarAddMonoid R] : AddSubgroup R where
  carrier := { x | IsSelfAdjoint x }
  zero_mem' := star_zero R
  add_mem' hx := hx.add
  neg_mem' hx := hx.neg

/-- The skew-adjoint elements of a star additive group, as an additive subgroup. -/
/-
**skewAdjoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：skewAdjoint [AddCommGroup R] [StarAddMonoid R] : AddSubgroup R where carri
er
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The skew-adjoint elements of a star additive group, as an additive subgroup.
-/
def skewAdjoint [AddCommGroup R] [StarAddMonoid R] : AddSubgroup R where
  carrier := { x | star x = -x }
  zero_mem' := show star (0 : R) = -0 by simp only [star_zero, neg_zero]
  add_mem' := @fun x y (hx : star x = -x) (hy : star y = -y) =>
    show star (x + y) = -(x + y) by rw [star_add x y, hx, hy, neg_add]
  neg_mem' := @fun x (hx : star x = -x) => show star (-x) = - -x by simp only [hx, star_neg]

variable {R}

namespace selfAdjoint

section AddGroup

variable [AddGroup R] [StarAddMonoid R]

/-
**selfAdjoint.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：mem_iff {x : R} : x in selfAdjoint R ↔ star x = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.mem_carrier`：∀ {G : Type u_1} [inst : AddGroup G] {s : AddSu
bgroup G} {x : G}, x ∈ s.carrier ↔ x ∈ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff {x : R} : x ∈ selfAdjoint R ↔ star x = x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]
/-
**selfAdjoint.star_val_eq** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：star_val_eq {x : selfAdjoint R} : star (x : R) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem star_val_eq {x : selfAdjoint R} : star (x : R) = x :=
  x.prop
/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (selfAdjoint R) :=
  ⟨0⟩

@[simp]
/-
**selfAdjoint.isSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 `selfAdjoint`。
形式化陈述：isSelfAdjoint {x : selfAdjoint R} : IsSelfAdjoint (x : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `selfAdjoint.star_val_eq`：star_val_eq {x : selfAdjoint R} : star (x : R) 
= x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isSelfAdjoint {x : selfAdjoint R} : IsSelfAdjoint (x : R) := by simp [isSelfAdjoint_iff]

end AddGroup

/-
**selfAdjoint.isStarNormal** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
形式化陈述：isStarNormal [NonUnitalRing R] [StarRing R] (x : selfAdjoint R) : IsStarNo
rmal (x : R)
参数：x : selfAdjoint R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.isStarNormal`：isStarNormal {R : Type*} [Mul R] [Star R] {x
 : R} (hx : IsSelfAdjoint x) : IsStarNormal x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
instance isStarNormal [NonUnitalRing R] [StarRing R] (x : selfAdjoint R) :
    IsStarNormal (x : R) :=
  x.prop.isStarNormal

section Ring

variable [Ring R] [StarRing R]

/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (selfAdjoint R) :=
  ⟨⟨1, .one R⟩⟩

@[simp, norm_cast]
/-
**selfAdjoint.val_one** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：val_one : ↑(1 : selfAdjoint R) = (1 : R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_one : ↑(1 : selfAdjoint R) = (1 : R) :=
  rfl
/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial (selfAdjoint R) :=
  ⟨⟨0, 1, ne_of_apply_ne Subtype.val zero_ne_one⟩⟩
/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast (selfAdjoint R) where
  natCast n := ⟨n, .natCast _⟩
/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast (selfAdjoint R) where
  intCast n := ⟨n, .intCast _⟩
/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (selfAdjoint R) ℕ where
  pow x n := ⟨(x : R) ^ n, x.prop.pow n⟩

@[simp, norm_cast]
/-
**selfAdjoint.val_pow** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：val_pow (x : selfAdjoint R) (n : Nat) : ↑(x ^ n) = (x : R) ^ n
参数：x : selfAdjoint R；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_pow (x : selfAdjoint R) (n : ℕ) : ↑(x ^ n) = (x : R) ^ n :=
  rfl

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing R] [StarRing R]

/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (selfAdjoint R) where
  mul x y := ⟨(x : R) * y, x.prop.mul y.prop⟩

@[simp, norm_cast]
/-
**selfAdjoint.val_mul** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：val_mul (x y : selfAdjoint R) : ↑(x * y) = (x : R) * y
参数：x y : selfAdjoint R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mul (x y : selfAdjoint R) : ↑(x * y) = (x : R) * y :=
  rfl

end NonUnitalCommRing

section CommRing

variable [CommRing R] [StarRing R]

/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommRing (selfAdjoint R) :=
  Function.Injective.commRing _ Subtype.coe_injective (selfAdjoint R).coe_zero val_one
    (selfAdjoint R).coe_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).coe_sub
    (by intros; rfl) (by intros; rfl) val_pow
    (fun _ => rfl) fun _ => rfl

end CommRing

section Field

variable [Field R] [StarRing R]

/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (selfAdjoint R) where
  inv x := ⟨x.val⁻¹, x.prop.inv₀⟩

@[simp, norm_cast]
/-
**selfAdjoint.val_inv** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：val_inv (x : selfAdjoint R) : ↑x⁻¹ = (x : R)⁻¹
参数：x : selfAdjoint R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_inv (x : selfAdjoint R) : ↑x⁻¹ = (x : R)⁻¹ :=
  rfl
/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Div (selfAdjoint R) where
  div x y := ⟨x / y, x.prop.div y.prop⟩

@[simp, norm_cast]
/-
**selfAdjoint.val_div** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：val_div (x y : selfAdjoint R) : ↑(x / y) = (x / y : R)
参数：x y : selfAdjoint R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_div (x y : selfAdjoint R) : ↑(x / y) = (x / y : R) :=
  rfl
/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (selfAdjoint R) ℤ where
  pow x z := ⟨(x : R) ^ z, x.prop.zpow₀ z⟩

@[simp, norm_cast]
/-
**selfAdjoint.val_zpow** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：val_zpow (x : selfAdjoint R) (z : Int) : ↑(x ^ z) = (x : R) ^ z
参数：x : selfAdjoint R；z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_zpow (x : selfAdjoint R) (z : ℤ) : ↑(x ^ z) = (x : R) ^ z :=
  rfl
/-
**selfAdjoint.instNNRatCast** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
形式化陈述：instNNRatCast : NNRatCast (selfAdjoint R) where nnratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNNRatCast : NNRatCast (selfAdjoint R) where
  nnratCast q := ⟨q, .nnratCast q⟩
/-
**selfAdjoint.instRatCast** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
形式化陈述：instRatCast : RatCast (selfAdjoint R) where ratCast q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRatCast : RatCast (selfAdjoint R) where
  ratCast q := ⟨q, .ratCast q⟩
/-
**selfAdjoint.val_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] [inst_1 : StarRing R] (q : ℚ≥0), ↑↑q = ↑
q
参数：q : ℚ≥0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_nnratCast (q : ℚ≥0) : (q : selfAdjoint R) = (q : R) := rfl
/-
**selfAdjoint.val_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] [inst_1 : StarRing R] (q : ℚ), ↑↑q = ↑q
参数：q : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_ratCast (q : ℚ) : (q : selfAdjoint R) = (q : R) := rfl
/-
**selfAdjoint.instSMulNNRat** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
形式化陈述：instSMulNNRat : SMul Rat>=0 (selfAdjoint R) where smul a x
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulNNRat : SMul ℚ≥0 (selfAdjoint R) where
  smul a x := ⟨a • (x : R), by rw [NNRat.smul_def]; exact .mul (.nnratCast a) x.prop⟩
/-
**selfAdjoint.instSMulRat** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
形式化陈述：instSMulRat : SMul Rat (selfAdjoint R) where smul a x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulRat : SMul ℚ (selfAdjoint R) where
  smul a x := ⟨a • (x : R), by rw [Rat.smul_def]; exact .mul (.ratCast a) x.prop⟩
/-
**selfAdjoint.val_nnqsmul** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] [inst_1 : StarRing R] (q : ℚ≥0) (x : ↥(s
elfAdjoint R)), ↑(q • x) = q • ↑x
参数：q : ℚ≥0；x : ↥(selfAdjoint R)；q • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_nnqsmul (q : ℚ≥0) (x : selfAdjoint R) : ↑(q • x) = q • (x : R) := rfl
/-
**selfAdjoint.val_qsmul** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：∀ {R : Type u_1} [inst : Field R] [inst_1 : StarRing R] (q : ℚ) (x : ↥(sel
fAdjoint R)), ↑(q • x) = q • ↑x
参数：q : ℚ；x : ↥(selfAdjoint R)；q • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_qsmul (q : ℚ) (x : selfAdjoint R) : ↑(q • x) = q • (x : R) := rfl
/-
**selfAdjoint.instField** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
形式化陈述：instField : Field (selfAdjoint R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `selfAdjoint.val_inv`：val_inv (x : selfAdjoint R) : ↑x⁻¹ = (x : R)⁻¹
· 使用定理 `selfAdjoint.val_div`：val_div (x y : selfAdjoint R) : ↑(x / y) = (x / y :
 R)
· 使用定理 `selfAdjoint.val_nnqsmul`：∀ {R : Type u_1} [inst : Field R] [inst_1 : Sta
rRing R] (q : ℚ≥0) (x : ↥(selfAdjoint R)), ↑(q • x) = q • ↑x
· 使用定理 `selfAdjoint.val_qsmul`：∀ {R : Type u_1} [inst : Field R] [inst_1 : StarR
ing R] (q : ℚ) (x : ↥(selfAdjoint R)), ↑(q • x) = q • ↑x
· 使用定理 `selfAdjoint.val_zpow`：val_zpow (x : selfAdjoint R) (z : Int) : ↑(x ^ z) 
= (x : R) ^ z
· 使用定理 `selfAdjoint.val_nnratCast`：∀ {R : Type u_1} [inst : Field R] [inst_1 : S
tarRing R] (q : ℚ≥0), ↑↑q = ↑q
· 使用定理 `selfAdjoint.val_ratCast`：∀ {R : Type u_1} [inst : Field R] [inst_1 : Sta
rRing R] (q : ℚ), ↑↑q = ↑q
-/
instance instField : Field (selfAdjoint R) :=
  Subtype.coe_injective.field _ (selfAdjoint R).coe_zero val_one
    (selfAdjoint R).coe_add val_mul (selfAdjoint R).coe_neg (selfAdjoint R).coe_sub
    val_inv val_div (swap (selfAdjoint R).coe_nsmul) (by intros; rfl) val_nnqsmul
    val_qsmul val_pow val_zpow (fun _ => rfl) (fun _ => rfl) val_nnratCast val_ratCast

end Field

section SMul

variable [Star R] [TrivialStar R] [AddGroup A] [StarAddMonoid A]

/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R A] [StarModule R A] : SMul R (selfAdjoint A) where
  smul r x := ⟨r • (x : A), (IsSelfAdjoint.all _).smul x.prop⟩

@[simp, norm_cast]
/-
**selfAdjoint.val_smul** 是 Mathlib 中的一个定理，位于命名空间 `selfAdjoint`。
形式化陈述：val_smul [SMul R A] [StarModule R A] (r : R) (x : selfAdjoint A) : ↑(r • x
) = r • (x : A)
参数：r : R；x : selfAdjoint A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_smul [SMul R A] [StarModule R A] (r : R) (x : selfAdjoint A) : ↑(r • x) = r • (x : A) :=
  rfl
/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [MulAction R A] [StarModule R A] : MulAction R (selfAdjoint A) :=
  Function.Injective.mulAction Subtype.val Subtype.coe_injective val_smul
/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (selfAdjoint A) :=
  Function.Injective.distribMulAction (selfAdjoint A).subtype Subtype.coe_injective val_smul

end SMul

section Module

variable [Star R] [TrivialStar R] [AddCommGroup A] [StarAddMonoid A]

/-
**selfAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `selfAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [Module R A] [StarModule R A] : Module R (selfAdjoint A) :=
  Function.Injective.module R (selfAdjoint A).subtype Subtype.coe_injective val_smul

end Module

end selfAdjoint

namespace skewAdjoint

section AddGroup

variable [AddCommGroup R] [StarAddMonoid R]

/-
**skewAdjoint.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `skewAdjoint`。
形式化陈述：mem_iff {x : R} : x in skewAdjoint R ↔ star x = -x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.mem_carrier`：∀ {G : Type u_1} [inst : AddGroup G] {s : AddSu
bgroup G} {x : G}, x ∈ s.carrier ↔ x ∈ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff {x : R} : x ∈ skewAdjoint R ↔ star x = -x := by
  rw [← AddSubgroup.mem_carrier]
  exact Iff.rfl

@[simp, norm_cast]
/-
**skewAdjoint.star_val_eq** 是 Mathlib 中的一个定理，位于命名空间 `skewAdjoint`。
形式化陈述：star_val_eq {x : skewAdjoint R} : star (x : R) = -x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem star_val_eq {x : skewAdjoint R} : star (x : R) = -x :=
  x.prop
/-
**skewAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `skewAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (skewAdjoint R) :=
  ⟨0⟩

end AddGroup

section Ring

variable [Ring R] [StarRing R]

/-
**skewAdjoint.conjugate** 是 Mathlib 中的一个定理，位于命名空间 `skewAdjoint`。
形式化陈述：conjugate {x : R} (hx : x in skewAdjoint R) (z : R) : z * x * star z in sk
ewAdjoint R
参数：hx : x in skewAdjoint R；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `skewAdjoint.mem_iff`：mem_iff {x : R} : x in skewAdjoint R ↔ star x = -x
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjugate {x : R} (hx : x ∈ skewAdjoint R) (z : R) : z * x * star z ∈ skewAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]
/-
**skewAdjoint.conjugate'** 是 Mathlib 中的一个定理，位于命名空间 `skewAdjoint`。
形式化陈述：conjugate' {x : R} (hx : x in skewAdjoint R) (z : R) : star z * x * z in s
kewAdjoint R
参数：hx : x in skewAdjoint R；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `skewAdjoint.mem_iff`：mem_iff {x : R} : x in skewAdjoint R ↔ star x = -x
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem conjugate' {x : R} (hx : x ∈ skewAdjoint R) (z : R) : star z * x * z ∈ skewAdjoint R := by
  simp only [mem_iff, star_mul, star_star, mem_iff.mp hx, neg_mul, mul_neg, mul_assoc]
/-
**skewAdjoint.isStarNormal_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `skewAdjoint`。
形式化陈述：isStarNormal_of_mem {x : R} (hx : x in skewAdjoint R) : IsStarNormal x
参数：hx : x in skewAdjoint R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isStarNormal_of_mem {x : R} (hx : x ∈ skewAdjoint R) : IsStarNormal x :=
  ⟨by
    simp only [mem_iff] at hx
    simp only [hx, Commute.neg_left, Commute.refl]⟩
/-
**skewAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `skewAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : skewAdjoint R) : IsStarNormal (x : R) :=
  isStarNormal_of_mem (SetLike.coe_mem _)

end Ring

section SMul

variable [Star R] [TrivialStar R] [AddCommGroup A] [StarAddMonoid A]

@[aesop 90% (rule_sets := [SetLike])]
/-
**skewAdjoint.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `skewAdjoint`。
形式化陈述：smul_mem [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) {x : A
} (h : x in skewAdjoint A) : r • x in skewAdjoint A
参数：r : R；h : x in skewAdjoint A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `skewAdjoint.mem_iff`：mem_iff {x : R} : x in skewAdjoint R ↔ star x = -x
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
-/
theorem smul_mem [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) {x : A}
    (h : x ∈ skewAdjoint A) : r • x ∈ skewAdjoint A := by
  rw [mem_iff, star_smul, star_trivial, mem_iff.mp h, smul_neg r]
/-
**skewAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `skewAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [DistribMulAction R A] [StarModule R A] : SMul R (skewAdjoint A) where
  smul r x := ⟨r • (x : A), smul_mem r x.prop⟩

@[simp, norm_cast]
/-
**skewAdjoint.val_smul** 是 Mathlib 中的一个定理，位于命名空间 `skewAdjoint`。
形式化陈述：val_smul [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) (x : s
kewAdjoint A) : ↑(r • x) = r • (x : A)
参数：r : R；x : skewAdjoint A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_smul [Monoid R] [DistribMulAction R A] [StarModule R A] (r : R) (x : skewAdjoint A) :
    ↑(r • x) = r • (x : A) :=
  rfl
/-
**skewAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `skewAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [DistribMulAction R A] [StarModule R A] : DistribMulAction R (skewAdjoint A) :=
  Function.Injective.distribMulAction (skewAdjoint A).subtype Subtype.coe_injective val_smul
/-
**skewAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `skewAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [Module R A] [StarModule R A] : Module R (skewAdjoint A) :=
  Function.Injective.module R (skewAdjoint A).subtype Subtype.coe_injective val_smul

end SMul

end skewAdjoint

/-- Scalar multiplication of a self-adjoint element by a skew-adjoint element produces a
skew-adjoint element. -/
/-
**IsSelfAdjoint.smul_mem_skewAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.smul_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A] 
[StarAddMonoid R] [StarAddMonoid A] [StarModule R A] {r : R} (hr : r in skewAdjo
int R) {a : A} (ha : IsSelfAdjoint a) : r • a in skewAdjoint A
参数：hr : r in skewAdjoint R；ha : IsSelfAdjoint a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)

--- 原说明 ---
Scalar multiplication of a self-adjoint element by a skew-adjoint element produc
es a
skew-adjoint element.
-/
theorem IsSelfAdjoint.smul_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A] [StarAddMonoid R]
    [StarAddMonoid A] [StarModule R A] {r : R} (hr : r ∈ skewAdjoint R) {a : A}
    (ha : IsSelfAdjoint a) : r • a ∈ skewAdjoint A :=
  (star_smul _ _).trans <| (congr_arg₂ _ hr ha).trans <| neg_smul _ _

/-- Scalar multiplication of a skew-adjoint element by a skew-adjoint element produces a
self-adjoint element. -/
/-
**isSelfAdjoint_smul_of_mem_skewAdjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSelfAdjoint_smul_of_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R 
A] [StarAddMonoid R] [StarAddMonoid A] [StarModule R A] {r : R} (hr : r in skewA
djoint R) {a : A} (ha : a in skewAdjoint A) : IsSelfAdjoint (r • a)
参数：hr : r in skewAdjoint R；ha : a in skewAdjoint A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `neg_smul_neg`：neg_smul_neg : -r • -x = r • x

--- 原说明 ---
Scalar multiplication of a skew-adjoint element by a skew-adjoint element produc
es a
self-adjoint element.
-/
theorem isSelfAdjoint_smul_of_mem_skewAdjoint [Ring R] [AddCommGroup A] [Module R A]
    [StarAddMonoid R] [StarAddMonoid A] [StarModule R A] {r : R} (hr : r ∈ skewAdjoint R) {a : A}
    (ha : a ∈ skewAdjoint A) : IsSelfAdjoint (r • a) :=
  (star_smul _ _).trans <| (congr_arg₂ _ hr ha).trans <| neg_smul_neg _ _
/-
**IsStarNormal.zero** 是 Mathlib 中的一个定理，位于命名空间 `IsStarNormal`。
形式化陈述：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemiring R] [inst_1 : StarAddMon
oid R], IsStarNormal 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
protected instance IsStarNormal.zero [NonUnitalNonAssocSemiring R]
    [StarAddMonoid R] : IsStarNormal (0 : R) :=
  ⟨by simp only [Commute.refl, star_zero]⟩
/-
**IsStarNormal.one** 是 Mathlib 中的一个定理，位于命名空间 `IsStarNormal`。
形式化陈述：∀ {R : Type u_1} [inst : MulOneClass R] [inst_1 : StarMul R], IsStarNormal
 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
-/
protected instance IsStarNormal.one [MulOneClass R] [StarMul R] : IsStarNormal (1 : R) :=
  ⟨by simp only [Commute.refl, star_one]⟩
/-
**IsStarNormal.star** 是 Mathlib 中的一个定理，位于命名空间 `IsStarNormal`。
形式化陈述：∀ {R : Type u_1} [inst : Mul R] [inst_1 : StarMul R] {x : R} [IsStarNormal
 x], IsStarNormal (star x)
参数：star x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `star_comm_self'`：star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal 
x] : star x * x = x * star x
-/
protected instance IsStarNormal.star [Mul R] [StarMul R] {x : R} [IsStarNormal x] :
    IsStarNormal (star x) :=
  ⟨show star (star x) * star x = star x * star (star x) by rw [star_star, star_comm_self']⟩
/-
**IsStarNormal.neg** 是 Mathlib 中的一个定理，位于命名空间 `IsStarNormal`。
形式化陈述：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] [inst_1 : StarAddMonoid 
R] {x : R} [IsStarNormal x], IsStarNormal (-x)
参数：-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `star_neg`：star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = 
-star r
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `star_comm_self'`：star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal 
x] : star x * x = x * star x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected instance IsStarNormal.neg [NonUnitalNonAssocRing R]
    [StarAddMonoid R] {x : R} [IsStarNormal x] : IsStarNormal (-x) :=
  ⟨show star (-x) * -x = -x * star (-x) by simp_rw [star_neg, neg_mul_neg, star_comm_self']⟩
/-
**IsStarNormal.val_inv** 是 Mathlib 中的一个定理，位于命名空间 `IsStarNormal`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : StarMul R] {x : Rˣ} [IsStarNo
rmal ↑x], IsStarNormal ↑x⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStarNormal.star_comm_self`：∀ {R : Type u_1} {inst : Mul R} {inst_1 : S
tar R} {x : R} [self : IsStarNormal x], Commute (star x) x
-/
protected instance IsStarNormal.val_inv [Monoid R] [StarMul R] {x : Rˣ} [IsStarNormal (x : R)] :
    IsStarNormal (↑x⁻¹ : R) where
  star_comm_self := by simpa [← Units.coe_star_inv, -Commute.units_val_iff] using star_comm_self
/-
**IsStarNormal.map** 是 Mathlib 中的一个定理，位于命名空间 `IsStarNormal`。
形式化陈述：∀ {F : Type u_3} {R : Type u_4} {S : Type u_5} [inst : Mul R] [inst_1 : St
ar R] [inst_2 : Mul S] [inst_3 : Star S]   [inst_4 : FunLike F R S] [MulHomClass
 F R S] [StarHomClass F R S] (f : F) (r : R) [hr : IsStarNormal r],   IsStarNorm
al (f r)
参数：f : F；r : R；f r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `IsStarNormal.star_comm_self`：∀ {R : Type u_1} {inst : Mul R} {inst_1 : S
tar R} {x : R} [self : IsStarNormal x], Commute (star x) x
-/
protected instance IsStarNormal.map {F R S : Type*} [Mul R] [Star R] [Mul S] [Star S]
    [FunLike F R S] [MulHomClass F R S] [StarHomClass F R S] (f : F) (r : R) [hr : IsStarNormal r] :
    IsStarNormal (f r) where
  star_comm_self := by simpa [map_star] using! congr(f $(hr.star_comm_self))
/-
**IsStarNormal.smul** 是 Mathlib 中的一个定理，位于命名空间 `IsStarNormal`。
形式化陈述：∀ {R : Type u_3} {A : Type u_4} [inst : SMul R A] [inst_1 : Star R] [inst_
2 : Star A] [inst_3 : Mul A] [StarModule R A]   [SMulCommClass R A A] [IsScalarT
ower R A A] (r : R) (a : A) [ha : IsStarNormal a], IsStarNormal (r • a)
参数：r : R；a : A；r • a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Commute.smul_right`：Commute.smul_right [Mul α] [SMulCommClass M α α] [Is
ScalarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute a (r • b)
· 使用引理 `Commute.smul_left`：Commute.smul_left [Mul α] [SMulCommClass M α α] [IsSc
alarTower M α α] {a b : α} (h : Commute a b) (r : M) : Commute (r • a) b
· 使用定理 `IsStarNormal.star_comm_self`：∀ {R : Type u_1} {inst : Mul R} {inst_1 : S
tar R} {x : R} [self : IsStarNormal x], Commute (star x) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StarModule.star_smul`：∀ {R : Type u} {A : Type v} {inst : Star R} {inst_
1 : Star A} {inst_2 : SMul R A} [self : StarModule R A] (r : R)   (a : A), star 
(r • a) = …
-/
protected instance IsStarNormal.smul {R A : Type*} [SMul R A] [Star R] [Star A] [Mul A]
    [StarModule R A] [SMulCommClass R A A] [IsScalarTower R A A]
    (r : R) (a : A) [ha : IsStarNormal a] : IsStarNormal (r • a) where
  star_comm_self := star_smul r a ▸ ha.star_comm_self.smul_left (star r) |>.smul_right r

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) TrivialStar.isStarNormal [Mul R] [StarMul R] [TrivialStar R]
    {x : R} : IsStarNormal x :=
  ⟨by rw [star_trivial]⟩

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CommMonoid.isStarNormal [CommMonoid R] [StarMul R] {x : R} :
    IsStarNormal x :=
  ⟨mul_comm _ _⟩
/-
**Commute.isStarNormal_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.isStarNormal_add [NonUnitalNonAssocSemiring R] [StarRing R] {a b :
 R} (hab : Commute a (star b)) [ha : IsStarNormal a] [hb : IsStarNormal b] : IsS
tarNormal (a + b)
参数：hab : Commute a (star b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isStarNormal_iff`：∀ {R : Type u_1} [inst : Mul R] [inst_1 : Star R] (x :
 R), IsStarNormal x ↔ Commute (star x) x
· 使用定理 `Commute.star_star`：∀ {R : Type u} [inst : Mul R] [inst_1 : StarMul R] {x
 y : R}, Commute x y → Commute (star x) (star y)
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
-/
theorem Commute.isStarNormal_add [NonUnitalNonAssocSemiring R] [StarRing R] {a b : R}
    (hab : Commute a (star b)) [ha : IsStarNormal a] [hb : IsStarNormal b] :
    IsStarNormal (a + b) := by
  rw [isStarNormal_iff] at ha hb ⊢
  have := _root_.star_star b ▸ hab.star_star
  simp only [star_add, commute_iff_eq, mul_add, add_mul]
  rw [ha.eq, hb.eq, add_add_add_comm, hab.eq, this.eq]
/-
**Commute.isStarNormal_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.isStarNormal_sub [NonUnitalNonAssocRing R] [StarRing R] {a b : R} 
(hab : Commute a (star b)) [ha : IsStarNormal a] [hb : IsStarNormal b] : IsStarN
ormal (a - b)
参数：hab : Commute a (star b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.isStarNormal_add`：Commute.isStarNormal_add [NonUnitalNonAssocSem
iring R] [StarRing R] {a b : R} (hab : Commute a (star b)) [ha : IsStarNormal a]
 [hb : IsStarN…
· 使用定理 `Commute.neg_right`：neg_right : Commute a b -> Commute a (-b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_neg`：star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = 
-star r
· 使用定理 `IsStarNormal.neg`：∀ {R : Type u_1} [inst : NonUnitalNonAssocRing R] [ins
t_1 : StarAddMonoid R] {x : R} [IsStarNormal x], IsStarNormal (-x)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem Commute.isStarNormal_sub [NonUnitalNonAssocRing R] [StarRing R] {a b : R}
    (hab : Commute a (star b)) [ha : IsStarNormal a] [hb : IsStarNormal b] :
    IsStarNormal (a - b) :=
  sub_eq_add_neg a b ▸ (star_neg b ▸ hab.neg_right).isStarNormal_add
/-
**IsStarNormal.one_add** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsStarNormal.one_add [NonAssocSemiring R] [StarRing R] {a : R} [ha : IsSta
rNormal a] : IsStarNormal (1 + a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.isStarNormal_add`：Commute.isStarNormal_add [NonUnitalNonAssocSem
iring R] [StarRing R] {a b : R} (hab : Commute a (star b)) [ha : IsStarNormal a]
 [hb : IsStarN…
· 使用定理 `Commute.one_left`：one_left (a : M) : Commute 1 a
· 使用定理 `IsStarNormal.one`：∀ {R : Type u_1} [inst : MulOneClass R] [inst_1 : Star
Mul R], IsStarNormal 1
-/
instance IsStarNormal.one_add [NonAssocSemiring R] [StarRing R] {a : R}
    [ha : IsStarNormal a] : IsStarNormal (1 + a) :=
  Commute.one_left (star a) |>.isStarNormal_add
/-
**IsStarNormal.one_sub** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsStarNormal.one_sub [NonAssocRing R] [StarRing R] {a : R} [ha : IsStarNor
mal a] : IsStarNormal (1 - a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.isStarNormal_sub`：Commute.isStarNormal_sub [NonUnitalNonAssocRin
g R] [StarRing R] {a b : R} (hab : Commute a (star b)) [ha : IsStarNormal a] [hb
 : IsStarNorma…
· 使用定理 `Commute.one_left`：one_left (a : M) : Commute 1 a
· 使用定理 `IsStarNormal.one`：∀ {R : Type u_1} [inst : MulOneClass R] [inst_1 : Star
Mul R], IsStarNormal 1
-/
instance IsStarNormal.one_sub [NonAssocRing R] [StarRing R] {a : R}
    [ha : IsStarNormal a] : IsStarNormal (1 - a) :=
  Commute.one_left (star a) |>.isStarNormal_sub
/-
**IsSelfAdjoint.commute_of_mul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.commute_of_mul_eq_zero [NonUnitalNonAssocRing R] [StarRing R
] {a b : R} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) : Co
mmute a b
参数：ha : IsSelfAdjoint a；hb : IsSelfAdjoint b；hab : a * b = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `star_zero`：star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0
-/
lemma IsSelfAdjoint.commute_of_mul_eq_zero [NonUnitalNonAssocRing R] [StarRing R]
    {a b : R} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) :
    Commute a b := by
  have : b * a = 0 := by simpa [ha.star_eq, hb.star_eq] using congr(star $hab)
  grind [commute_iff_eq]

namespace Pi
variable {ι : Type*} {α : ι → Type*} [∀ i, Star (α i)] {f : ∀ i, α i}

/-
**Pi.isSelfAdjoint** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_3} {α : ι → Type u_4} [inst : (i : ι) → Star (α i)] {f : (i 
: ι) → α i},   IsSelfAdjoint f ↔ ∀ (i : ι), IsSelfAdjoint (f i)
参数：i : ι；α i；i : ι；i : ι；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
protected lemma isSelfAdjoint : IsSelfAdjoint f ↔ ∀ i, IsSelfAdjoint (f i) := funext_iff

alias ⟨_root_.IsSelfAdjoint.apply, _⟩ := Pi.isSelfAdjoint

end Pi

