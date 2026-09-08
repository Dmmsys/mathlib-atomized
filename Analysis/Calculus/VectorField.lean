/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Vector fields in vector spaces

We study functions of the form `V : E → E` on a vector space, thinking of these as vector fields.
We define several notions in this context, with the aim to generalize them to vector fields on
manifolds.

Notably, we define the pullback of a vector field under a map, as
`VectorField.pullback 𝕜 f V x := (fderiv 𝕜 f x).inverse (V (f x))` (together with the same notion
within a set).

We also define the Lie bracket of two vector fields as
`VectorField.lieBracket 𝕜 V W x := fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)`
(together with the same notion within a set).

In addition to comprehensive API on these two notions, the main results are the following:
* `VectorField.pullback_lieBracket` states that the pullback of the Lie bracket
  is the Lie bracket of the pullbacks, when the second derivative is symmetric.
* `VectorField.leibniz_identity_lieBracket` is the Leibniz
  identity `[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.

-/

@[expose] public section

open Set
open scoped Topology ContDiff

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W V₁ W₁ : E → E} {s t : Set E} {x : E}

/-!
### The Lie bracket of vector fields in a vector space

We define the Lie bracket of two vector fields, and call it `lieBracket 𝕜 V W x`. We also define
a version localized to sets, `lieBracketWithin 𝕜 V W s x`. We copy the relevant API
of `fderivWithin` and `fderiv` for these notions to get a comprehensive API.
-/

namespace VectorField

variable (𝕜) in
/-- The Lie bracket `[V, W] (x)` of two vector fields at a point, defined as
`DW(x) (V x) - DV(x) (W x)`. -/
/-
**VectorField.lieBracket** 是 Mathlib 中的一个定义，位于命名空间 `VectorField`。
形式化陈述：lieBracket (V W : E -> E) (x : E) : E
参数：V W : E -> E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie bracket `[V, W] (x)` of two vector fields at a point, defined as
`DW(x) (V x) - DV(x) (W x)`.
-/
def lieBracket (V W : E → E) (x : E) : E :=
  fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)

variable (𝕜) in
/-- The Lie bracket `[V, W] (x)` of two vector fields within a set at a point, defined as
`DW(x) (V x) - DV(x) (W x)` where the derivatives are taken inside `s`. -/
/-
**VectorField.lieBracketWithin** 是 Mathlib 中的一个定义，位于命名空间 `VectorField`。
形式化陈述：lieBracketWithin (V W : E -> E) (s : Set E) (x : E) : E
参数：V W : E -> E；s : Set E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie bracket `[V, W] (x)` of two vector fields within a set at a point, defin
ed as
`DW(x) (V x) - DV(x) (W x)` where the derivatives are taken inside `s`.
-/
def lieBracketWithin (V W : E → E) (s : Set E) (x : E) : E :=
  fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x)
/-
**VectorField.lieBracket_eq** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracket_eq : lieBracket 𝕜 V W = fun x => fderiv 𝕜 W x (V x) - fderiv 𝕜 
V x (W x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lieBracket_eq :
    lieBracket 𝕜 V W = fun x ↦ fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x) := rfl
/-
**VectorField.lieBracketWithin_eq** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracketWithin_eq : lieBracketWithin 𝕜 V W s = fun x => fderivWithin 𝕜 W
 s x (V x) - fderivWithin 𝕜 V s x (W x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lieBracketWithin_eq :
    lieBracketWithin 𝕜 V W s =
      fun x ↦ fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x) := rfl

@[simp]
/-
**VectorField.lieBracketWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：lieBracketWithin_univ : lieBracketWithin 𝕜 V W univ = lieBracket 𝕜 V W
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lieBracketWithin_univ : lieBracketWithin 𝕜 V W univ = lieBracket 𝕜 V W := by
  ext1 x
  simp [lieBracketWithin, lieBracket]
/-
**VectorField.lieBracketWithin_eq_zero_of_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Vec
torField`。
形式化陈述：lieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) : lieBra
cketWithin 𝕜 V W s x = 0
参数：hV : V x = 0；hW : W x = 0。
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    lieBracketWithin 𝕜 V W s x = 0 := by
  simp [lieBracketWithin, hV, hW]
/-
**VectorField.lieBracket_eq_zero_of_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `VectorFie
ld`。
形式化陈述：lieBracket_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) : lieBracket 𝕜
 V W x = 0
参数：hV : V x = 0；hW : W x = 0。
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lieBracket_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    lieBracket 𝕜 V W x = 0 := by
  simp [lieBracket, hV, hW]
/-
**VectorField.lieBracketWithin_swap** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracketWithin_swap : lieBracketWithin 𝕜 V W s = - lieBracketWithin 𝕜 W 
V s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lieBracketWithin_swap : lieBracketWithin 𝕜 V W s = - lieBracketWithin 𝕜 W V s := by
  ext x; simp [lieBracketWithin]
/-
**VectorField.lieBracket_swap** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracket_swap : lieBracket 𝕜 V W x = - lieBracket 𝕜 W V x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lieBracket_swap : lieBracket 𝕜 V W x = - lieBracket 𝕜 W V x := by
  simp [lieBracket]
/-
**VectorField.lieBracketWithin_self** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {V : E → E} {s : Set E}, V
ectorField.lieBracketWithin 𝕜 V V s = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lieBracketWithin_self : lieBracketWithin 𝕜 V V s = 0 := by
  ext x; simp [lieBracketWithin]
/-
**VectorField.lieBracket_self** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {V : E → E}, VectorField.l
ieBracket 𝕜 V V = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma lieBracket_self : lieBracket 𝕜 V V = 0 := by
  ext x; simp [lieBracket]
/-
**VectorField.lieBracketWithin_const_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `Vector
Field`。
形式化陈述：lieBracketWithin_const_smul_left {c : 𝕜} (hV : DifferentiableWithinAt 𝕜 V 
s x) (hs : UniqueDiffWithinAt 𝕜 s x) : lieBracketWithin 𝕜 (c • V) W s x = c • li
eBracketWithin 𝕜 V W s x
参数：hV : DifferentiableWithinAt 𝕜 V s x；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `fderivWithin_const_smul`：fderivWithin_const_smul (hxs : UniqueDiffWithin
At 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f s x) (c : R) : fderivWithin 𝕜 (c • f) 
s x = c • fde…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lieBracketWithin_const_smul_left {c : 𝕜} (hV : DifferentiableWithinAt 𝕜 V s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (c • V) W s x =
      c • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hV]
/-
**VectorField.lieBracket_const_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`
。
形式化陈述：lieBracket_const_smul_left {c : 𝕜} (hV : DifferentiableAt 𝕜 V x) : lieBrac
ket 𝕜 (c • V) W x = c • lieBracket 𝕜 V W x
参数：hV : DifferentiableAt 𝕜 V x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.lieBracketWithin_const_smul_left`：lieBracketWithin_const_smu
l_left {c : 𝕜} (hV : DifferentiableWithinAt 𝕜 V s x) (hs : UniqueDiffWithinAt 𝕜 
s x) : lieBracketWithin 𝕜 (c • V) …
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
lemma lieBracket_const_smul_left {c : 𝕜} (hV : DifferentiableAt 𝕜 V x) :
    lieBracket 𝕜 (c • V) W x = c • lieBracket 𝕜 V W x := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hV ⊢
  exact lieBracketWithin_const_smul_left hV uniqueDiffWithinAt_univ
/-
**VectorField.lieBracketWithin_const_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `Vecto
rField`。
形式化陈述：lieBracketWithin_const_smul_right {c : 𝕜} (hW : DifferentiableWithinAt 𝕜 W
 s x) (hs : UniqueDiffWithinAt 𝕜 s x) : lieBracketWithin 𝕜 V (c • W) s x = c • l
ieBracketWithin 𝕜 V W s x
参数：hW : DifferentiableWithinAt 𝕜 W s x；hs : UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `fderivWithin_const_smul`：fderivWithin_const_smul (hxs : UniqueDiffWithin
At 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f s x) (c : R) : fderivWithin 𝕜 (c • f) 
s x = c • fde…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lieBracketWithin_const_smul_right {c : 𝕜} (hW : DifferentiableWithinAt 𝕜 W s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (c • W) s x =
      c • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hW]
/-
**VectorField.lieBracket_const_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField
`。
形式化陈述：lieBracket_const_smul_right {c : 𝕜} (hW : DifferentiableAt 𝕜 W x) : lieBra
cket 𝕜 V (c • W) x = c • lieBracket 𝕜 V W x
参数：hW : DifferentiableAt 𝕜 W x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.lieBracketWithin_const_smul_right`：lieBracketWithin_const_sm
ul_right {c : 𝕜} (hW : DifferentiableWithinAt 𝕜 W s x) (hs : UniqueDiffWithinAt 
𝕜 s x) : lieBracketWithin 𝕜 V (c • …
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
-/
lemma lieBracket_const_smul_right {c : 𝕜} (hW : DifferentiableAt 𝕜 W x) :
    lieBracket 𝕜 V (c • W) x = c • lieBracket 𝕜 V W x := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hW ⊢
  exact lieBracketWithin_const_smul_right hW uniqueDiffWithinAt_univ

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[V, f • W] = (df V) • W + f • [V, W]`
-/
/-
**VectorField.lieBracketWithin_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField
`。
形式化陈述：lieBracketWithin_smul_right {f : E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f 
s x) (hW : DifferentiableWithinAt 𝕜 W s x) (hs : UniqueDiffWithinAt 𝕜 s x) : lie
BracketWithin 𝕜 V (fun y => f y • W y) s x = (fderivWithin 𝕜 f s x) (V x) • (W x
) + (f x) • lieBracketWithin 𝕜 V W s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hW : DifferentiableWithinAt 𝕜 W s x；hs : 
UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `fderivWithin_fun_smul`：fderivWithin_fun_smul (hxs : UniqueDiffWithinAt 𝕜
 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (hf : DifferentiableWithinAt 𝕜 f s x
) : fderivW…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ContinuousLinearMap.instIsSMulApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a funct
ion `f : E → 𝕜`,
we have `[V, f • W] = (df V) • W + f • [V, W]`
-/
lemma lieBracketWithin_smul_right {f : E → 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (fun y ↦ f y • W y) s x =
      (fderivWithin 𝕜 f s x) (V x) • (W x) + (f x) • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, fderivWithin_fun_smul hs hf hW, map_smul, add_comm, smul_sub,
    add_sub_assoc]

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[V, f • W] = (df V) • W + f • [V, W]`
-/
/-
**VectorField.lieBracket_smul_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracket_smul_right {f : E -> 𝕜} (hf : DifferentiableAt 𝕜 f x) (hW : Dif
ferentiableAt 𝕜 W x) : lieBracket 𝕜 V (fun y => f y • W y) x = (fderiv 𝕜 f x) (V
 x) • (W x) + (f x) • lieBracket 𝕜 V W x
参数：hf : DifferentiableAt 𝕜 f x；hW : DifferentiableAt 𝕜 W x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `fderiv_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E : Typ
e u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Topolo
…
· 使用引理 `VectorField.lieBracketWithin_smul_right`：lieBracketWithin_smul_right {f 
: E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x) (hW : DifferentiableWithinAt 𝕜 W
 s x) (hs : UniqueDiffWithinA…
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a funct
ion `f : E → 𝕜`,
we have `[V, f • W] = (df V) • W + f • [V, W]`
-/
lemma lieBracket_smul_right {f : E → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hW : DifferentiableAt 𝕜 W x) :
    lieBracket 𝕜 V (fun y ↦ f y • W y) x =
      (fderiv 𝕜 f x) (V x) • (W x) + (f x) • lieBracket 𝕜 V W x := by
  simp_rw [← differentiableWithinAt_univ, ← lieBracketWithin_univ, fderiv] at hW hf ⊢
  exact lieBracketWithin_smul_right hf hW uniqueDiffWithinAt_univ

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[f • V, W] = - (df W) • V + f • [V, W]`
-/
/-
**VectorField.lieBracketWithin_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`
。
形式化陈述：lieBracketWithin_smul_left {f : E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f s
 x) (hV : DifferentiableWithinAt 𝕜 V s x) (hs : UniqueDiffWithinAt 𝕜 s x) : lieB
racketWithin 𝕜 (fun y => f y • V y) W s x = - (fderivWithin 𝕜 f s x) (W x) • (V 
x) + (f x) • lieBracketWithin 𝕜 V W s x
参数：hf : DifferentiableWithinAt 𝕜 f s x；hV : DifferentiableWithinAt 𝕜 V s x；hs : 
UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.lieBracketWithin_swap`：lieBracketWithin_swap : lieBracketWit
hin 𝕜 V W s = - lieBracketWithin 𝕜 W V s
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用引理 `VectorField.lieBracketWithin_smul_right`：lieBracketWithin_smul_right {f 
: E -> 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x) (hW : DifferentiableWithinAt 𝕜 W
 s x) (hs : UniqueDiffWithinA…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a funct
ion `f : E → 𝕜`,
we have `[f • V, W] = - (df W) • V + f • [V, W]`
-/
lemma lieBracketWithin_smul_left {f : E → 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hV : DifferentiableWithinAt 𝕜 V s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (fun y ↦ f y • V y) W s x =
      - (fderivWithin 𝕜 f s x) (W x) • (V x) + (f x) • lieBracketWithin 𝕜 V W s x := by
  rw [lieBracketWithin_swap, Pi.neg_apply, lieBracketWithin_smul_right hf hV hs,
    lieBracketWithin_swap, add_comm]
  simp

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[f • V, W] = - (df W) • V + f • [V, W]`
-/
/-
**VectorField.lieBracket_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracket_smul_left {f : E -> 𝕜} (hf : DifferentiableAt 𝕜 f x) (hV : Diff
erentiableAt 𝕜 V x) : lieBracket 𝕜 (fun y => f y • V y) W x = - (fderiv 𝕜 f x) (
W x) • (V x) + (f x) • lieBracket 𝕜 V W x
参数：hf : DifferentiableAt 𝕜 f x；hV : DifferentiableAt 𝕜 V x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.lieBracket_swap`：lieBracket_swap : lieBracket 𝕜 V W x = - li
eBracket 𝕜 W V x
· 使用引理 `VectorField.lieBracket_smul_right`：lieBracket_smul_right {f : E -> 𝕜} (h
f : DifferentiableAt 𝕜 f x) (hW : DifferentiableAt 𝕜 W x) : lieBracket 𝕜 V (fun 
y => f y • W y) x = (fd…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a funct
ion `f : E → 𝕜`,
we have `[f • V, W] = - (df W) • V + f • [V, W]`
-/
lemma lieBracket_smul_left {f : E → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hV : DifferentiableAt 𝕜 V x) :
    lieBracket 𝕜 (fun y ↦ f y • V y) W x =
      - (fderiv 𝕜 f x) (W x) • (V x) + (f x) • lieBracket 𝕜 V W x := by
  rw [lieBracket_swap, lieBracket_smul_right hf hV, lieBracket_swap, add_comm]
  simp
/-
**VectorField.lieBracketWithin_add_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracketWithin_add_left (hV : DifferentiableWithinAt 𝕜 V s x) (hV₁ : Dif
ferentiableWithinAt 𝕜 V₁ s x) (hs : UniqueDiffWithinAt 𝕜 s x) : lieBracketWithin
 𝕜 (V + V₁) W s x = lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V₁ W s x
参数：hV : DifferentiableWithinAt 𝕜 V s x；hV₁ : DifferentiableWithinAt 𝕜 V₁ s x；hs 
: UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fderivWithin_add`：fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf 
: DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : fderiv
Within…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `_private.Mathlib.Analysis.Calculus.VectorField.0.VectorField.lieBracketW
ithin_add_left._abel_1_2`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {V W V
₁ : E …
-/
lemma lieBracketWithin_add_left (hV : DifferentiableWithinAt 𝕜 V s x)
    (hV₁ : DifferentiableWithinAt 𝕜 V₁ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (V + V₁) W s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V₁ W s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hV hV₁, add_apply]
  abel
/-
**VectorField.lieBracket_add_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracket_add_left (hV : DifferentiableAt 𝕜 V x) (hV₁ : DifferentiableAt 
𝕜 V₁ x) : lieBracket 𝕜 (V + V₁) W x = lieBracket 𝕜 V W x + lieBracket 𝕜 V₁ W x
参数：hV : DifferentiableAt 𝕜 V x；hV₁ : DifferentiableAt 𝕜 V₁ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fderiv_add`：fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : Differentiabl
eAt 𝕜 g x) : fderiv 𝕜 (f + g) x = fderiv 𝕜 f x + fderiv 𝕜 g x
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `_private.Mathlib.Analysis.Calculus.VectorField.0.VectorField.lieBracket_
add_left._abel_1_2`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {E : Typ
e u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {V W V₁ : E 
…
-/
lemma lieBracket_add_left (hV : DifferentiableAt 𝕜 V x) (hV₁ : DifferentiableAt 𝕜 V₁ x) :
    lieBracket 𝕜 (V + V₁) W x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V₁ W x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hV hV₁, add_apply]
  abel

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
/-
**VectorField.lieBracketWithin_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`
。
形式化陈述：lieBracketWithin_zero_left : lieBracketWithin 𝕜 0 W s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_zero`：fderivWithin_zero : fderivWithin 𝕜 (0 : E -> F) s = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set.
-/
lemma lieBracketWithin_zero_left : lieBracketWithin 𝕜 0 W s = 0 := by ext; simp [lieBracketWithin]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
/-
**VectorField.lieBracketWithin_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField
`。
形式化陈述：lieBracketWithin_zero_right : lieBracketWithin 𝕜 W 0 s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_zero`：fderivWithin_zero : fderivWithin 𝕜 (0 : E -> F) s = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set.
-/
lemma lieBracketWithin_zero_right : lieBracketWithin 𝕜 W 0 s = 0 := by ext; simp [lieBracketWithin]

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
/-
**VectorField.lieBracket_zero_left** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracket_zero_left : lieBracket 𝕜 0 W = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.lieBracketWithin_zero_left`：lieBracketWithin_zero_left : lie
BracketWithin 𝕜 0 W s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable.
-/
lemma lieBracket_zero_left : lieBracket 𝕜 0 W = 0 := by simp [← lieBracketWithin_univ]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
/-
**VectorField.lieBracket_zero_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracket_zero_right : lieBracket 𝕜 W 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `VectorField.lieBracketWithin_zero_right`：lieBracketWithin_zero_right : l
ieBracketWithin 𝕜 W 0 s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable.
-/
lemma lieBracket_zero_right : lieBracket 𝕜 W 0 = 0 := by simp [← lieBracketWithin_univ]
/-
**VectorField.lieBracketWithin_add_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`
。
形式化陈述：lieBracketWithin_add_right (hW : DifferentiableWithinAt 𝕜 W s x) (hW₁ : Di
fferentiableWithinAt 𝕜 W₁ s x) (hs : UniqueDiffWithinAt 𝕜 s x) : lieBracketWithi
n 𝕜 V (W + W₁) s x = lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V W₁ s x
参数：hW : DifferentiableWithinAt 𝕜 W s x；hW₁ : DifferentiableWithinAt 𝕜 W₁ s x；hs 
: UniqueDiffWithinAt 𝕜 s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fderivWithin_add`：fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf 
: DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) : fderiv
Within…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `_private.Mathlib.Analysis.Calculus.VectorField.0.VectorField.lieBracketW
ithin_add_right._abel_1_2`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {
E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {V W 
W₁ : E …
-/
lemma lieBracketWithin_add_right (hW : DifferentiableWithinAt 𝕜 W s x)
    (hW₁ : DifferentiableWithinAt 𝕜 W₁ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (W + W₁) s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V W₁ s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hW hW₁, add_apply]
  abel
/-
**VectorField.lieBracket_add_right** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：lieBracket_add_right (hW : DifferentiableAt 𝕜 W x) (hW₁ : DifferentiableAt
 𝕜 W₁ x) : lieBracket 𝕜 V (W + W₁) x = lieBracket 𝕜 V W x + lieBracket 𝕜 V W₁ x
参数：hW : DifferentiableAt 𝕜 W x；hW₁ : DifferentiableAt 𝕜 W₁ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fderiv_add`：fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : Differentiabl
eAt 𝕜 g x) : fderiv 𝕜 (f + g) x = fderiv 𝕜 f x + fderiv 𝕜 g x
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `_private.Mathlib.Analysis.Calculus.VectorField.0.VectorField.lieBracket_
add_right._abel_1_2`：∀ {𝕜 : Type u_2} [inst : NontriviallyNormedField 𝕜] {E : Ty
pe u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {V W W₁ : E
 …
-/
lemma lieBracket_add_right (hW : DifferentiableAt 𝕜 W x) (hW₁ : DifferentiableAt 𝕜 W₁ x) :
    lieBracket 𝕜 V (W + W₁) x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V W₁ x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hW hW₁, add_apply]
  abel

/-- The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`. -/
/-
**VectorField.fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt** 是 Mathl
ib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt {f : E -> F} (hf 
: ContDiffWithinAt 𝕜 2 f s x) (hsymm : IsSymmSndFDerivWithinAt 𝕜 f s x) (hs : Un
iqueDiffOn 𝕜 s) (hxs : x in s) (hW : DifferentiableWithinAt 𝕜 W s x) (hV : Diffe
rentiableWithinAt 𝕜 V s x) : fderivWithin 𝕜 f s x (lieBracketWithin 𝕜 V W s x) =
 fderivWithin 𝕜 (fun x => fderivWithin 𝕜 f s x (W x)) s x (V x) - fderivWithin 𝕜
 (fun x => fderivWithin 𝕜 f s x (V x)) s x (W x)
参数：hf : ContDiffWithinAt 𝕜 2 f s x；hsymm : IsSymmSndFDerivWithinAt 𝕜 f s x；hs : 
UniqueDiffOn 𝕜 s；hxs : x in s；hW : DifferentiableWithinAt 𝕜 W s x；hV : Different
iableWithinAt 𝕜 V s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `ContDiffWithinAt.fderivWithin_right`：ContDiffWithinAt.fderivWithin_right
 (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (
hx₀s : x₀ in s) : ContDif…
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivWithin_clm_apply`：fderivWithin_clm_apply (hxs : UniqueDiffWithinAt
 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s
 x) : fderiv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`.
-/
lemma fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt {f : E → F}
    (hf : ContDiffWithinAt 𝕜 2 f s x) (hsymm : IsSymmSndFDerivWithinAt 𝕜 f s x)
    (hs : UniqueDiffOn 𝕜 s) (hxs : x ∈ s)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hV : DifferentiableWithinAt 𝕜 V s x) :
    fderivWithin 𝕜 f s x (lieBracketWithin 𝕜 V W s x) =
      fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 f s x (W x)) s x (V x) -
        fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 f s x (V x)) s x (W x) := by
  have H₀ : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f s) s x :=
    (hf.fderivWithin_right hs (by decide) hxs).differentiableWithinAt one_ne_zero
  have H₁ : UniqueDiffWithinAt 𝕜 s x := hs x hxs
  rw [fderivWithin_clm_apply, fderivWithin_clm_apply] <;> try assumption
  simp [lieBracketWithin, hsymm (V _) (W _)]

/-- The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`. -/
/-
**VectorField.fderiv_apply_lieBracket_of_isSymmSndFDerivAt** 是 Mathlib 中的一个引理，位于
命名空间 `VectorField`。
形式化陈述：fderiv_apply_lieBracket_of_isSymmSndFDerivAt {f : E -> F} (hf : ContDiffAt
 𝕜 2 f x) (hsymm : IsSymmSndFDerivAt 𝕜 f x) (hW : DifferentiableAt 𝕜 W x) (hV : 
DifferentiableAt 𝕜 V x) : fderiv 𝕜 f x (lieBracket 𝕜 V W x) = fderiv 𝕜 (fun x =>
 fderiv 𝕜 f x (W x)) x (V x) - fderiv 𝕜 (fun x => fderiv 𝕜 f x (V x)) x (W x)
参数：hf : ContDiffAt 𝕜 2 f x；hsymm : IsSymmSndFDerivAt 𝕜 f x；hW : DifferentiableAt
 𝕜 W x；hV : DifferentiableAt 𝕜 V x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `VectorField.fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt`：fd
erivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt {f : E -> F} (hf : ContDi
ffWithinAt 𝕜 2 f s x) (hsymm : IsSymmSndFDerivWithinAt 𝕜 f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`.
-/
lemma fderiv_apply_lieBracket_of_isSymmSndFDerivAt {f : E → F}
    (hf : ContDiffAt 𝕜 2 f x) (hsymm : IsSymmSndFDerivAt 𝕜 f x)
    (hW : DifferentiableAt 𝕜 W x) (hV : DifferentiableAt 𝕜 V x) :
    fderiv 𝕜 f x (lieBracket 𝕜 V W x) =
      fderiv 𝕜 (fun x ↦ fderiv 𝕜 f x (W x)) x (V x) -
        fderiv 𝕜 (fun x ↦ fderiv 𝕜 f x (V x)) x (W x) := by
  simp only [← fderivWithin_univ, ← lieBracketWithin_univ, ← contDiffWithinAt_univ,
    ← isSymmSndFDerivWithinAt_univ, ← differentiableWithinAt_univ] at *
  exact fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt hf hsymm (by simp) (by simp)
    hW hV

/-- The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`. -/
/-
**VectorField.fderivWithin_apply_lieBracket** 是 Mathlib 中的一个引理，位于命名空间 `VectorFie
ld`。
形式化陈述：fderivWithin_apply_lieBracket {f : E -> F} {n : Nat∞ω} (hf : ContDiffWithi
nAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2 <= n) (hs : UniqueDiffOn 𝕜 s) (hxs' : x i
n closure (interior s)) (hxs : x in s) (hW : DifferentiableWithinAt 𝕜 W s x) (hV
 : DifferentiableWithinAt 𝕜 V s x) : fderivWithin 𝕜 f s x (lieBracketWithin 𝕜 V 
W s x) = fderivWithin 𝕜 (fun x => fderivWithin 𝕜 f s x (W x)) s x (V x) - fderiv
Within 𝕜 (fun x => fderivWithin 𝕜 f s x (V x)) s x (W x)
参数：hf : ContDiffWithinAt 𝕜 n f s x；hn : minSmoothness 𝕜 2 <= n；hs : UniqueDiffOn
 𝕜 s；hxs' : x in closure (interior s)；hxs : x in s；hW : DifferentiableWithinAt 𝕜
 W s x；hV : DifferentiableWithinAt 𝕜 V s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `VectorField.fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt`：fd
erivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt {f : E -> F} (hf : ContDi
ffWithinAt 𝕜 2 f s x) (hsymm : IsSymmSndFDerivWithinAt 𝕜 f…
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `ContDiffWithinAt.isSymmSndFDerivWithinAt`：ContDiffWithinAt.isSymmSndFDer
ivWithinAt {n : Nat∞ω} (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2
 <= n) (hs : UniqueDiffOn 𝕜 s)…

--- 原说明 ---
The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`.
-/
lemma fderivWithin_apply_lieBracket {f : E → F} {n : ℕ∞ω}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hs : UniqueDiffOn 𝕜 s) (hxs' : x ∈ closure (interior s)) (hxs : x ∈ s)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hV : DifferentiableWithinAt 𝕜 V s x) :
    fderivWithin 𝕜 f s x (lieBracketWithin 𝕜 V W s x) =
      fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 f s x (W x)) s x (V x) -
        fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 f s x (V x)) s x (W x) := by
  apply fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt <;> try assumption
  exacts [hf.of_le <| le_minSmoothness.trans hn, hf.isSymmSndFDerivWithinAt hn hs hxs' hxs]

/-- The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`. -/
/-
**VectorField.fderiv_apply_lieBracket** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：fderiv_apply_lieBracket {f : E -> F} {n : Nat∞ω} (hf : ContDiffAt 𝕜 n f x)
 (hn : minSmoothness 𝕜 2 <= n) (hW : DifferentiableAt 𝕜 W x) (hV : Differentiabl
eAt 𝕜 V x) : fderiv 𝕜 f x (lieBracket 𝕜 V W x) = fderiv 𝕜 (fun x => fderiv 𝕜 f x
 (W x)) x (V x) - fderiv 𝕜 (fun x => fderiv 𝕜 f x (V x)) x (W x)
参数：hf : ContDiffAt 𝕜 n f x；hn : minSmoothness 𝕜 2 <= n；hW : DifferentiableAt 𝕜 W
 x；hV : DifferentiableAt 𝕜 V x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `VectorField.fderiv_apply_lieBracket_of_isSymmSndFDerivAt`：fderiv_apply_l
ieBracket_of_isSymmSndFDerivAt {f : E -> F} (hf : ContDiffAt 𝕜 2 f x) (hsymm : I
sSymmSndFDerivAt 𝕜 f x) (hW : DifferentiableAt…
· 使用定理 `ContDiffAt.of_le`：ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m <= 
n) : ContDiffAt 𝕜 m f x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `ContDiffAt.isSymmSndFDerivAt`：ContDiffAt.isSymmSndFDerivAt {n : Nat∞ω} (
hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 <= n) : IsSymmSndFDerivAt 𝕜 f x

--- 原说明 ---
The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`.
-/
lemma fderiv_apply_lieBracket {f : E → F} {n : ℕ∞ω}
    (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hW : DifferentiableAt 𝕜 W x) (hV : DifferentiableAt 𝕜 V x) :
    fderiv 𝕜 f x (lieBracket 𝕜 V W x) =
      fderiv 𝕜 (fun x ↦ fderiv 𝕜 f x (W x)) x (V x) -
        fderiv 𝕜 (fun x ↦ fderiv 𝕜 f x (V x)) x (W x) := by
  apply fderiv_apply_lieBracket_of_isSymmSndFDerivAt <;> try assumption
  exacts [hf.of_le <| le_minSmoothness.trans hn, hf.isSymmSndFDerivAt hn]
/-
**VectorField._root_.ContDiffWithinAt.lieBracketWithin_vectorField** 是 Mathlib 中
的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContDiffWithinAt.lieBracketWithin_vectorField
    {m n : ℕ∞ω} (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 m (lieBracketWithin 𝕜 V W s) s x := by
  apply ContDiffWithinAt.sub
  · exact ContDiffWithinAt.clm_apply (hW.fderivWithin_right hs hmn hx)
      (hV.of_le (le_trans le_self_add hmn))
  · exact ContDiffWithinAt.clm_apply (hV.fderivWithin_right hs hmn hx)
      (hW.of_le (le_trans le_self_add hmn))
/-
**VectorField._root_.ContDiffAt.lieBracket_vectorField** 是 Mathlib 中的一个引理，位于命名空间
 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContDiffAt.lieBracket_vectorField {m n : ℕ∞ω} (hV : ContDiffAt 𝕜 n V x)
    (hW : ContDiffAt 𝕜 n W x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (lieBracket 𝕜 V W) x := by
  rw [← contDiffWithinAt_univ] at hV hW ⊢
  simp_rw [← lieBracketWithin_univ]
  exact hV.lieBracketWithin_vectorField hW uniqueDiffOn_univ hmn (mem_univ _)
/-
**VectorField._root_.ContDiffOn.lieBracketWithin_vectorField** 是 Mathlib 中的一个引理，
位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContDiffOn.lieBracketWithin_vectorField {m n : ℕ∞ω} (hV : ContDiffOn 𝕜 n V s)
    (hW : ContDiffOn 𝕜 n W s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (lieBracketWithin 𝕜 V W s) s :=
  fun x hx ↦ (hV x hx).lieBracketWithin_vectorField (hW x hx) hs hmn hx
/-
**VectorField._root_.ContDiff.lieBracket_vectorField** 是 Mathlib 中的一个引理，位于命名空间 `
VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContDiff.lieBracket_vectorField {m n : ℕ∞ω} (hV : ContDiff 𝕜 n V)
    (hW : ContDiff 𝕜 n W) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m (lieBracket 𝕜 V W) :=
  contDiff_iff_contDiffAt.2 (fun _ ↦ hV.contDiffAt.lieBracket_vectorField hW.contDiffAt hmn)
/-
**VectorField.lieBracketWithin_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `Vect
orField`。
形式化陈述：lieBracketWithin_of_mem_nhdsWithin (st : t in 𝓝[s] x) (hs : UniqueDiffWith
inAt 𝕜 s x) (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜
 W t x) : lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x
参数：st : t in 𝓝[s] x；hs : UniqueDiffWithinAt 𝕜 s x；hV : DifferentiableWithinAt 𝕜 
V t x；hW : DifferentiableWithinAt 𝕜 W t x。
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
· 使用定理 `fderivWithin_of_mem_nhdsWithin`：fderivWithin_of_mem_nhdsWithin [Continuo
usAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
 (st : t in 𝓝[s] x) …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lieBracketWithin_of_mem_nhdsWithin (st : t ∈ 𝓝[s] x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_of_mem_nhdsWithin st hs hV,
    fderivWithin_of_mem_nhdsWithin st hs hW]
/-
**VectorField.lieBracketWithin_subset** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：lieBracketWithin_subset (st : s subseteq t) (ht : UniqueDiffWithinAt 𝕜 s x
) (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) : 
lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x
参数：st : s subseteq t；ht : UniqueDiffWithinAt 𝕜 s x；hV : DifferentiableWithinAt 𝕜
 V t x；hW : DifferentiableWithinAt 𝕜 W t x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorField.lieBracketWithin_of_mem_nhdsWithin`：lieBracketWithin_of_mem_
nhdsWithin (st : t in 𝓝[s] x) (hs : UniqueDiffWithinAt 𝕜 s x) (hV : Differentiab
leWithinAt 𝕜 V t x) (hW : Differenti…
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem lieBracketWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
  lieBracketWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW
/-
**VectorField.lieBracketWithin_inter** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：lieBracketWithin_inter (ht : t in 𝓝 x) : lieBracketWithin 𝕜 V W (s inter t
) x = lieBracketWithin 𝕜 V W s x
参数：ht : t in 𝓝 x。
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
· 使用定理 `fderivWithin_inter`：fderivWithin_inter (ht : t in 𝓝 x) : fderivWithin 𝕜 
f (s inter t) x = fderivWithin 𝕜 f s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lieBracketWithin_inter (ht : t ∈ 𝓝 x) :
    lieBracketWithin 𝕜 V W (s ∩ t) x = lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, fderivWithin_inter, ht]
/-
**VectorField.lieBracketWithin_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `VectorFiel
d`。
形式化陈述：lieBracketWithin_of_mem_nhds (h : s in 𝓝 x) : lieBracketWithin 𝕜 V W s x =
 lieBracket 𝕜 V W x
参数：h : s in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `VectorField.lieBracketWithin_univ`：lieBracketWithin_univ : lieBracketWit
hin 𝕜 V W univ = lieBracket 𝕜 V W
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `VectorField.lieBracketWithin_inter`：lieBracketWithin_inter (ht : t in 𝓝 
x) : lieBracketWithin 𝕜 V W (s inter t) x = lieBracketWithin 𝕜 V W s x
-/
theorem lieBracketWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ, ← univ_inter s, lieBracketWithin_inter h]
/-
**VectorField.lieBracketWithin_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`
。
形式化陈述：lieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x in s) : lieBracketWithi
n 𝕜 V W s x = lieBracket 𝕜 V W x
参数：hs : IsOpen s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorField.lieBracketWithin_of_mem_nhds`：lieBracketWithin_of_mem_nhds (
h : s in 𝓝 x) : lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem lieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x :=
  lieBracketWithin_of_mem_nhds (hs.mem_nhds hx)
/-
**VectorField.lieBracketWithin_eq_lieBracket** 是 Mathlib 中的一个定理，位于命名空间 `VectorFi
eld`。
形式化陈述：lieBracketWithin_eq_lieBracket (hs : UniqueDiffWithinAt 𝕜 s x) (hV : Diffe
rentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) : lieBracketWithin 𝕜 V W s x = 
lieBracket 𝕜 V W x
参数：hs : UniqueDiffWithinAt 𝕜 s x；hV : DifferentiableAt 𝕜 V x；hW : Differentiable
At 𝕜 W x。
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
· 使用定理 `fderivWithin_eq_fderiv`：fderivWithin_eq_fderiv [ContinuousAdd E] [Contin
uousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F] (hs : UniqueDif
fWithinAt 𝕜 …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lieBracketWithin_eq_lieBracket (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x := by
  simp [lieBracketWithin, lieBracket, fderivWithin_eq_fderiv, hs, hV, hW]

/-- Variant of `lieBracketWithin_congr_set` where one requires the sets to coincide only in
the complement of a point. -/
/-
**VectorField.lieBracketWithin_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 `VectorField
`。
形式化陈述：lieBracketWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : lieBracketWi
thin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x
参数：y : E；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
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
· 使用定理 `fderivWithin_congr_set'`：fderivWithin_congr_set' [T1Space E] (y : E) (h 
: s =ᶠ[𝓝[{y}ᶜ] x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Variant of `lieBracketWithin_congr_set` where one requires the sets to coincide 
only in
the complement of a point.
-/
theorem lieBracketWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_congr_set' _ h]
/-
**VectorField.lieBracketWithin_congr_set** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`
。
形式化陈述：lieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) : lieBracketWithin 𝕜 V W s x 
= lieBracketWithin 𝕜 V W t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorField.lieBracketWithin_congr_set'`：lieBracketWithin_congr_set' (y 
: E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V
 W t x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem lieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
  lieBracketWithin_congr_set' x <| h.filter_mono inf_le_left

/-- Variant of `lieBracketWithin_eventually_congr_set` where one requires the sets to coincide only
in the complement of a point. -/
/-
**VectorField.lieBracketWithin_eventually_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 `
VectorField`。
形式化陈述：lieBracketWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : l
ieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t
参数：y : E；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhds_nhdsWithin`：eventually_nhds_nhdsWithin {a : α} {s : Set 
α} {p : α -> Prop} : (forallᶠ y in 𝓝 a, forallᶠ x in 𝓝[s] y, p x) ↔ forallᶠ x in
 𝓝[s] a, p x
· 使用定理 `VectorField.lieBracketWithin_congr_set'`：lieBracketWithin_congr_set' (y 
: E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V
 W t x

--- 原说明 ---
Variant of `lieBracketWithin_eventually_congr_set` where one requires the sets t
o coincide only
in the complement of a point.
-/
theorem lieBracketWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => lieBracketWithin_congr_set' y
/-
**VectorField.lieBracketWithin_eventually_congr_set** 是 Mathlib 中的一个定理，位于命名空间 `V
ectorField`。
形式化陈述：lieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) : lieBracketWithin
 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorField.lieBracketWithin_eventually_congr_set'`：lieBracketWithin_eve
ntually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : lieBracketWithin 𝕜 V W s =ᶠ
[𝓝 x] lieBracketWithin 𝕜 V W t
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem lieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    lieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t :=
  lieBracketWithin_eventually_congr_set' x <| h.filter_mono inf_le_left
/-
**VectorField._root_.DifferentiableWithinAt.lieBracketWithin_congr_mono** 是 Math
lib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.DifferentiableWithinAt.lieBracketWithin_congr_mono
    (hV : DifferentiableWithinAt 𝕜 V s x) (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
    lieBracketWithin 𝕜 V₁ W₁ t x = lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
    hWs, hWx, hxt, h₁]
/-
**VectorField._root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq** 是 Mat
hlib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  simp only [lieBracketWithin, hV.fderivWithin_eq hxV, hW.fderivWithin_eq hxW, hxV, hxW]
/-
**VectorField._root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem*
* 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  hV.lieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

/-- If vector fields coincide on a neighborhood of a point within a set, then the Lie brackets
also coincide on a neighborhood of this point within this set. Version where one considers the Lie
bracket within a subset. -/
/-
**VectorField._root_.Filter.EventuallyEq.lieBracketWithin_vectorField'** 是 Mathl
ib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If vector fields coincide on a neighborhood of a point within a set, then the Li
e brackets
also coincide on a neighborhood of this point within this set. Version where one
 considers the Lie
bracket within a subset.
-/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t ⊆ s) :
    lieBracketWithin 𝕜 V₁ W₁ t =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W t := by
  filter_upwards [hV.fderivWithin' ht (𝕜 := 𝕜), hW.fderivWithin' ht (𝕜 := 𝕜), hV, hW]
    with x hV' hW' hV hW
  simp [lieBracketWithin, hV', hW', hV, hW]
/-
**VectorField._root_.Filter.EventuallyEq.lieBracketWithin_vectorField** 是 Mathli
b 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W s :=
  hV.lieBracketWithin_vectorField' hW Subset.rfl
/-
**VectorField._root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_inse
rt** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_insert
    (hV : V₁ =ᶠ[𝓝[insert x s] x] V) (hW : W₁ =ᶠ[𝓝[insert x s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  apply mem_of_mem_nhdsWithin (mem_insert x s) (hV.lieBracketWithin_vectorField' hW
    (subset_insert x s))
/-
**VectorField._root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_nhds** 
是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).lieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds
/-
**VectorField.lieBracketWithin_congr** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：lieBracketWithin_congr (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁
 W s) (hWx : W₁ x = W x) : lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W
 s x
参数：hV : EqOn V₁ V s；hVx : V₁ x = V x；hW : EqOn W₁ W s；hWx : W₁ x = W x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.lieBracketWithin_vectorField_eq`：∀ {𝕜 : Type u_1} [i
nst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] 
  [inst_2 : NormedSpace 𝕜 E] {V W V₁ W₁ :…
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `Set.EqOn.eventuallyEq`：Set.EqOn.eventuallyEq {α β} {s : Set α} {f g : α 
-> β} (h : EqOn f g s) : f =ᶠ[𝓟 s] g
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem lieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).lieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/-- Version of `lieBracketWithin_congr` in which one assumes that the point belongs to the
given set. -/
/-
**VectorField.lieBracketWithin_congr'** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：lieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x in s
) : lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x
参数：hV : EqOn V₁ V s；hW : EqOn W₁ W s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorField.lieBracketWithin_congr`：lieBracketWithin_congr (hV : EqOn V₁
 V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) : lieBracketWithi
n 𝕜 V₁ W₁ s x = lieBrack…

--- 原说明 ---
Version of `lieBracketWithin_congr` in which one assumes that the point belongs 
to the
given set.
-/
theorem lieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  lieBracketWithin_congr hV (hV hx) hW (hW hx)
/-
**VectorField._root_.Filter.EventuallyEq.lieBracket_vectorField_eq** 是 Mathlib 中
的一个定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.EventuallyEq.lieBracket_vectorField_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracket 𝕜 V₁ W₁ x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ, ← lieBracketWithin_univ, hV.lieBracketWithin_vectorField_eq_nhds hW]
/-
**VectorField._root_.Filter.EventuallyEq.lieBracket_vectorField** 是 Mathlib 中的一个
定理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Filter.EventuallyEq.lieBracket_vectorField
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : lieBracket 𝕜 V₁ W₁ =ᶠ[𝓝 x] lieBracket 𝕜 V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.lieBracket_vectorField_eq hWy

/-- The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`. -/
/-
**VectorField.leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt** 是 M
athlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt {U V W : E ->
 E} {s : Set E} {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hU : ContDiffWith
inAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) (hW : ContDiffWithinAt 𝕜 2 W s
 x) (h'U : IsSymmSndFDerivWithinAt 𝕜 U s x) (h'V : IsSymmSndFDerivWithinAt 𝕜 V s
 x) (h'W : IsSymmSndFDerivWithinAt 𝕜 W s x) : lieBracketWithin 𝕜 U (lieBracketWi
thin 𝕜 V W s) s x = lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x + lieBra
cketWithin 𝕜 V (lieBracket
参数：hs : UniqueDiffOn 𝕜 s；hx : x in s；hU : ContDiffWithinAt 𝕜 2 U s x；hV : ContDi
ffWithinAt 𝕜 2 V s x；hW : ContDiffWithinAt 𝕜 2 W s x；h'U : IsSymmSndFDerivWithin
At 𝕜 U s x；h'V : IsSymmSndFDerivWithinAt 𝕜 V s x；h'W : IsSymmSndFDerivWithinAt 𝕜
 W s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContDiffWithinAt.fderivWithin_right_apply`：ContDiffWithinAt.fderivWithin
_right_apply {f : F -> G} {k : F -> F} {s : Set F} {x₀ : F} (hf : ContDiffWithin
At 𝕜 n f s x₀) (hk : ContDiffWi…
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `fderivWithin_clm_apply`：fderivWithin_clm_apply (hxs : UniqueDiffWithinAt
 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s
 x) : fderiv…
· 使用定理 `ContDiffWithinAt.fderivWithin_right`：ContDiffWithinAt.fderivWithin_right
 (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (
hx₀s : x₀ in s) : ContDif…
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `fderivWithin_fun_sub`：fderivWithin_fun_sub (hxs : UniqueDiffWithinAt 𝕜 s
 x) (hf : DifferentiableWithinAt 𝕜 f s x) (hg : DifferentiableWithinAt 𝕜 g s x) 
: fderivWi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FunLike.coe_sub`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Sub F] [inst_2 : Sub β]   [IsSubApply F α β] (f g : F),
 ⇑(f …
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.
-/
lemma leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt
    {U V W : E → E} {s : Set E} {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x)
    (hW : ContDiffWithinAt 𝕜 2 W s x)
    (h'U : IsSymmSndFDerivWithinAt 𝕜 U s x) (h'V : IsSymmSndFDerivWithinAt 𝕜 V s x)
    (h'W : IsSymmSndFDerivWithinAt 𝕜 W s x) :
    lieBracketWithin 𝕜 U (lieBracketWithin 𝕜 V W s) s x =
      lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x
      + lieBracketWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x := by
  simp only [lieBracketWithin_eq, map_sub]
  have aux₁ {U V : E → E} (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) :
      DifferentiableWithinAt 𝕜 (fun x ↦ (fderivWithin 𝕜 V s x) (U x)) s x :=
    have := hV.fderivWithin_right_apply (hU.of_le one_le_two) hs le_rfl hx
    this.differentiableWithinAt one_ne_zero
  have aux₂ {U V : E → E} (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) :
      fderivWithin 𝕜 (fun y ↦ (fderivWithin 𝕜 U s y) (V y)) s x =
        (fderivWithin 𝕜 U s x).comp (fderivWithin 𝕜 V s x) +
        (fderivWithin 𝕜 (fderivWithin 𝕜 U s) s x).flip (V x) := by
    refine fderivWithin_clm_apply (hs x hx) ?_ (hV.differentiableWithinAt two_ne_zero)
    exact (hU.fderivWithin_right hs le_rfl hx).differentiableWithinAt one_ne_zero
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hV hW) (aux₁ hW hV)]
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hU hV) (aux₁ hV hU)]
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hU hW) (aux₁ hW hU)]
  rw [aux₂ hW hV, aux₂ hV hW, aux₂ hV hU, aux₂ hU hV, aux₂ hW hU, aux₂ hU hW]
  simp only [FunLike.coe_sub, Pi.sub_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, h'V.eq, h'U.eq, h'W.eq]
  abel

/-- The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`. -/
/-
**VectorField.leibniz_identity_lieBracketWithin** 是 Mathlib 中的一个引理，位于命名空间 `Vecto
rField`。
形式化陈述：leibniz_identity_lieBracketWithin (hn : minSmoothness 𝕜 2 <= n) {U V W : E
 -> E} {s : Set E} {x : E} (hs : UniqueDiffOn 𝕜 s) (h'x : x in closure (interior
 s)) (hx : x in s) (hU : ContDiffWithinAt 𝕜 n U s x) (hV : ContDiffWithinAt 𝕜 n 
V s x) (hW : ContDiffWithinAt 𝕜 n W s x) : lieBracketWithin 𝕜 U (lieBracketWithi
n 𝕜 V W s) s x = lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x + lieBracke
tWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x
参数：hn : minSmoothness 𝕜 2 <= n；hs : UniqueDiffOn 𝕜 s；h'x : x in closure (interio
r s)；hx : x in s；hU : ContDiffWithinAt 𝕜 n U s x；hV : ContDiffWithinAt 𝕜 n V s x
；hW : ContDiffWithinAt 𝕜 n W s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `VectorField.leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt
`：leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt {U V W : E -> E} 
{s : Set E} {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hU …
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `ContDiffWithinAt.isSymmSndFDerivWithinAt`：ContDiffWithinAt.isSymmSndFDer
ivWithinAt {n : Nat∞ω} (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2
 <= n) (hs : UniqueDiffOn 𝕜 s)…

--- 原说明 ---
The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.
-/
lemma leibniz_identity_lieBracketWithin (hn : minSmoothness 𝕜 2 ≤ n)
    {U V W : E → E} {s : Set E} {x : E}
    (hs : UniqueDiffOn 𝕜 s) (h'x : x ∈ closure (interior s)) (hx : x ∈ s)
    (hU : ContDiffWithinAt 𝕜 n U s x) (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) :
    lieBracketWithin 𝕜 U (lieBracketWithin 𝕜 V W s) s x =
      lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x
      + lieBracketWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x := by
  apply leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt hs hx
    (hU.of_le (le_minSmoothness.trans hn)) (hV.of_le (le_minSmoothness.trans hn))
    (hW.of_le (le_minSmoothness.trans hn))
  · exact hU.isSymmSndFDerivWithinAt hn hs h'x hx
  · exact hV.isSymmSndFDerivWithinAt hn hs h'x hx
  · exact hW.isSymmSndFDerivWithinAt hn hs h'x hx

/-- The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`. -/
/-
**VectorField.leibniz_identity_lieBracket** 是 Mathlib 中的一个引理，位于命名空间 `VectorField
`。
形式化陈述：leibniz_identity_lieBracket (hn : minSmoothness 𝕜 2 <= n) {U V W : E -> E}
 {x : E} (hU : ContDiffAt 𝕜 n U x) (hV : ContDiffAt 𝕜 n V x) (hW : ContDiffAt 𝕜 
n W x) : lieBracket 𝕜 U (lieBracket 𝕜 V W) x = lieBracket 𝕜 (lieBracket 𝕜 U V) W
 x + lieBracket 𝕜 V (lieBracket 𝕜 U W) x
参数：hn : minSmoothness 𝕜 2 <= n；hU : ContDiffAt 𝕜 n U x；hV : ContDiffAt 𝕜 n V x；h
W : ContDiffAt 𝕜 n W x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.leibniz_identity_lieBracketWithin`：leibniz_identity_lieBrack
etWithin (hn : minSmoothness 𝕜 2 <= n) {U V W : E -> E} {s : Set E} {x : E} (hs 
: UniqueDiffOn 𝕜 s) (h'x : x in clo…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `interior_univ`：interior_univ : interior (univ : Set X) = univ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.
-/
lemma leibniz_identity_lieBracket (hn : minSmoothness 𝕜 2 ≤ n) {U V W : E → E} {x : E}
    (hU : ContDiffAt 𝕜 n U x) (hV : ContDiffAt 𝕜 n V x) (hW : ContDiffAt 𝕜 n W x) :
    lieBracket 𝕜 U (lieBracket 𝕜 V W) x =
      lieBracket 𝕜 (lieBracket 𝕜 U V) W x + lieBracket 𝕜 V (lieBracket 𝕜 U W) x := by
  simp only [← lieBracketWithin_univ, ← contDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_lieBracketWithin hn uniqueDiffOn_univ (by simp) (mem_univ _) hU hV hW


/-!
### The pullback of vector fields in a vector space
-/

variable (𝕜) in
/-- The pullback of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))`. If `Df(x)` is not invertible, we use the junk value `0`.
-/
/-
**VectorField.pullback** 是 Mathlib 中的一个定义，位于命名空间 `VectorField`。
形式化陈述：pullback (f : E -> F) (V : F -> F) (x : E) : E
参数：f : E -> F；V : F -> F；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))`. If `Df(x)` is not invertible, we use th
e junk value `0`.
-/
def pullback (f : E → F) (V : F → F) (x : E) : E := (fderiv 𝕜 f x).inverse (V (f x))

variable (𝕜) in
/-- The pullback within a set of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))` where `Df(x)` is the derivative of `f` within `s`.
If `Df(x)` is not invertible, we use the junk value `0`.
-/
/-
**VectorField.pullbackWithin** 是 Mathlib 中的一个定义，位于命名空间 `VectorField`。
形式化陈述：pullbackWithin (f : E -> F) (V : F -> F) (s : Set E) (x : E) : E
参数：f : E -> F；V : F -> F；s : Set E；x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback within a set of a vector field under a function, defined
as `(f^* V) (x) = Df(x)^{-1} (V (f x))` where `Df(x)` is the derivative of `f` w
ithin `s`.
If `Df(x)` is not invertible, we use the junk value `0`.
-/
def pullbackWithin (f : E → F) (V : F → F) (s : Set E) (x : E) : E :=
  (fderivWithin 𝕜 f s x).inverse (V (f x))
/-
**VectorField.pullbackWithin_eq** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：pullbackWithin_eq {f : E -> F} {V : F -> F} {s : Set E} : pullbackWithin 𝕜
 f V s = fun x => (fderivWithin 𝕜 f s x).inverse (V (f x))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullbackWithin_eq {f : E → F} {V : F → F} {s : Set E} :
    pullbackWithin 𝕜 f V s = fun x ↦ (fderivWithin 𝕜 f s x).inverse (V (f x)) := rfl
/-
**VectorField.pullback_eq_of_fderiv_eq** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：pullback_eq_of_fderiv_eq {f : E -> F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fd
eriv 𝕜 f x) (V : F -> F) : pullback 𝕜 f V x = M.symm (V (f x))
参数：hf : M = fderiv 𝕜 f x；V : F -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullback_eq_of_fderiv_eq
    {f : E → F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderiv 𝕜 f x) (V : F → F) :
    pullback 𝕜 f V x = M.symm (V (f x)) := by
  simp [pullback, ← hf]
/-
**VectorField.pullback_eq_of_not_isInvertible** 是 Mathlib 中的一个引理，位于命名空间 `VectorF
ield`。
形式化陈述：pullback_eq_of_not_isInvertible {f : E -> F} {x : E} (h : ¬(fderiv 𝕜 f x).
IsInvertible) (V : F -> F) : pullback 𝕜 f V x = 0
参数：h : ¬(fderiv 𝕜 f x).IsInvertible；V : F -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_of_not_isInvertible`：∀ {R : Type u_1} {M : T
ype u_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace 
M₂]   [inst_2 : Semiring R] [inst_3 :…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullback_eq_of_not_isInvertible {f : E → F} {x : E}
    (h : ¬(fderiv 𝕜 f x).IsInvertible) (V : F → F) :
    pullback 𝕜 f V x = 0 := by
  simp [pullback, h]
/-
**VectorField.pullbackWithin_eq_of_not_isInvertible** 是 Mathlib 中的一个引理，位于命名空间 `V
ectorField`。
形式化陈述：pullbackWithin_eq_of_not_isInvertible {f : E -> F} {x : E} (h : ¬(fderivWi
thin 𝕜 f s x).IsInvertible) (V : F -> F) : pullbackWithin 𝕜 f V s x = 0
参数：h : ¬(fderivWithin 𝕜 f s x).IsInvertible；V : F -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.inverse_of_not_isInvertible`：∀ {R : Type u_1} {M : T
ype u_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace 
M₂]   [inst_2 : Semiring R] [inst_3 :…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackWithin_eq_of_not_isInvertible {f : E → F} {x : E}
    (h : ¬(fderivWithin 𝕜 f s x).IsInvertible) (V : F → F) :
    pullbackWithin 𝕜 f V s x = 0 := by
  simp [pullbackWithin, h]
/-
**VectorField.pullbackWithin_eq_of_fderivWithin_eq** 是 Mathlib 中的一个引理，位于命名空间 `Ve
ctorField`。
形式化陈述：pullbackWithin_eq_of_fderivWithin_eq {f : E -> F} {M : E ≃L[𝕜] F} {x : E} 
(hf : M = fderivWithin 𝕜 f s x) (V : F -> F) : pullbackWithin 𝕜 f V s x = M.symm
 (V (f x))
参数：hf : M = fderivWithin 𝕜 f s x；V : F -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackWithin_eq_of_fderivWithin_eq
    {f : E → F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderivWithin 𝕜 f s x) (V : F → F) :
    pullbackWithin 𝕜 f V s x = M.symm (V (f x)) := by
  simp [pullbackWithin, ← hf]
/-
**VectorField.pullbackWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 `VectorField`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {f : E → F}   {V : F → F}, Vecto
rField.pullbackWithin 𝕜 f V Set.univ = VectorField.pullback 𝕜 f V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma pullbackWithin_univ {f : E → F} {V : F → F} :
    pullbackWithin 𝕜 f V univ = pullback 𝕜 f V := by
  ext x
  simp [pullbackWithin, pullback]

open scoped Topology Filter
/-
**VectorField.fderiv_pullback** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：fderiv_pullback (f : E -> F) (V : F -> F) (x : E) (h'f : (fderiv 𝕜 f x).Is
Invertible) : fderiv 𝕜 f x (pullback 𝕜 f V x) = V (f x)
参数：f : E -> F；V : F -> F；x : E；h'f : (fderiv 𝕜 f x).IsInvertible。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `VectorField.pullback_eq_of_fderiv_eq`：pullback_eq_of_fderiv_eq {f : E ->
 F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderiv 𝕜 f x) (V : F -> F) : pullback 𝕜 f 
V x = M.symm (V (f x))
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderiv_pullback (f : E → F) (V : F → F) (x : E) (h'f : (fderiv 𝕜 f x).IsInvertible) :
    fderiv 𝕜 f x (pullback 𝕜 f V x) = V (f x) := by
  rcases h'f with ⟨M, hM⟩
  simp [pullback_eq_of_fderiv_eq hM, ← hM]
/-
**VectorField.fderivWithin_pullbackWithin** 是 Mathlib 中的一个引理，位于命名空间 `VectorField
`。
形式化陈述：fderivWithin_pullbackWithin {f : E -> F} {V : F -> F} {x : E} (h'f : (fder
ivWithin 𝕜 f s x).IsInvertible) : fderivWithin 𝕜 f s x (pullbackWithin 𝕜 f V s x
) = V (f x)
参数：h'f : (fderivWithin 𝕜 f s x).IsInvertible。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `VectorField.pullbackWithin_eq_of_fderivWithin_eq`：pullbackWithin_eq_of_f
derivWithin_eq {f : E -> F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderivWithin 𝕜 f s
 x) (V : F -> F) : pullbackWithin 𝕜 f …
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fderivWithin_pullbackWithin {f : E → F} {V : F → F} {x : E}
    (h'f : (fderivWithin 𝕜 f s x).IsInvertible) :
    fderivWithin 𝕜 f s x (pullbackWithin 𝕜 f V s x) = V (f x) := by
  rcases h'f with ⟨M, hM⟩
  simp [pullbackWithin_eq_of_fderivWithin_eq hM, ← hM]

open Set

variable [CompleteSpace E]

/-- If a `C^2` map has an invertible derivative within a set at a point, then nearby derivatives
can be written as continuous linear equivs, which depend in a `C^1` way on the point, as well as
their inverse, and moreover one can compute the derivative of the inverse. -/
/-
**VectorField._root_.exists_continuousLinearEquiv_fderivWithin_symm_eq** 是 Mathl
ib 中的一个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `C^2` map has an invertible derivative within a set at a point, then nearby
 derivatives
can be written as continuous linear equivs, which depend in a `C^1` way on the p
oint, as well as
their inverse, and moreover one can compute the derivative of the inverse.
-/
lemma _root_.exists_continuousLinearEquiv_fderivWithin_symm_eq
    {f : E → F} {s : Set E} {x : E} (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hf : (fderivWithin 𝕜 f s x).IsInvertible) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ∃ N : E → (E ≃L[𝕜] F), ContDiffWithinAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) s x
    ∧ ContDiffWithinAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x
    ∧ (∀ᶠ y in 𝓝[s] x, N y = fderivWithin 𝕜 f s y)
    ∧ ∀ v, fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v
      = - (N x).symm ∘L ((fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x v)) ∘L (N x).symm := by
  classical
  rcases hf with ⟨M, hM⟩
  let U := {y | ∃ (N : E ≃L[𝕜] F), N = fderivWithin 𝕜 f s y}
  have hU : U ∈ 𝓝[s] x := by
    have I : range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (fderivWithin 𝕜 f s x) := by
      rw [← hM]
      exact M.nhds
    have : ContinuousWithinAt (fderivWithin 𝕜 f s) s x :=
      (h'f.fderivWithin_right (m := 1) hs le_rfl hx).continuousWithinAt
    exact this I
  let N : E → (E ≃L[𝕜] F) := fun x ↦ if h : x ∈ U then h.choose else M
  have eN : (fun y ↦ (N y : E →L[𝕜] F)) =ᶠ[𝓝[s] x] fun y ↦ fderivWithin 𝕜 f s y := by
    filter_upwards [hU] with y hy
    simpa only [hy, ↓reduceDIte, N] using Exists.choose_spec hy
  have e'N : N x = fderivWithin 𝕜 f s x := by apply mem_of_mem_nhdsWithin hx eN
  have hN : ContDiffWithinAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) s x := by
    have : ContDiffWithinAt 𝕜 1 (fun y ↦ fderivWithin 𝕜 f s y) s x :=
      h'f.fderivWithin_right (m := 1) hs le_rfl hx
    apply this.congr_of_eventuallyEq eN e'N
  have hN' : ContDiffWithinAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x := by
    have : ContDiffWithinAt 𝕜 1 (ContinuousLinearMap.inverse ∘ (fun y ↦ (N y : E →L[𝕜] F))) s x :=
      (contDiffAt_map_inverse (N x)).comp_contDiffWithinAt x hN
    convert! this with y
    simp only [Function.comp_apply, ContinuousLinearMap.inverse_equiv]
  refine ⟨N, hN, hN', eN, fun v ↦ ?_⟩
  have A' y : ContinuousLinearMap.compL 𝕜 F E F (N y : E →L[𝕜] F) ((N y).symm : F →L[𝕜] E)
      = ContinuousLinearMap.id 𝕜 F := by ext; simp
  have : fderivWithin 𝕜 (fun y ↦ ContinuousLinearMap.compL 𝕜 F E F (N y : E →L[𝕜] F)
      ((N y).symm : F →L[𝕜] E)) s x v = 0 := by
    simp [A', fderivWithin_const_apply]
  have I : (N x : E →L[𝕜] F) ∘L (fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v) =
      - (fderivWithin 𝕜 (fun y ↦ (N y : E →L[𝕜] F)) s x v) ∘L ((N x).symm : F →L[𝕜] E) := by
    rw [ContinuousLinearMap.fderivWithin_of_bilinear _ (hN.differentiableWithinAt one_ne_zero)
      (hN'.differentiableWithinAt one_ne_zero) (hs x hx)] at this
    simpa [eq_neg_iff_add_eq_zero] using this
  have B (M : F →L[𝕜] E) : M = ((N x).symm : F →L[𝕜] E) ∘L ((N x) ∘L M) := by
    ext; simp
  rw [B (fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x v), I]
  simp only [ContinuousLinearMap.comp_neg, eN.fderivWithin_eq e'N]
/-
**VectorField.DifferentiableWithinAt.pullbackWithin** 是 Mathlib 中的一个定理，位于命名空间 `V
ectorField.DifferentiableWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] [CompleteSpace E]   {f : E → F} 
{V : F → F} {s : Set E} {t : Set F} {x : E},   DifferentiableWithinAt 𝕜 V t (f x
) →     ContDiffWithinAt 𝕜 2 f s x →       (fderivWithin 𝕜 f s x).IsInvertible →
         UniqueDiffOn 𝕜 s → x ∈ s → Set.MapsTo f s t → DifferentiableWithinAt 𝕜 
(VectorField.pullbackWithin 𝕜 f V s) s x
参数：f x；fderivWithin 𝕜 f s x；VectorField.pullbackWithin 𝕜 f V s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `exists_continuousLinearEquiv_fderivWithin_symm_eq`：∀ {𝕜 : Type u_1} [ins
t : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `DifferentiableWithinAt.clm_apply`：DifferentiableWithinAt.clm_apply (hc :
 DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) : Differe
ntiableWithinAt 𝕜 (fun…
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `DifferentiableWithinAt.comp`：DifferentiableWithinAt.comp {g : F -> G} {t
 : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt
 𝕜 f s x) (h : Ma…
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `DifferentiableWithinAt.congr_of_eventuallyEq`：DifferentiableWithinAt.con
gr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜 f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (
hx : f₁ x = f x) : DifferentiableW…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.inverse_equiv`：inverse_equiv (e : M ≃L[R] M₂) : inve
rse (e : M ->L[R] M₂) = e.symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
-/
lemma DifferentiableWithinAt.pullbackWithin {f : E → F} {V : F → F} {s : Set E} {t : Set F} {x : E}
    (hV : DifferentiableWithinAt 𝕜 V t (f x))
    (hf : ContDiffWithinAt 𝕜 2 f s x) (hf' : (fderivWithin 𝕜 f s x).IsInvertible)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    DifferentiableWithinAt 𝕜 (pullbackWithin 𝕜 f V s) s x := by
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq hf hf' hs hx
    with ⟨M, -, M_symm_smooth, hM, -⟩
  simp only [pullbackWithin_eq]
  have : DifferentiableWithinAt 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (V (f y))) s x := by
    apply DifferentiableWithinAt.clm_apply
    · exact M_symm_smooth.differentiableWithinAt one_ne_zero
    · exact hV.comp _ (hf.differentiableWithinAt two_ne_zero) hst
  apply this.congr_of_eventuallyEq
  · filter_upwards [hM] with y hy using by simp [← hy]
  · have hMx : M x = fderivWithin 𝕜 f s x := by apply mem_of_mem_nhdsWithin hx hM
    simp [← hMx]

/-- If a `C^2` map has an invertible derivative at a point, then nearby derivatives can be written
as continuous linear equivs, which depend in a `C^1` way on the point, as well as their inverse, and
moreover one can compute the derivative of the inverse. -/
/-
**VectorField._root_.exists_continuousLinearEquiv_fderiv_symm_eq** 是 Mathlib 中的一
个引理，位于命名空间 `VectorField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a `C^2` map has an invertible derivative at a point, then nearby derivatives 
can be written
as continuous linear equivs, which depend in a `C^1` way on the point, as well a
s their inverse, and
moreover one can compute the derivative of the inverse.
-/
lemma _root_.exists_continuousLinearEquiv_fderiv_symm_eq
    {f : E → F} {x : E} (h'f : ContDiffAt 𝕜 2 f x) (hf : (fderiv 𝕜 f x).IsInvertible) :
    ∃ N : E → (E ≃L[𝕜] F), ContDiffAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) x
    ∧ ContDiffAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x
    ∧ (∀ᶠ y in 𝓝 x, N y = fderiv 𝕜 f y)
    ∧ ∀ v, fderiv 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x v
      = - (N x).symm ∘L ((fderiv 𝕜 (fderiv 𝕜 f) x v)) ∘L (N x).symm := by
  simp only [← fderivWithin_univ, ← contDiffWithinAt_univ, ← nhdsWithin_univ] at hf h'f ⊢
  exact exists_continuousLinearEquiv_fderivWithin_symm_eq h'f hf uniqueDiffOn_univ (mem_univ _)

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeomorphism. -/
/-
**VectorField.pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt** 是 Mat
hlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt {f : E -> F} {V
 W : F -> F} {x : E} {t : Set F} (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : C
ontDiffWithinAt 𝕜 2 f s x) (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : Diffe
rentiableWithinAt 𝕜 W t (f x)) (hu : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : Maps
To f s t) : pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x = lieBracketWithin
 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x
参数：hf : IsSymmSndFDerivWithinAt 𝕜 f s x；h'f : ContDiffWithinAt 𝕜 2 f s x；hV : Di
fferentiableWithinAt 𝕜 V t (f x)；hW : DifferentiableWithinAt 𝕜 W t (f x)；hu : Un
iqueDiffOn 𝕜 s；hx : x in s；hst : MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `exists_continuousLinearEquiv_fderivWithin_symm_eq`：∀ {𝕜 : Type u_1} [ins
t : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   
[inst_2 : NormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq_of_mem`：Filter.EventuallyEq.fderivWi
thin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : fderivWithin 𝕜 f₁ s x = fd
erivWithin 𝕜 f s x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `VectorField.pullbackWithin_eq_of_fderivWithin_eq`：pullbackWithin_eq_of_f
derivWithin_eq {f : E -> F} {M : E ≃L[𝕜] F} {x : E} (hf : M = fderivWithin 𝕜 f s
 x) (V : F -> F) : pullbackWithin 𝕜 f …
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `fderivWithin_clm_apply`：fderivWithin_clm_apply (hxs : UniqueDiffWithinAt
 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s
 x) : fderiv…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DifferentiableWithinAt.comp`：DifferentiableWithinAt.comp {g : F -> G} {t
 : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt
 𝕜 f s x) (h : Ma…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `fderivWithin_fun_comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
F : Type u_…
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The Lie bracket commutes with taking pullbacks. This requires the function to ha
ve symmetric
second derivative. Version in a complete space. One could also give a version av
oiding
completeness but requiring that `f` is a local diffeomorphism.
-/
lemma pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
    {f : E → F} {V W : F → F} {x : E} {t : Set F}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x := by
  by_cases h : (fderivWithin 𝕜 f s x).IsInvertible; swap
  · simp [pullbackWithin_eq_of_not_isInvertible h, lieBracketWithin_eq]
  rcases exists_continuousLinearEquiv_fderivWithin_symm_eq h'f h hu hx
    with ⟨M, -, M_symm_smooth, hM, M_diff⟩
  have hMx : M x = fderivWithin 𝕜 f s x := (mem_of_mem_nhdsWithin hx hM :)
  have AV : fderivWithin 𝕜 (pullbackWithin 𝕜 f V s) s x =
      fderivWithin 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (V (f y))) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
    filter_upwards [hM] with y hy using pullbackWithin_eq_of_fderivWithin_eq hy _
  have AW : fderivWithin 𝕜 (pullbackWithin 𝕜 f W s) s x =
      fderivWithin 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (W (f y))) s x := by
    apply Filter.EventuallyEq.fderivWithin_eq_of_mem _ hx
    filter_upwards [hM] with y hy using pullbackWithin_eq_of_fderivWithin_eq hy _
  have Af : DifferentiableWithinAt 𝕜 f s x := h'f.differentiableWithinAt two_ne_zero
  simp only [lieBracketWithin_eq, pullbackWithin_eq_of_fderivWithin_eq hMx, map_sub, AV, AW]
  rw [fderivWithin_clm_apply, fderivWithin_clm_apply]
  · simp [fderivWithin_fun_comp x hW Af hst (hu x hx), ← hMx,
      fderivWithin_fun_comp x hV Af hst (hu x hx), M_diff, hf.eq]
  · exact hu x hx
  · exact M_symm_smooth.differentiableWithinAt one_ne_zero
  · exact hV.comp x Af hst
  · exact hu x hx
  · exact M_symm_smooth.differentiableWithinAt one_ne_zero
  · exact hW.comp x Af hst

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeomorphism. Variant where unique
differentiability and the invariance property are only required in a smaller set `u`. -/
/-
**VectorField.pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_even
tuallyEq** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq
 {f : E -> F} {V W : F -> F} {x : E} {t : Set F} {u : Set E} (hf : IsSymmSndFDer
ivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x) (hV : DifferentiableWithi
nAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x)) (hu : UniqueDiffOn 𝕜 
u) (hx : x in u) (hst : MapsTo f u t) (hus : u =ᶠ[𝓝 x] s) : pullbackWithin 𝕜 f (
lieBracketWithin 𝕜 V W t) s x = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pul
lbackWithin 𝕜 f W s) s x
参数：hf : IsSymmSndFDerivWithinAt 𝕜 f s x；h'f : ContDiffWithinAt 𝕜 2 f s x；hV : Di
fferentiableWithinAt 𝕜 V t (f x)；hW : DifferentiableWithinAt 𝕜 W t (f x)；hu : Un
iqueDiffOn 𝕜 u；hx : x in u；hst : MapsTo f u t；hus : u =ᶠ[𝓝 x] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fderivWithin_congr_set`：fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderi
vWithin 𝕜 f s x = fderivWithin 𝕜 f t x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `VectorField.pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt`：
pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt {f : E -> F} {V W : F
 -> F} {x : E} {t : Set F} (hf : IsSymmSndFDerivWithinAt 𝕜 f…
· 使用定理 `IsSymmSndFDerivWithinAt.congr_set`：IsSymmSndFDerivWithinAt.congr_set (h 
: IsSymmSndFDerivWithinAt 𝕜 f s x) (hst : s =ᶠ[𝓝 x] t) : IsSymmSndFDerivWithinAt
 𝕜 f t x
· 使用定理 `ContDiffWithinAt.congr_set`：ContDiffWithinAt.congr_set (h : ContDiffWith
inAt 𝕜 n f s x) {t : Set E} (hst : s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem`：∀ {𝕜 : Type 
u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGr
oup E]   [inst_2 : NormedSpace 𝕜 E] {V W V₁ W₁ :…
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `fderivWithin_eventually_congr_set`：fderivWithin_eventually_congr_set (h 
: s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `VectorField.lieBracketWithin_congr_set`：lieBracketWithin_congr_set (h : 
s =ᶠ[𝓝 x] t) : lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x

--- 原说明 ---
The Lie bracket commutes with taking pullbacks. This requires the function to ha
ve symmetric
second derivative. Version in a complete space. One could also give a version av
oiding
completeness but requiring that `f` is a local diffeomorphism. Variant where uni
que
differentiability and the invariance property are only required in a smaller set
 `u`.
-/
lemma pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq
    {f : E → F} {V W : F → F} {x : E} {t : Set F} {u : Set E}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 u) (hx : x ∈ u) (hst : MapsTo f u t) (hus : u =ᶠ[𝓝 x] s) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x := calc
  pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
  _ = pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) u x := by
    simp only [pullbackWithin]
    congr 2
    exact fderivWithin_congr_set hus.symm
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V u) (pullbackWithin 𝕜 f W u) u x :=
    pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
      (hf.congr_set hus.symm) (h'f.congr_set hus.symm) hV hW hu hx hst
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) u x := by
    apply Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem _ _ hx
    · apply nhdsWithin_le_nhds
      filter_upwards [fderivWithin_eventually_congr_set (𝕜 := 𝕜) (f := f) hus] with y hy
      simp [pullbackWithin, hy]
    · apply nhdsWithin_le_nhds
      filter_upwards [fderivWithin_eventually_congr_set (𝕜 := 𝕜) (f := f) hus] with y hy
      simp [pullbackWithin, hy]
  _ = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x :=
    lieBracketWithin_congr_set hus

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeomorphism. -/
/-
**VectorField.pullback_lieBracket_of_isSymmSndFDerivAt** 是 Mathlib 中的一个引理，位于命名空间
 `VectorField`。
形式化陈述：pullback_lieBracket_of_isSymmSndFDerivAt {f : E -> F} {V W : F -> F} {x : 
E} (hf : IsSymmSndFDerivAt 𝕜 f x) (h'f : ContDiffAt 𝕜 2 f x) (hV : Differentiabl
eAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x)) : pullback 𝕜 f (lieBracket 𝕜 V 
W) x = lieBracket 𝕜 (pullback 𝕜 f V) (pullback 𝕜 f W) x
参数：hf : IsSymmSndFDerivAt 𝕜 f x；h'f : ContDiffAt 𝕜 2 f x；hV : DifferentiableAt 𝕜
 V (f x)；hW : DifferentiableAt 𝕜 W (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `VectorField.pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt`：
pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt {f : E -> F} {V W : F
 -> F} {x : E} {t : Set F} (hf : IsSymmSndFDerivWithinAt 𝕜 f…
· 使用定理 `uniqueDiffOn_univ`：uniqueDiffOn_univ : UniqueDiffOn 𝕜 (univ : Set E)
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
The Lie bracket commutes with taking pullbacks. This requires the function to ha
ve symmetric
second derivative. Version in a complete space. One could also give a version av
oiding
completeness but requiring that `f` is a local diffeomorphism.
-/
lemma pullback_lieBracket_of_isSymmSndFDerivAt {f : E → F} {V W : F → F} {x : E}
    (hf : IsSymmSndFDerivAt 𝕜 f x) (h'f : ContDiffAt 𝕜 2 f x)
    (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x)) :
    pullback 𝕜 f (lieBracket 𝕜 V W) x = lieBracket 𝕜 (pullback 𝕜 f V) (pullback 𝕜 f W) x := by
  simp only [← lieBracketWithin_univ, ← pullbackWithin_univ, ← isSymmSndFDerivWithinAt_univ,
    ← differentiableWithinAt_univ] at hf h'f hV hW ⊢
  exact pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt hf h'f hV hW uniqueDiffOn_univ
    (mem_univ _) (mapsTo_univ _ _)

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeomorphism. -/
/-
**VectorField.pullbackWithin_lieBracketWithin** 是 Mathlib 中的一个引理，位于命名空间 `VectorF
ield`。
形式化陈述：pullbackWithin_lieBracketWithin {f : E -> F} {V W : F -> F} {x : E} {t : S
et F} (hn : minSmoothness 𝕜 2 <= n) (h'f : ContDiffWithinAt 𝕜 n f s x) (hV : Dif
ferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x)) (hu :
 UniqueDiffOn 𝕜 s) (hx : x in s) (h'x : x in closure (interior s)) (hst : MapsTo
 f s t) : pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x = lieBracketWithin 𝕜
 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x
参数：hn : minSmoothness 𝕜 2 <= n；h'f : ContDiffWithinAt 𝕜 n f s x；hV : Differentia
bleWithinAt 𝕜 V t (f x)；hW : DifferentiableWithinAt 𝕜 W t (f x)；hu : UniqueDiffO
n 𝕜 s；hx : x in s；h'x : x in closure (interior s)；hst : MapsTo f s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `VectorField.pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt`：
pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt {f : E -> F} {V W : F
 -> F} {x : E} {t : Set F} (hf : IsSymmSndFDerivWithinAt 𝕜 f…
· 使用定理 `ContDiffWithinAt.isSymmSndFDerivWithinAt`：ContDiffWithinAt.isSymmSndFDer
ivWithinAt {n : Nat∞ω} (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2
 <= n) (hs : UniqueDiffOn 𝕜 s)…
· 使用定理 `ContDiffWithinAt.of_le`：ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n
 f s x) (hmn : m <= n) : ContDiffWithinAt 𝕜 m f s x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n

--- 原说明 ---
The Lie bracket commutes with taking pullbacks. This requires the function to ha
ve symmetric
second derivative. Version in a complete space. One could also give a version av
oiding
completeness but requiring that `f` is a local diffeomorphism.
-/
lemma pullbackWithin_lieBracketWithin
    {f : E → F} {V W : F → F} {x : E} {t : Set F} (hn : minSmoothness 𝕜 2 ≤ n)
    (h'f : ContDiffWithinAt 𝕜 n f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h'x : x ∈ closure (interior s)) (hst : MapsTo f s t) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      = lieBracketWithin 𝕜 (pullbackWithin 𝕜 f V s) (pullbackWithin 𝕜 f W s) s x :=
  pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
  (h'f.isSymmSndFDerivWithinAt hn hu h'x hx) (h'f.of_le (le_minSmoothness.trans hn)) hV hW hu hx hst

/-- The Lie bracket commutes with taking pullbacks. One could also give a version avoiding
completeness but requiring that `f` is a local diffeomorphism. -/
/-
**VectorField.pullback_lieBracket** 是 Mathlib 中的一个引理，位于命名空间 `VectorField`。
形式化陈述：pullback_lieBracket (hn : minSmoothness 𝕜 2 <= n) {f : E -> F} {V W : F ->
 F} {x : E} (h'f : ContDiffAt 𝕜 n f x) (hV : DifferentiableAt 𝕜 V (f x)) (hW : D
ifferentiableAt 𝕜 W (f x)) : pullback 𝕜 f (lieBracket 𝕜 V W) x = lieBracket 𝕜 (p
ullback 𝕜 f V) (pullback 𝕜 f W) x
参数：hn : minSmoothness 𝕜 2 <= n；h'f : ContDiffAt 𝕜 n f x；hV : DifferentiableAt 𝕜 
V (f x)；hW : DifferentiableAt 𝕜 W (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `VectorField.pullback_lieBracket_of_isSymmSndFDerivAt`：pullback_lieBracke
t_of_isSymmSndFDerivAt {f : E -> F} {V W : F -> F} {x : E} (hf : IsSymmSndFDeriv
At 𝕜 f x) (h'f : ContDiffAt 𝕜 2 f x) (hV :…
· 使用定理 `ContDiffAt.isSymmSndFDerivAt`：ContDiffAt.isSymmSndFDerivAt {n : Nat∞ω} (
hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 <= n) : IsSymmSndFDerivAt 𝕜 f x
· 使用定理 `ContDiffAt.of_le`：ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m <= 
n) : ContDiffAt 𝕜 m f x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n

--- 原说明 ---
The Lie bracket commutes with taking pullbacks. One could also give a version av
oiding
completeness but requiring that `f` is a local diffeomorphism.
-/
lemma pullback_lieBracket (hn : minSmoothness 𝕜 2 ≤ n)
    {f : E → F} {V W : F → F} {x : E} (h'f : ContDiffAt 𝕜 n f x)
    (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x)) :
    pullback 𝕜 f (lieBracket 𝕜 V W) x = lieBracket 𝕜 (pullback 𝕜 f V) (pullback 𝕜 f W) x :=
  pullback_lieBracket_of_isSymmSndFDerivAt (h'f.isSymmSndFDerivAt hn)
    (h'f.of_le (le_minSmoothness.trans hn)) hV hW

end VectorField

