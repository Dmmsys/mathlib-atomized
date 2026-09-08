/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Infinitely smooth "bump" functions

A smooth bump function is an infinitely smooth function `f : E → ℝ` supported on a ball
that is equal to `1` on a ball of smaller radius.

These functions have many uses in real analysis. E.g.,

- they can be used to construct a smooth partition of unity which is a very useful tool;
- they can be used to approximate a continuous function by infinitely smooth functions.

There are two classes of spaces where bump functions are guaranteed to exist:
inner product spaces and finite-dimensional spaces.

In this file we define a typeclass `HasContDiffBump`
saying that a normed space has a family of smooth bump functions with certain properties.

We also define a structure `ContDiffBump` that holds the center and radii of the balls from above.
An element `f : ContDiffBump c` can be coerced to a function which is an infinitely smooth function
such that

- `f` is equal to `1` in `Metric.closedBall c f.rIn`;
- `support f = Metric.ball c f.rOut`;
- `0 ≤ f x ≤ 1` for all `x`.

## Main Definitions

- `ContDiffBump (c : E)`: a structure holding data needed to construct
  an infinitely smooth bump function.
- `ContDiffBumpBase (E : Type*)`: a family of infinitely smooth bump functions
  that can be used to construct coercion of a `ContDiffBump (c : E)`
  to a function.
- `HasContDiffBump (E : Type*)`: a typeclass saying that `E` has a `ContDiffBumpBase`.
  Two instances of this typeclass (for inner product spaces and for finite-dimensional spaces)
  are provided elsewhere.

## Keywords

smooth function, smooth bump function
-/

@[expose] public section
noncomputable section

open Function Set Filter
open scoped Topology Filter ContDiff

variable {E X : Type*}

/-- `f : ContDiffBump c`, where `c` is a point in a normed vector space, is a
bundled smooth function such that

- `f` is equal to `1` in `Metric.closedBall c f.rIn`;
- `support f = Metric.ball c f.rOut`;
- `0 ≤ f x ≤ 1` for all `x`.

The structure `ContDiffBump` contains the data required to construct the function:
real numbers `rIn`, `rOut`, and proofs of `0 < rIn < rOut`. The function itself is available through
`CoeFun` when the space is nice enough, i.e., satisfies the `HasContDiffBump` typeclass. -/
/-
**ContDiffBump** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{E : Type u_1} → E → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : ContDiffBump c`, where `c` is a point in a normed vector space, is a
bundled smooth function such that

- `f` is equal to `1` in `Metric.closedBall c f.rIn`;
- `support f = Metric.ball c f.rOut`;
- `0 ≤ f x ≤ 1` for all `x`.

The structure `ContDiffBump` contains the data required to construct the functio
n:
real numbers `rIn`, `rOut`, and proofs of `0 < rIn < rOut`. The function itself 
is available through
`CoeFun` when the space is nice enough, i.e., satisfies the `HasContDiffBump` ty
peclass.
-/
structure ContDiffBump (c : E) where
  /-- real numbers `0 < rIn < rOut` -/
  (rIn rOut : ℝ)
  rIn_pos : 0 < rIn
  rIn_lt_rOut : rIn < rOut

/-- The base function from which one will construct a family of bump functions. One could
add more properties if they are useful and satisfied in the examples of inner product spaces
and finite-dimensional vector spaces, notably derivative norm control in terms of `R - 1`.

TODO: do we ever need `f x = 1 ↔ ‖x‖ ≤ 1`? -/
/-
**ContDiffBumpBase** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_3) → [inst : NormedAddCommGroup E] → [NormedSpace ℝ E] → Type 
u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The base function from which one will construct a family of bump functions. One 
could
add more properties if they are useful and satisfied in the examples of inner pr
oduct spaces
and finite-dimensional vector spaces, notably derivative norm control in terms o
f `R - 1`.

TODO: do we ever need `f x = 1 ↔ ‖x‖ ≤ 1`?
-/
structure ContDiffBumpBase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The function underlying this family of bump functions -/
  toFun : ℝ → E → ℝ
  mem_Icc : ∀ (R : ℝ) (x : E), toFun R x ∈ Icc (0 : ℝ) 1
  symmetric : ∀ (R : ℝ) (x : E), toFun R (-x) = toFun R x
  smooth : ContDiffOn ℝ ∞ (uncurry toFun) (Ioi (1 : ℝ) ×ˢ (univ : Set E))
  eq_one : ∀ R : ℝ, 1 < R → ∀ x : E, ‖x‖ ≤ 1 → toFun R x = 1
  support : ∀ R : ℝ, 1 < R → Function.support (toFun R) = Metric.ball (0 : E) R

/-- A class registering that a real vector space admits bump functions. This will be instantiated
first for inner product spaces, and then for finite-dimensional normed spaces.
We use a specific class instead of `Nonempty (ContDiffBumpBase E)` for performance reasons. -/
/-
**HasContDiffBump** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_3) → [inst : NormedAddCommGroup E] → [NormedSpace ℝ E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class registering that a real vector space admits bump functions. This will be
 instantiated
first for inner product spaces, and then for finite-dimensional normed spaces.
We use a specific class instead of `Nonempty (ContDiffBumpBase E)` for performan
ce reasons.
-/
class HasContDiffBump (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  out : Nonempty (ContDiffBumpBase E)

/-- In a space with `C^∞` bump functions, register some function that will be used as a basis
to construct bump functions of arbitrary size around any point. -/
/-
**someContDiffBumpBase** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：someContDiffBumpBase (E : Type*) [NormedAddCommGroup E] [NormedSpace Real 
E] [hb : HasContDiffBump E] : ContDiffBumpBase E
参数：E : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HasContDiffBump.out`：∀ {E : Type u_3} {inst : NormedAddCommGroup E} {ins
t_1 : NormedSpace ℝ E} [self : HasContDiffBump E],   Nonempty (ContDiffBumpBase 
E)

--- 原说明 ---
In a space with `C^∞` bump functions, register some function that will be used a
s a basis
to construct bump functions of arbitrary size around any point.
-/
def someContDiffBumpBase (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [hb : HasContDiffBump E] : ContDiffBumpBase E :=
  Nonempty.some hb.out

namespace ContDiffBump

/-
**ContDiffBump.rOut_pos** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：rOut_pos {c : E} (f : ContDiffBump c) : 0 < f.rOut
参数：f : ContDiffBump c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `ContDiffBump.rIn_pos`：∀ {E : Type u_1} {c : E} (self : ContDiffBump c), 
0 < self.rIn
· 使用定理 `ContDiffBump.rIn_lt_rOut`：∀ {E : Type u_1} {c : E} (self : ContDiffBump 
c), self.rIn < self.rOut
-/
theorem rOut_pos {c : E} (f : ContDiffBump c) : 0 < f.rOut :=
  f.rIn_pos.trans f.rIn_lt_rOut
/-
**ContDiffBump.one_lt_rOut_div_rIn** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：one_lt_rOut_div_rIn {c : E} (f : ContDiffBump c) : 1 < f.rOut / f.rIn
参数：f : ContDiffBump c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_lt_div`：one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ContDiffBump.rIn_pos`：∀ {E : Type u_1} {c : E} (self : ContDiffBump c), 
0 < self.rIn
· 使用定理 `ContDiffBump.rIn_lt_rOut`：∀ {E : Type u_1} {c : E} (self : ContDiffBump 
c), self.rIn < self.rOut
-/
theorem one_lt_rOut_div_rIn {c : E} (f : ContDiffBump c) : 1 < f.rOut / f.rIn := by
  rw [one_lt_div f.rIn_pos]
  exact f.rIn_lt_rOut
/-
**ContDiffBump.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffBump`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : E) : Inhabited (ContDiffBump c) :=
  ⟨⟨1, 2, zero_lt_one, one_lt_two⟩⟩

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [HasContDiffBump E] {c : E} (f : ContDiffBump c) {x : E} {n : ℕ∞}

/-- The function defined by `f : ContDiffBump c`. Use automatic coercion to
function instead. -/
/-
**ContDiffBump.toFun** 是 Mathlib 中的一个定义，位于命名空间 `ContDiffBump`。
形式化陈述：{E : Type u_1} →   [inst : NormedAddCommGroup E] → [inst_1 : NormedSpace ℝ
 E] → [HasContDiffBump E] → {c : E} → ContDiffBump c → E → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function defined by `f : ContDiffBump c`. Use automatic coercion to
function instead.
-/
@[coe] def toFun {c : E} (f : ContDiffBump c) : E → ℝ :=
  (someContDiffBumpBase E).toFun (f.rOut / f.rIn) ∘ fun x ↦ (f.rIn⁻¹ • (x - c))
/-
**ContDiffBump.** 是 Mathlib 中的一个实例，位于命名空间 `ContDiffBump`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (ContDiffBump c) fun _ => E → ℝ :=
  ⟨toFun⟩
/-
**ContDiffBump.apply** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffBump c) (x : E), ↑f x = (som
eContDiffBumpBase E).toFun (f.rOut / f.rIn) (f.rIn⁻¹ • (x - c))
参数：f : ContDiffBump c；x : E；someContDiffBumpBase E；f.rOut / f.rIn；f.rIn⁻¹ • (x -
 c)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem apply (x : E) :
    f x = (someContDiffBumpBase E).toFun (f.rOut / f.rIn) (f.rIn⁻¹ • (x - c)) :=
  rfl
/-
**ContDiffBump.sub** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffBump c) (x : E), ↑f (c - x) 
= ↑f (c + x)
参数：f : ContDiffBump c；x : E；c - x；c + x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - b - a = -b
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `ContDiffBumpBase.symmetric`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : NormedSpace ℝ E] (self : ContDiffBumpBase E) (R : ℝ) (x : E),   sel
f.toFun R (-x) =…
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem sub (x : E) : f (c - x) = f (c + x) := by
  simp [f.apply, ContDiffBumpBase.symmetric]
/-
**ContDiffBump.neg** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : HasContDiffBump E]   (f : ContDiffBump 0) (x : E), ↑f (-x) = ↑f x
参数：f : ContDiffBump 0；x : E；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffBump.toFun.congr_simp`：∀ {E : Type u_1} [inst : NormedAddCommGro
up E] [inst_1 : NormedSpace ℝ E] [inst_2 : HasContDiffBump E] {c : E}   (f f_1 :
 ContDiffBump c), f…
· 使用定理 `ContDiffBump.sub`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1
 : NormedSpace ℝ E] [inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffBump c) 
(x : E…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem neg (f : ContDiffBump (0 : E)) (x : E) : f (-x) = f x := by
  simp_rw [← zero_sub, f.sub, zero_add]

open Metric
/-
**ContDiffBump.one_of_mem_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：one_of_mem_closedBall (hx : x in closedBall c f.rIn) : f x = 1
参数：hx : x in closedBall c f.rIn。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffBumpBase.eq_one`：∀ {E : Type u_3} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] (self : ContDiffBumpBase E) (R : ℝ),   1 < R → ∀ (x :
 E), ‖x‖ ≤ 1 …
· 使用定理 `ContDiffBump.one_lt_rOut_div_rIn`：one_lt_rOut_div_rIn {c : E} (f : ContD
iffBump c) : 1 < f.rOut / f.rIn
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ContDiffBump.rIn_pos`：∀ {E : Type u_1} {c : E} (self : ContDiffBump c), 
0 < self.rIn
· 使用定理 `div_le_one`：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closedBall_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup
 E] {a b : E} {r : ℝ}, b ∈ Metric.closedBall a r ↔ ‖b - a‖ ≤ r
-/
theorem one_of_mem_closedBall (hx : x ∈ closedBall c f.rIn) : f x = 1 := by
  apply ContDiffBumpBase.eq_one _ _ f.one_lt_rOut_div_rIn
  simpa only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg f.rIn_pos.le, ← div_eq_inv_mul,
    div_le_one f.rIn_pos] using mem_closedBall_iff_norm.1 hx
/-
**ContDiffBump.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：nonneg : 0 <= f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContDiffBumpBase.mem_Icc`：∀ {E : Type u_3} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] (self : ContDiffBumpBase E) (R : ℝ) (x : E),   self.
toFun R x ∈ Se…
-/
theorem nonneg : 0 ≤ f x :=
  (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).1

/-- A version of `ContDiffBump.nonneg` with `x` explicit -/
/-
**ContDiffBump.nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：nonneg' (x : E) : 0 <= f x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffBump.nonneg`：nonneg : 0 <= f x

--- 原说明 ---
A version of `ContDiffBump.nonneg` with `x` explicit
-/
theorem nonneg' (x : E) : 0 ≤ f x := f.nonneg
/-
**ContDiffBump.le_one** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：le_one : f x <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContDiffBumpBase.mem_Icc`：∀ {E : Type u_3} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] (self : ContDiffBumpBase E) (R : ℝ) (x : E),   self.
toFun R x ∈ Se…
-/
theorem le_one : f x ≤ 1 :=
  (ContDiffBumpBase.mem_Icc (someContDiffBumpBase E) _ _).2
/-
**ContDiffBump.support_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：support_eq : Function.support f = Metric.ball c f.rOut
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffBumpBase.support`：∀ {E : Type u_3} [inst : NormedAddCommGroup E]
 [inst_1 : NormedSpace ℝ E] (self : ContDiffBumpBase E) (R : ℝ),   1 < R → Funct
ion.support (s…
· 使用定理 `ContDiffBump.one_lt_rOut_div_rIn`：one_lt_rOut_div_rIn {c : E} (f : ContD
iffBump c) : 1 < f.rOut / f.rIn
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `abs_inv`：abs_inv (a : α) : |a⁻¹| = |a|⁻¹
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ContDiffBump.rIn_pos`：∀ {E : Type u_1} {c : E} (self : ContDiffBump c), 
0 < self.rIn
· 使用引理 `div_lt_div_iff_of_pos_right`：div_lt_div_iff_of_pos_right (hc : 0 < c) : 
a / c < b / c ↔ a < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_eq : Function.support f = Metric.ball c f.rOut := by
  simp only [toFun, support_comp_eq_preimage, ContDiffBumpBase.support _ _ f.one_lt_rOut_div_rIn]
  ext x
  simp only [mem_ball_iff_norm, sub_zero, norm_smul, mem_preimage, Real.norm_eq_abs, abs_inv,
    abs_of_pos f.rIn_pos, ← div_eq_inv_mul, div_lt_div_iff_of_pos_right f.rIn_pos]
/-
**ContDiffBump.tsupport_eq** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：tsupport_eq : tsupport f = closedBall c f.rOut
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffBump.support_eq`：support_eq : Function.support f = Metric.ball c
 f.rOut
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ContDiffBump.rOut_pos`：rOut_pos {c : E} (f : ContDiffBump c) : 0 < f.rOu
t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tsupport_eq : tsupport f = closedBall c f.rOut := by
  simp_rw [tsupport, f.support_eq, closure_ball _ f.rOut_pos.ne']
/-
**ContDiffBump.pos_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：pos_of_mem_ball (hx : x in ball c f.rOut) : 0 < f x
参数：hx : x in ball c f.rOut。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `ContDiffBump.nonneg`：nonneg : 0 <= f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContDiffBump.support_eq`：support_eq : Function.support f = Metric.ball c
 f.rOut
-/
theorem pos_of_mem_ball (hx : x ∈ ball c f.rOut) : 0 < f x :=
  f.nonneg.lt_of_ne' <| by rwa [← support_eq, mem_support] at hx
/-
**ContDiffBump.zero_of_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：zero_of_le_dist (hx : f.rOut <= dist x c) : f x = 0
参数：hx : f.rOut <= dist x c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
· 使用定理 `ContDiffBump.support_eq`：support_eq : Function.support f = Metric.ball c
 f.rOut
· 使用定理 `Metric.mem_ball`：mem_ball : y in ball x ε ↔ dist y x < ε
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem zero_of_le_dist (hx : f.rOut ≤ dist x c) : f x = 0 := by
  rwa [← notMem_support, support_eq, mem_ball, not_lt]
/-
**ContDiffBump.hasCompactSupport** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffBump c) [FiniteDimensional ℝ
 E], HasCompactSupport ↑f
参数：f : ContDiffBump c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContDiffBump.tsupport_eq`：tsupport_eq : tsupport f = closedBall c f.rOut
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
-/
protected theorem hasCompactSupport [FiniteDimensional ℝ E] : HasCompactSupport f := by
  simp_rw [HasCompactSupport, f.tsupport_eq, isCompact_closedBall]
/-
**ContDiffBump.eventuallyEq_one_of_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffB
ump`。
形式化陈述：eventuallyEq_one_of_mem_ball (h : x in ball c f.rIn) : f =ᶠ[𝓝 x] 1
参数：h : x in ball c f.rIn。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Metric.closedBall_mem_nhds_of_mem`：closedBall_mem_nhds_of_mem {x c : α} 
{ε : Real} (h : x in ball c ε) : closedBall c ε in 𝓝 x
· 使用定理 `ContDiffBump.one_of_mem_closedBall`：one_of_mem_closedBall (hx : x in clo
sedBall c f.rIn) : f x = 1
-/
theorem eventuallyEq_one_of_mem_ball (h : x ∈ ball c f.rIn) : f =ᶠ[𝓝 x] 1 :=
  mem_of_superset (closedBall_mem_nhds_of_mem h) fun _ ↦ f.one_of_mem_closedBall
/-
**ContDiffBump.eventuallyEq_one** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：eventuallyEq_one : f =ᶠ[𝓝 c] 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffBump.eventuallyEq_one_of_mem_ball`：eventuallyEq_one_of_mem_ball 
(h : x in ball c f.rIn) : f =ᶠ[𝓝 x] 1
· 使用定理 `Metric.mem_ball_self`：mem_ball_self (h : 0 < ε) : x in ball x ε
· 使用定理 `ContDiffBump.rIn_pos`：∀ {E : Type u_1} {c : E} (self : ContDiffBump c), 
0 < self.rIn
-/
theorem eventuallyEq_one : f =ᶠ[𝓝 c] 1 :=
  f.eventuallyEq_one_of_mem_ball (mem_ball_self f.rIn_pos)

/-- `ContDiffBump` is `𝒞ⁿ` in all its arguments. -/
/-
**ContDiffBump._root_.ContDiffWithinAt.contDiffBump** 是 Mathlib 中的一个定理，位于命名空间 `C
ontDiffBump`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ContDiffBump` is `𝒞ⁿ` in all its arguments.
-/
protected theorem _root_.ContDiffWithinAt.contDiffBump {c g : X → E} {s : Set X}
    {f : ∀ x, ContDiffBump (c x)} {x : X} (hc : ContDiffWithinAt ℝ n c s x)
    (hr : ContDiffWithinAt ℝ n (fun x => (f x).rIn) s x)
    (hR : ContDiffWithinAt ℝ n (fun x => (f x).rOut) s x)
    (hg : ContDiffWithinAt ℝ n g s x) :
    ContDiffWithinAt ℝ n (fun x => f x (g x)) s x := by
  change ContDiffWithinAt ℝ n (uncurry (someContDiffBumpBase E).toFun ∘ fun x : X =>
    ((f x).rOut / (f x).rIn, (f x).rIn⁻¹ • (g x - c x))) s x
  refine (((someContDiffBumpBase E).smooth.contDiffAt ?_).of_le
    (mod_cast le_top)).comp_contDiffWithinAt x ?_
  · exact prod_mem_nhds (Ioi_mem_nhds (f x).one_lt_rOut_div_rIn) univ_mem
  · exact (hR.div hr (f x).rIn_pos.ne').prodMk ((hr.inv (f x).rIn_pos.ne').smul (hg.sub hc))

/-- `ContDiffBump` is `𝒞ⁿ` in all its arguments. -/
protected nonrec theorem _root_.ContDiffAt.contDiffBump {c g : X → E} {f : ∀ x, ContDiffBump (c x)}
    {x : X} (hc : ContDiffAt ℝ n c x) (hr : ContDiffAt ℝ n (fun x => (f x).rIn) x)
    (hR : ContDiffAt ℝ n (fun x => (f x).rOut) x) (hg : ContDiffAt ℝ n g x) :
    ContDiffAt ℝ n (fun x => f x (g x)) x :=
  hc.contDiffBump hr hR hg

/-
**ContDiffBump._root_.ContDiff.contDiffBump** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffB
ump`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContDiff.contDiffBump {c g : X → E} {f : ∀ x, ContDiffBump (c x)}
    (hc : ContDiff ℝ n c) (hr : ContDiff ℝ n fun x => (f x).rIn)
    (hR : ContDiff ℝ n fun x => (f x).rOut) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n fun x => f x (g x) := by
  rw [contDiff_iff_contDiffAt] at *
  exact fun x => (hc x).contDiffBump (hr x) (hR x) (hg x)
/-
**ContDiffBump.contDiff** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffBump c) {n : ℕ∞}, ContDiff ℝ
 ↑n ↑f
参数：f : ContDiffBump c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffBump`：∀ {E : Type u_1} {X : Type u_2} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup X]   [inst_
3 : NormedS…
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
-/
protected theorem contDiff : ContDiff ℝ n f :=
  contDiff_const.contDiffBump contDiff_const contDiff_const contDiff_id
/-
**ContDiffBump.contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffBump c) {x : E} {n : ℕ∞}, Co
ntDiffAt ℝ (↑n) (↑f) x
参数：f : ContDiffBump c；↑n；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `ContDiffBump.contDiff`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [i
nst_1 : NormedSpace ℝ E] [inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffBum
p c) {n : ℕ…
-/
protected theorem contDiffAt : ContDiffAt ℝ n f x :=
  f.contDiff.contDiffAt
/-
**ContDiffBump.contDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffBump c) {x : E} {n : ℕ∞} {s 
: Set E}, ContDiffWithinAt ℝ (↑n) (↑f) s x
参数：f : ContDiffBump c；↑n；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `ContDiffBump.contDiffAt`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℝ E] [inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffB
ump c) {x : E…
-/
protected theorem contDiffWithinAt {s : Set E} : ContDiffWithinAt ℝ n f s x :=
  f.contDiffAt.contDiffWithinAt
/-
**ContDiffBump.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffBump`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
[inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffBump c), Continuous ↑f
参数：f : ContDiffBump c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_zero`：contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f
· 使用定理 `ContDiffBump.contDiff`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [i
nst_1 : NormedSpace ℝ E] [inst_2 : HasContDiffBump E] {c : E}   (f : ContDiffBum
p c) {n : ℕ…
-/
protected theorem continuous : Continuous f :=
  contDiff_zero.mp f.contDiff

end ContDiffBump

