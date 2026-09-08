/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Algebra.Module.LinearMap.Rat
public import Mathlib.Tactic.Module

/-!
# Inner product space derived from a norm

This file defines an `InnerProductSpace` instance from a norm that respects the
parallelogram identity. The parallelogram identity is a way to express the inner product of `x` and
`y` in terms of the norms of `x`, `y`, `x + y`, `x - y`.

## Main results

- `InnerProductSpace.ofNorm`: a normed space whose norm respects the parallelogram identity,
  can be seen as an inner product space.

## Implementation notes

We define `inner_`

$$\langle x, y \rangle := \frac{1}{4} (‖x + y‖^2 - ‖x - y‖^2 + i ‖ix + y‖ ^ 2 - i ‖ix - y‖^2)$$

and use the parallelogram identity

$$‖x + y‖^2 + ‖x - y‖^2 = 2 (‖x‖^2 + ‖y‖^2)$$

to prove it is an inner product, i.e., that it is conjugate-symmetric (`inner_.conj_symm`) and
linear in the first argument. `add_left` is proved by judicious application of the parallelogram
identity followed by tedious arithmetic. `smul_left` is proved step by step, first noting that
$\langle λ x, y \rangle = λ \langle x, y \rangle$ for $λ ∈ ℕ$, $λ = -1$, hence $λ ∈ ℤ$ and $λ ∈ ℚ$
by arithmetic. Then by continuity and the fact that ℚ is dense in ℝ, the same is true for ℝ.
The case of ℂ then follows by applying the result for ℝ and more arithmetic.

## TODO

Move upstream to `Analysis.InnerProductSpace.Basic`.

## References

- [Jordan, P. and von Neumann, J., *On inner products in linear, metric spaces*][Jordan1935]
- https://math.stackexchange.com/questions/21792/norms-induced-by-inner-products-and-the-parallelogram-law
- https://math.dartmouth.edu/archive/m113w10/public_html/jordan-vneumann-thm.pdf

## Tags

inner product space, Hilbert space, norm
-/

@[expose] public section


open RCLike

open scoped ComplexConjugate

variable {𝕜 : Type*} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]

/-- Predicate for the parallelogram identity to hold in a normed group. This is a scalar-less
version of `InnerProductSpace`. If you have an `InnerProductSpaceable` assumption, you can
locally upgrade that to `InnerProductSpace 𝕜 E` using `casesI nonempty_innerProductSpace 𝕜 E`.
-/
/-
**InnerProductSpaceable** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_2) → [NormedAddCommGroup E] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for the parallelogram identity to hold in a normed group. This is a sc
alar-less
version of `InnerProductSpace`. If you have an `InnerProductSpaceable` assumptio
n, you can
locally upgrade that to `InnerProductSpace 𝕜 E` using `casesI nonempty_innerProd
uctSpace 𝕜 E`.
-/
class InnerProductSpaceable : Prop where
  parallelogram_identity :
    ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)

variable (𝕜) {E}
/-
**InnerProductSpace.toInnerProductSpaceable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：InnerProductSpace.toInnerProductSpaceable [InnerProductSpace 𝕜 E] : InnerP
roductSpaceable E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `parallelogram_law_with_norm_mul`：parallelogram_law_with_norm_mul (x y : 
E) : ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)
-/
theorem InnerProductSpace.toInnerProductSpaceable [InnerProductSpace 𝕜 E] :
    InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm_mul 𝕜⟩

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) InnerProductSpace.toInnerProductSpaceable_ofReal
    [InnerProductSpace ℝ E] : InnerProductSpaceable E :=
  ⟨parallelogram_law_with_norm_mul ℝ⟩

variable [NormedSpace 𝕜 E]

local notation "𝓚" => algebraMap ℝ 𝕜

set_option backward.privateInPublic true in
/-- Auxiliary definition of the inner product derived from the norm. -/
/-
**inner_** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition of the inner product derived from the norm.
-/
private noncomputable def inner_ (x y : E) : 𝕜 :=
  4⁻¹ * (𝓚 ‖x + y‖ * 𝓚 ‖x + y‖ - 𝓚 ‖x - y‖ * 𝓚 ‖x - y‖ +
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x + y‖ * 𝓚 ‖(I : 𝕜) • x + y‖ -
    (I : 𝕜) * 𝓚 ‖(I : 𝕜) • x - y‖ * 𝓚 ‖(I : 𝕜) • x - y‖)

namespace InnerProductSpaceable

variable {𝕜} (E)

set_option backward.privateInPublic true in
-- This has a prime added to avoid clashing with public `innerProp`
/-- Auxiliary definition for the `add_left` property. -/
/-
**InnerProductSpaceable.innerProp'** 是 Mathlib 中的一个定义，位于命名空间 `InnerProductSpacea
ble`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the `add_left` property.
-/
private def innerProp' (r : 𝕜) : Prop :=
  ∀ x y : E, inner_ 𝕜 (r • x) y = conj r * inner_ 𝕜 x y

variable {E}

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**InnerProductSpaceable._root_.Continuous.inner_** 是 Mathlib 中的一个定理，位于命名空间 `Inne
rProductSpaceable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.inner_ {f g : ℝ → E} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => inner_ 𝕜 (f x) (g x) := by
  unfold _root_.inner_
  fun_prop

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**InnerProductSpaceable.inner_.norm_sq** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSp
aceable.inner_`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommG
roup E] [inst_2 : NormedSpace 𝕜 E] (x : E),   ‖x‖ ^ 2 = RCLike.re (inner_✝ 𝕜 x x
)
参数：x : E；inner_✝ 𝕜 x x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.mul_re`：mul_re : forall z w : K, re (z * w) = re z * re w - im z 
* im w
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RCLike.inv_re`：inv_re (z : K) : re z⁻¹ = re z / normSq z
· 使用定理 `RCLike.ofNat_re`：ofNat_re (n : Nat) [n.AtLeastTwo] : re (ofNat(n) : K) =
 ofNat(n)
· 使用定理 `RCLike.ofNat_im`：ofNat_im (n : Nat) [n.AtLeastTwo] : im (ofNat(n) : K) =
 0
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `RCLike.ofReal_im`：ofReal_im : forall r : Real, im (r : K) = 0
· 使用定理 `RCLike.I_re`：I_re : re (I : K) = 0
· 使用定理 `RCLike.mul_im`：mul_im : forall z w : K, im (z * w) = re z * im w + im z 
* re w
· 使用定理 `RCLike.inv_im`：inv_im (z : K) : im z⁻¹ = -im z / normSq z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
（共 86 条，此处仅展示前 30 条）
-/
theorem inner_.norm_sq (x : E) : ‖x‖ ^ 2 = re (inner_ 𝕜 x x) := by
  simp only [inner_, normSq_apply, ofNat_re, ofNat_im, map_sub, map_add,
    ofReal_re, ofReal_im, mul_re, inv_re, mul_im, I_re, inv_im]
  have h₁ : ‖x - x‖ = 0 := by simp
  have h₂ : ‖x + x‖ = 2 • ‖x‖ := by convert norm_nsmul 𝕜 2 x; module
  rw [h₁, h₂]
  ring

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**InnerProductSpaceable.inner_.conj_symm** 是 Mathlib 中的一个定理，位于命名空间 `InnerProduct
Spaceable.inner_`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAddCommG
roup E] [inst_2 : NormedSpace 𝕜 E] (x y : E),   (starRingEnd 𝕜) (inner_✝ 𝕜 y x) 
= inner_✝ 𝕜 x y
参数：x y : E；starRingEnd 𝕜；inner_✝ 𝕜 y x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `RCLike.conj_I`：conj_I : conj (I : K) = -I
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `norm_sub_rev`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), 
‖a - b‖ = ‖b - a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RCLike.I_mul_I_of_nonzero`：I_mul_I_of_nonzero : (I : K) != 0 -> (I : K) 
* I = -1
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `RCLike.norm_I_of_ne_zero`：norm_I_of_ne_zero (hI : (I : K) != 0) : ‖(I : 
K)‖ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 107 条，此处仅展示前 30 条）
-/
theorem inner_.conj_symm (x y : E) : conj (inner_ 𝕜 y x) = inner_ 𝕜 x y := by
  simp only [inner_, map_sub, map_add, map_mul, map_inv₀, map_ofNat, conj_ofReal, conj_I]
  rw [add_comm y x, norm_sub_rev]
  by_cases hI : (I : 𝕜) = 0
  · simp only [hI, neg_zero, zero_mul]
  have hI' := I_mul_I_of_nonzero hI
  have I_smul (v : E) : ‖(I : 𝕜) • v‖ = ‖v‖ := by rw [norm_smul, norm_I_of_ne_zero hI, one_mul]
  have h₁ : ‖(I : 𝕜) • y - x‖ = ‖(I : 𝕜) • x + y‖ := by
    convert I_smul ((I : 𝕜) • x + y)
    linear_combination (norm := module) -hI' • x
  have h₂ : ‖(I : 𝕜) • y + x‖ = ‖(I : 𝕜) • x - y‖ := by
    convert (I_smul ((I : 𝕜) • y + x)).symm
    linear_combination (norm := module) -hI' • y
  rw [h₁, h₂]
  ring

variable [InnerProductSpaceable E]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**InnerProductSpaceable.add_left** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpaceabl
e`。
形式化陈述：add_left (x y z : E) : inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z
参数：x y z : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `InnerProductSpaceable.parallelogram_identity`：∀ {E : Type u_2} {inst : N
ormedAddCommGroup E} [self : InnerProductSpaceable E] (x y : E),   ‖x + y‖ * ‖x 
+ y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Abel.unfold_sub`：unfold_sub {α} [SubtractionMonoid α] (a 
b c : α) (h : a + -b = c) : a - b = c
· 使用引理 `Mathlib.Tactic.Abel.subst_into_addg`：subst_into_addg {α} [AddCommGroup α
] (l r tl tr t) (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r 
= t
· 使用定理 `Mathlib.Tactic.Abel.term_atom_pfg`：term_atom_pfg {α} [AddCommGroup α] (x
 x' : α) (h : x = x') : x = termg 1 x' 0
· 使用定理 `Mathlib.Tactic.Abel.term_atomg`：term_atomg {α} [AddCommGroup α] (x : α) 
: x = termg 1 x 0
· 使用定理 `Mathlib.Tactic.Abel.term_add_constg`：term_add_constg {α} [AddCommGroup α
] (n x a k a') (h : a + k = a') : @termg α _ n x a + k = termg n x a'
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Abel.termg_eq`：termg_eq {α : Type*} [AddCommGroup α] (n :
 Int) (x a : α) : termg n x a = n • x + a
· 使用定理 `one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 1 • a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `Mathlib.Tactic.Abel.subst_into_negg`：subst_into_negg {α} [AddCommGroup α
] (a ta t : α) (pra : a = ta) (prt : -ta = t) : -a = t
· 使用定理 `Mathlib.Tactic.Abel.term_neg`：term_neg {α} [AddCommGroup α] (n x a n' a'
) (h₁ : -n = n') (h₂ : -a = a') : -@termg α _ n x a = termg n' x a'
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Mathlib.Tactic.Abel.const_add_termg`：const_add_termg {α} [AddCommGroup α
] (k n x a a') (h : k + a = a') : k + @termg α _ n x a = termg n x a'
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.div_eq_const`：div_eq_const [Div α] (p :
 a = b) (c : α) : a / c = b / c
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Abel.term_add_termg`：term_add_termg {α} [AddCommGroup α] 
(n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') : @termg α _ n₁ x 
a₁ + @termg α _ n₂ x a₂ …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 105 条，此处仅展示前 30 条）
-/
theorem add_left (x y z : E) : inner_ 𝕜 (x + y) z = inner_ 𝕜 x z + inner_ 𝕜 y z := by
  unfold inner_
  have h1 := parallelogram_identity (x + y + z) (x - z)
  have h2 := parallelogram_identity (x + y - z) (x + z)
  have h3 := parallelogram_identity (y + z) z
  have h4 := parallelogram_identity (y - z) z
  have h5 := parallelogram_identity ((I : 𝕜) • (x + y) + z) ((I : 𝕜) • x - z)
  have h6 := parallelogram_identity ((I : 𝕜) • (x + y) - z) ((I : 𝕜) • x + z)
  have h7 := parallelogram_identity ((I : 𝕜) • y + z) z
  have h8 := parallelogram_identity ((I : 𝕜) • y - z) z
  apply_fun 𝓚 at h1 h2 h3 h4 h5 h6 h7 h8
  simp only [map_add, map_mul, map_ofNat, smul_add] at *
  abel_nf at * -- TODO this should be `module_nf` (then the `smul_add` above can go)
  linear_combination (- h1 + h2 + h3 - h4 + I * (- h5 + h6 + h7 - h8)) / 8
/-
**InnerProductSpaceable.rat_prop** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpaceabl
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem rat_prop (r : ℚ) : innerProp' E (r : 𝕜) := by
  intro x y
  let hom : 𝕜 →ₗ[ℚ] 𝕜 := AddMonoidHom.toRatLinearMap <|
    AddMonoidHom.mk' (fun r ↦ inner_ 𝕜 (r • x) y) <| fun a b ↦ by
      simpa [add_smul] using add_left (a • x) (b • x) y
  simpa [hom, Rat.smul_def] using map_smul hom r 1
/-
**InnerProductSpaceable.real_prop** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpaceab
le`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem real_prop (r : ℝ) : innerProp' E (r : 𝕜) := by
  intro x y
  revert r
  rw [← funext_iff]
  refine Rat.isDenseEmbedding_coe_real.dense.equalizer ?_ ?_ (funext fun X => ?_)
  · exact (continuous_ofReal.smul continuous_const).inner_ continuous_const
  · exact (continuous_conj.comp continuous_ofReal).mul continuous_const
  · simp only [Function.comp_apply, RCLike.ofReal_ratCast, rat_prop _ _]
/-
**InnerProductSpaceable.I_prop** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpaceable`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem I_prop : innerProp' E (I : 𝕜) := by
  by_cases hI : (I : 𝕜) = 0
  · rw [hI]
    simpa using real_prop (𝕜 := 𝕜) 0
  intro x y
  have hI' := I_mul_I_of_nonzero hI
  rw [conj_I, inner_, inner_, mul_left_comm, smul_smul, hI', neg_one_smul]
  have h₁ : ‖-x - y‖ = ‖x + y‖ := by rw [← neg_add', norm_neg]
  have h₂ : ‖-x + y‖ = ‖x - y‖ := by rw [← neg_sub, norm_neg, sub_eq_neg_add]
  rw [h₁, h₂]
  linear_combination (- 𝓚 ‖(I : 𝕜) • x - y‖ ^ 2 + 𝓚 ‖(I : 𝕜) • x + y‖ ^ 2) * hI' / 4

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**InnerProductSpaceable.innerProp** 是 Mathlib 中的一个定理，位于命名空间 `InnerProductSpaceab
le`。
形式化陈述：innerProp (r : 𝕜) : innerProp' E r
参数：r : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.re_add_im`：re_add_im (z : K) : (re z : K) + im z * I = z
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `InnerProductSpaceable.add_left`：add_left (x y z : E) : inner_ 𝕜 (x + y) 
z = inner_ 𝕜 x z + inner_ 𝕜 y z
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.OfNorm.0.InnerProductSpaceab
le.real_prop`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : Normed
AddCommGroup E] [inst_2 : NormedSpace 𝕜 E]   [InnerProductSpaceable E] (r …
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.OfNorm.0.InnerProductSpaceab
le.I_prop`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} [inst_1 : NormedAdd
CommGroup E] [inst_2 : NormedSpace 𝕜 E]   [InnerProductSpaceable E], In…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RCLike.conj_ofReal`：conj_ofReal (r : Real) : conj (r : K) = (r : K)
· 使用定理 `RCLike.conj_I`：conj_I : conj (I : K) = -I
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 42 条，此处仅展示前 30 条）
-/
theorem innerProp (r : 𝕜) : innerProp' E r := by
  intro x y
  rw [← re_add_im r, add_smul, add_left, real_prop _ x, ← smul_smul, real_prop _ _ y, I_prop,
    map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  ring

end InnerProductSpaceable

open InnerProductSpaceable

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- **Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies the
parallelogram identity can be given a compatible inner product. -/
@[instance_reducible]
/-
**InnerProductSpace.ofNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：InnerProductSpace.ofNorm (h : forall x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ 
* ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) : InnerProductSpace 𝕜 E
参数：h : forall x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + 
‖y‖ * ‖y‖)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpaceable.inner_.norm_sq`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜]
 {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] (x : 
E),   ‖x‖ ^ 2 = RCLike.re …
· 使用定理 `InnerProductSpaceable.inner_.conj_symm`：∀ {𝕜 : Type u_1} [inst : RCLike 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] (x 
y : E),   (starRingEnd 𝕜) (i…

--- 原说明 ---
**Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies 
the
parallelogram identity can be given a compatible inner product.
-/
noncomputable def InnerProductSpace.ofNorm
    (h : ∀ x y : E, ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖)) :
    InnerProductSpace 𝕜 E :=
  haveI : InnerProductSpaceable E := ⟨h⟩
  { inner := inner_ 𝕜
    norm_sq_eq_re_inner := inner_.norm_sq
    conj_inner_symm := inner_.conj_symm
    add_left := InnerProductSpaceable.add_left
    smul_left := fun _ _ _ => innerProp _ _ _ }

variable (E)
variable [InnerProductSpaceable E]

/-- **Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies the
parallelogram identity can be given a compatible inner product. Do
`casesI nonempty_innerProductSpace 𝕜 E` to locally upgrade `InnerProductSpaceable E` to
`InnerProductSpace 𝕜 E`. -/
/-
**nonempty_innerProductSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_innerProductSpace : Nonempty (InnerProductSpace 𝕜 E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InnerProductSpaceable.inner_.norm_sq`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜]
 {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] (x : 
E),   ‖x‖ ^ 2 = RCLike.re …
· 使用定理 `InnerProductSpaceable.inner_.conj_symm`：∀ {𝕜 : Type u_1} [inst : RCLike 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] (x 
y : E),   (starRingEnd 𝕜) (i…
· 使用定理 `InnerProductSpaceable.add_left`：add_left (x y z : E) : inner_ 𝕜 (x + y) 
z = inner_ 𝕜 x z + inner_ 𝕜 y z
· 使用定理 `InnerProductSpaceable.innerProp`：innerProp (r : 𝕜) : innerProp' E r

--- 原说明 ---
**Fréchet–von Neumann–Jordan Theorem**. A normed space `E` whose norm satisfies 
the
parallelogram identity can be given a compatible inner product. Do
`casesI nonempty_innerProductSpace 𝕜 E` to locally upgrade `InnerProductSpaceabl
e E` to
`InnerProductSpace 𝕜 E`.
-/
theorem nonempty_innerProductSpace : Nonempty (InnerProductSpace 𝕜 E) :=
  ⟨{  inner := inner_ 𝕜
      norm_sq_eq_re_inner := inner_.norm_sq
      conj_inner_symm := inner_.conj_symm
      add_left := add_left
      smul_left := fun _ _ _ => innerProp _ _ _ }⟩

variable {𝕜 E}
variable [NormedSpace ℝ E]

-- TODO: Replace `InnerProductSpace.toUniformConvexSpace`
-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) InnerProductSpaceable.to_uniformConvexSpace : UniformConvexSpace E := by
  cases nonempty_innerProductSpace ℝ E; infer_instance
