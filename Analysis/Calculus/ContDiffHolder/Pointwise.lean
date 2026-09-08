/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.MetricSpace.Holder

/-!
# Continuously `k` times differentiable functions with pointwise Hölder continuous derivatives

We say that a function is of class $C^{k+(α)}$ at a point `a`,
where `k` is a natural number and `0 ≤ α ≤ 1`, if

- it is of class $C^k$ at `a` in the sense of `ContDiffAt`;
- its `k`th derivative satisfies $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`.

Note that the Hölder condition used in this definition fixes one of the points at `a`.
In different sources, it is called *pointwise*, *local*, or *weak* Hölder condition,
though the term "local" may also mean a stronger condition
saying that a function is Hölder continuous on a neighborhood of `a`.

The immediate reason for adding this definition to the library
is its use in [Moreira2001], where Moreira proves a version of the Morse-Sard theorem
for functions that satisfy this condition on their critical set.

In this file, we define `ContDiffPointwiseHolderAt` to be the predicate
saying that a function is $C^{k+(α)}$ in the sense described above
and prove basic properties of this predicate.

## Implementation notes

In Moreira's paper, `k` is assumed to be a strictly positive number.
We define the predicate for any `k : ℕ`, then assume `k ≠ 0` whenever it is necessary.
-/

public section

open scoped unitInterval Topology NNReal
open Asymptotics Filter Set

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k l m : ℕ} {α β : I} {f : E → F} {a : E}

/-- A map `f` is said to be $C^{k+(α)}$ at `a`, where `k` is a natural number and `0 ≤ α ≤ 1`,
if it is $C^k$ at this point and $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`.

When naming lemmas about this predicate, `k` is called "order", and `α` is called "exponent". -/
@[mk_iff]
/-
**ContDiffPointwiseHolderAt** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{E : Type u_1} →   {F : Type u_2} →     [inst : NormedAddCommGroup E] →   
    [NormedSpace ℝ E] → [inst : NormedAddCommGroup F] → [NormedSpace ℝ F] → ℕ → 
↑unitInterval → (E → F) → E → Prop
参数：E → F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f` is said to be $C^{k+(α)}$ at `a`, where `k` is a natural number and `0
 ≤ α ≤ 1`,
if it is $C^k$ at this point and $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`.

When naming lemmas about this predicate, `k` is called "order", and `α` is calle
d "exponent".
-/
structure ContDiffPointwiseHolderAt (k : ℕ) (α : I) (f : E → F) (a : E) : Prop where
  /-- A $C^{k+(α)}$ map is a $C^k$ map. -/
  contDiffAt : ContDiffAt ℝ k f a
  /-- A $C^{k+(α)}$ map satisfies $D^kf(x)-D^kf(a) = O(‖x - a‖ ^ α)$ as `x → a`. -/
  isBigO : (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ))

/-- A $C^n$ map is a $C^{k+(α)}$ map for any `k < n`. -/
/-
**ContDiffAt.contDiffPointwiseHolderAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.contDiffPointwiseHolderAt {n : WithTop Nat∞} (h : ContDiffAt Re
al n f a) (hk : k < n) (α : I) : ContDiffPointwiseHolderAt k α f a where contDif
fAt
参数：h : ContDiffAt Real n f a；hk : k < n；α : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.of_le`：ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m <= 
n) : ContDiffAt 𝕜 m f x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `DifferentiableAt.isBigO_sub`：DifferentiableAt.isBigO_sub (h : Differenti
ableAt 𝕜 f x₀) : (f · - f x₀) =O[𝓝 x₀] (· - x₀)
· 使用定理 `ContDiffAt.differentiableAt_iteratedFDeriv`：ContDiffAt.differentiableAt_
iteratedFDeriv {f : E -> F} {n : Nat∞ω} {m : Nat} {x : E} (h : ContDiffAt 𝕜 n f 
x) (hmn : ↑m < n) : Differentiab…
· 使用定理 `Asymptotics.IsBigO.of_norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' 
: α → E'} {l : Filter…
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Asymptotics.IsBigO.id_rpow_of_le_one`：∀ {a : ℝ}, a ≤ 1 → id =O[nhdsWithi
n 0 (Set.Ici 0)] fun x => x ^ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `tendsto_norm_sub_self_nhdsGE`：∀ {E : Type u_4} [inst : SeminormedAddComm
Group E] (x : E),   Filter.Tendsto (fun a => ‖a - x‖) (nhds x) (nhdsWithin 0 (Se
t.Ici 0))

--- 原说明 ---
A $C^n$ map is a $C^{k+(α)}$ map for any `k < n`.
-/
theorem ContDiffAt.contDiffPointwiseHolderAt {n : WithTop ℕ∞} (h : ContDiffAt ℝ n f a) (hk : k < n)
    (α : I) : ContDiffPointwiseHolderAt k α f a where
  contDiffAt := h.of_le hk.le
  isBigO := calc
    (iteratedFDeriv ℝ k f · - iteratedFDeriv ℝ k f a) =O[𝓝 a] (· - a) :=
      (h.differentiableAt_iteratedFDeriv hk).isBigO_sub
    _ =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) :=
      .of_norm_left <| .comp_tendsto (.id_rpow_of_le_one α.2.2) <| tendsto_norm_sub_self_nhdsGE a

namespace ContDiffPointwiseHolderAt

/-
**ContDiffPointwiseHolderAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPoin
twiseHolderAt`。
形式化陈述：continuousAt (h : ContDiffPointwiseHolderAt k α f a) : ContinuousAt f a
参数：h : ContDiffPointwiseHolderAt k α f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.continuousAt`：ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x
) : ContinuousAt f x
· 使用定理 `ContDiffPointwiseHolderAt.contDiffAt`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
-/
theorem continuousAt (h : ContDiffPointwiseHolderAt k α f a) : ContinuousAt f a :=
  h.contDiffAt.continuousAt
/-
**ContDiffPointwiseHolderAt.differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `ContDiff
PointwiseHolderAt`。
形式化陈述：differentiableAt (h : ContDiffPointwiseHolderAt k α f a) (hk : k != 0) : D
ifferentiableAt Real f a
参数：h : ContDiffPointwiseHolderAt k α f a；hk : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `ContDiffPointwiseHolderAt.contDiffAt`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem differentiableAt (h : ContDiffPointwiseHolderAt k α f a) (hk : k ≠ 0) :
    DifferentiableAt ℝ f a :=
  h.contDiffAt.differentiableAt <| mod_cast hk

/-- A function is $C^{k+(0)}$ at a point if and only if it is $C^k$ at the point. -/
@[simp]
/-
**ContDiffPointwiseHolderAt.zero_exponent_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContDif
fPointwiseHolderAt`。
形式化陈述：zero_exponent_iff : ContDiffPointwiseHolderAt k 0 f a ↔ ContDiffAt Real k 
f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffPointwiseHolderAt.contDiffAt`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
· 使用定理 `Filter.Tendsto.sub_const`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] {c : G} {f : α → G}   {l : Filter α
}, Filter.Tend…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `ContDiffAt.continuousAt_iteratedFDeriv`：ContDiffAt.continuousAt_iterated
FDeriv {k : Nat} (hf : ContDiffAt 𝕜 n f x) (hk : k <= n) : ContinuousAt (iterate
dFDeriv 𝕜 k f) x
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
A function is $C^{k+(0)}$ at a point if and only if it is $C^k$ at the point.
-/
theorem zero_exponent_iff : ContDiffPointwiseHolderAt k 0 f a ↔ ContDiffAt ℝ k f a := by
  refine ⟨contDiffAt, fun h ↦ ⟨h, ?_⟩⟩
  simpa using ((h.continuousAt_iteratedFDeriv le_rfl).sub_const _).norm.isBoundedUnder_le

/-- A function is $C^{0+(α)}$ at a point if and only if
it is $C^0$ at the point (i.e., it is continuous on a neighborhood of the point)
and $f(x) - f(a) = O(‖x - a‖ ^ α)$. -/
/-
**ContDiffPointwiseHolderAt.zero_order_iff** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPo
intwiseHolderAt`。
形式化陈述：zero_order_iff : ContDiffPointwiseHolderAt 0 α f a ↔ ContDiffAt Real 0 f a
 ∧ (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (α : Real))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isBigO_norm_left`：isBigO_norm_left : (fun x => ‖f' x‖) =O[l]
 g ↔ f' =O[l] g
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A function is $C^{0+(α)}$ at a point if and only if
it is $C^0$ at the point (i.e., it is continuous on a neighborhood of the point)
and $f(x) - f(a) = O(‖x - a‖ ^ α)$.
-/
theorem zero_order_iff :
    ContDiffPointwiseHolderAt 0 α f a ↔
      ContDiffAt ℝ 0 f a ∧ (f · - f a) =O[𝓝 a] (‖· - a‖ ^ (α : ℝ)) := by
  simp only [contDiffPointwiseHolderAt_iff, Nat.cast_zero, and_congr_right_iff]
  intro hfc
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_def, ← map_sub]
  rw [← isBigO_norm_left]
  simp_rw [LinearIsometryEquiv.norm_map, isBigO_norm_left]
/-
**ContDiffPointwiseHolderAt.of_exponent_le** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPo
intwiseHolderAt`。
形式化陈述：of_exponent_le (hf : ContDiffPointwiseHolderAt k α f a) (hle : β <= α) : C
ontDiffPointwiseHolderAt k β f a where contDiffAt
参数：hf : ContDiffPointwiseHolderAt k α f a；hle : β <= α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffPointwiseHolderAt.contDiffAt`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContDiffPointwiseHolderAt.isBigO`：∀ {E : Type u_1} {F : Type u_2} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup 
F]   [inst_3 : NormedS…
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Asymptotics.IsBigO.rpow_rpow_nhdsGE_zero_of_le_of_imp`：∀ {a b : ℝ}, a ≤ 
b → (b = 0 → a = 0) → (fun x => x ^ b) =O[nhdsWithin 0 (Set.Ici 0)] fun x => x ^
 a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `tendsto_norm_sub_self_nhdsGE`：∀ {E : Type u_4} [inst : SeminormedAddComm
Group E] (x : E),   Filter.Tendsto (fun a => ‖a - x‖) (nhds x) (nhdsWithin 0 (Se
t.Ici 0))
-/
theorem of_exponent_le (hf : ContDiffPointwiseHolderAt k α f a) (hle : β ≤ α) :
    ContDiffPointwiseHolderAt k β f a where
  contDiffAt := hf.contDiffAt
  isBigO := hf.isBigO.trans <| by
    refine .comp_tendsto (.rpow_rpow_nhdsGE_zero_of_le_of_imp hle fun hα ↦ ?_) ?_
    · exact le_antisymm (le_trans (mod_cast hle) hα.le) β.2.1
    · exact tendsto_norm_sub_self_nhdsGE a
/-
**ContDiffPointwiseHolderAt.of_order_lt** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPoint
wiseHolderAt`。
形式化陈述：of_order_lt (hf : ContDiffPointwiseHolderAt k α f a) (hlt : l < k) : ContD
iffPointwiseHolderAt l β f a
参数：hf : ContDiffPointwiseHolderAt k α f a；hlt : l < k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffPointwiseHolderAt`：ContDiffAt.contDiffPointwiseHolder
At {n : WithTop Nat∞} (h : ContDiffAt Real n f a) (hk : k < n) (α : I) : ContDif
fPointwiseHolderAt k α f a…
· 使用定理 `ContDiffPointwiseHolderAt.contDiffAt`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem of_order_lt (hf : ContDiffPointwiseHolderAt k α f a) (hlt : l < k) :
    ContDiffPointwiseHolderAt l β f a :=
  hf.contDiffAt.contDiffPointwiseHolderAt (mod_cast hlt) _
/-
**ContDiffPointwiseHolderAt.of_toLex_le** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPoint
wiseHolderAt`。
形式化陈述：of_toLex_le (hf : ContDiffPointwiseHolderAt k α f a) (hle : toLex (l, β) <
= toLex (k, α)) : ContDiffPointwiseHolderAt l β f a
参数：hf : ContDiffPointwiseHolderAt k α f a；hle : toLex (l, β) <= toLex (k, α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Prod.Lex.le_iff`：le_iff [LT α] [LE β] {x y : α ×ₗ β} : x <= y ↔ (ofLex x
).1 < (ofLex y).1 ∨ (ofLex x).1 = (ofLex y).1 ∧ (ofLex x).2 <= (ofLex y).2
· 使用定理 `ContDiffPointwiseHolderAt.of_order_lt`：of_order_lt (hf : ContDiffPointwi
seHolderAt k α f a) (hlt : l < k) : ContDiffPointwiseHolderAt l β f a
· 使用定理 `ContDiffPointwiseHolderAt.of_exponent_le`：of_exponent_le (hf : ContDiffP
ointwiseHolderAt k α f a) (hle : β <= α) : ContDiffPointwiseHolderAt k β f a whe
re contDiffAt
-/
theorem of_toLex_le (hf : ContDiffPointwiseHolderAt k α f a) (hle : toLex (l, β) ≤ toLex (k, α)) :
    ContDiffPointwiseHolderAt l β f a :=
  (Prod.Lex.le_iff.mp hle).elim hf.of_order_lt <| by rintro ⟨rfl, hle⟩; exact hf.of_exponent_le hle
/-
**ContDiffPointwiseHolderAt.of_order_le** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPoint
wiseHolderAt`。
形式化陈述：of_order_le (hf : ContDiffPointwiseHolderAt k α f a) (hl : l <= k) : ContD
iffPointwiseHolderAt l α f a
参数：hf : ContDiffPointwiseHolderAt k α f a；hl : l <= k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffPointwiseHolderAt.of_toLex_le`：of_toLex_le (hf : ContDiffPointwi
seHolderAt k α f a) (hle : toLex (l, β) <= toLex (k, α)) : ContDiffPointwiseHold
erAt l β f a
· 使用定理 `Prod.Lex.toLex_mono`：toLex_mono : Monotone (toLex : α × β -> α ×ₗ β)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem of_order_le (hf : ContDiffPointwiseHolderAt k α f a) (hl : l ≤ k) :
    ContDiffPointwiseHolderAt l α f a :=
  hf.of_toLex_le <| Prod.Lex.toLex_mono ⟨hl, le_rfl⟩

/-- If a function is $C^{k+α}$ on a neighborhood of a point `a`,
i.e., it is $C^k$ on this neighborhood and $D^k f$ is Hölder continuous on it,
then the function is $C^{k+(α)}$ at `a`. -/
/-
**ContDiffPointwiseHolderAt.of_contDiffOn_holderOnWith** 是 Mathlib 中的一个定理，位于命名空间
 `ContDiffPointwiseHolderAt`。
形式化陈述：of_contDiffOn_holderOnWith {s : Set E} {C : Real>=0} (hf : ContDiffOn Real
 k f s) (hs : s in 𝓝 a) (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv Real k f
) s) : ContDiffPointwiseHolderAt k α f a where contDiffAt
参数：hf : ContDiffOn Real k f s；hs : s in 𝓝 a；hd : HolderOnWith C ⟨α, α.2.1⟩ (iter
atedFDeriv Real k f) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContDiffOn.contDiffAt`：ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (h
x : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.abs_rpow_of_nonneg`：abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 
<= x) : |x ^ y| = |x| ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `abs_dist`：∀ {α : Type u} [inst : PseudoMetricSpace α] {a b : α}, |dist a
 b| = dist a b
· 使用定理 `HolderOnWith.dist_le`：dist_le (hf : HolderOnWith C r f s) (hx : x in s) 
(hy : y in s) : dist (f x) (f y) <= C * dist x y ^ (r : Real)
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
If a function is $C^{k+α}$ on a neighborhood of a point `a`,
i.e., it is $C^k$ on this neighborhood and $D^k f$ is Hölder continuous on it,
then the function is $C^{k+(α)}$ at `a`.
-/
theorem of_contDiffOn_holderOnWith {s : Set E} {C : ℝ≥0} (hf : ContDiffOn ℝ k f s) (hs : s ∈ 𝓝 a)
    (hd : HolderOnWith C ⟨α, α.2.1⟩ (iteratedFDeriv ℝ k f) s) :
    ContDiffPointwiseHolderAt k α f a where
  contDiffAt := hf.contDiffAt hs
  isBigO := .of_bound C <| mem_of_superset hs fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg, ← dist_eq_norm, dist_nonneg]
      using! hd.dist_le hx (mem_of_mem_nhds hs)
/-
**ContDiffPointwiseHolderAt.fst** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseHold
erAt`。
形式化陈述：fst {a : E × F} : ContDiffPointwiseHolderAt k α Prod.fst a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffPointwiseHolderAt`：ContDiffAt.contDiffPointwiseHolder
At {n : WithTop Nat∞} (h : ContDiffAt Real n f a) (hk : k < n) (α : I) : ContDif
fPointwiseHolderAt k α f a…
· 使用定理 `contDiffAt_fst`：contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : 
E × F -> E) p
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
theorem fst {a : E × F} : ContDiffPointwiseHolderAt k α Prod.fst a :=
  contDiffAt_fst.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α
/-
**ContDiffPointwiseHolderAt.snd** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseHold
erAt`。
形式化陈述：snd {a : E × F} : ContDiffPointwiseHolderAt k α Prod.snd a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffPointwiseHolderAt`：ContDiffAt.contDiffPointwiseHolder
At {n : WithTop Nat∞} (h : ContDiffAt Real n f a) (hk : k < n) (α : I) : ContDif
fPointwiseHolderAt k α f a…
· 使用定理 `contDiffAt_snd`：contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : 
E × F -> F) p
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
theorem snd {a : E × F} : ContDiffPointwiseHolderAt k α Prod.snd a :=
  contDiffAt_snd.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α
/-
**ContDiffPointwiseHolderAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseH
olderAt`。
形式化陈述：prodMk {g : E -> G} (hf : ContDiffPointwiseHolderAt k α f a) (hg : ContDif
fPointwiseHolderAt k α g a) : ContDiffPointwiseHolderAt k α (fun x => (f x, g x)
) a where contDiffAt
参数：hf : ContDiffPointwiseHolderAt k α f a；hg : ContDiffPointwiseHolderAt k α g a
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.prodMk`：ContDiffAt.prodMk {f : E -> F} {g : E -> G} (hf : Con
tDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, 
g x)) x
· 使用定理 `ContDiffPointwiseHolderAt.contDiffAt`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContDiffAt.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type uF} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `iteratedFDeriv_prodMk`：iteratedFDeriv_prodMk {f : E -> F} {g : E -> G} (
hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) {i : Nat} (hi : i <= n) : ite
ratedFDeriv…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousMultilinearMap.instIsSubApplyForall`：∀ {R : Type u} {ι : Type 
v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Ring R] [inst_1 : (i : ι) → AddComm
Group (M₁ i)]   [inst_2 : AddCommGr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Asymptotics.IsBigO.of_norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' 
: α → E'} {l : Filter…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMultilinearMap.opNorm_prod`：opNorm_prod (f : ContinuousMultili
nearMap 𝕜 E G) (g : ContinuousMultilinearMap 𝕜 E G') : ‖f.prod g‖ = max ‖f‖ ‖g‖
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
· 使用定理 `Asymptotics.IsBigO.prod_left`：∀ {α : Type u_1} {E' : Type u_6} {F' : Typ
e u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Seminormed
AddCommGroup F'] […
· 使用定理 `ContDiffPointwiseHolderAt.isBigO`：∀ {E : Type u_1} {F : Type u_2} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup 
F]   [inst_3 : NormedS…
-/
theorem prodMk {g : E → G} (hf : ContDiffPointwiseHolderAt k α f a)
    (hg : ContDiffPointwiseHolderAt k α g a) :
    ContDiffPointwiseHolderAt k α (fun x ↦ (f x, g x)) a where
  contDiffAt := hf.contDiffAt.prodMk hg.contDiffAt
  isBigO := calc
    _ =ᶠ[𝓝 a] (fun x ↦ (iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f a).prod
                (iteratedFDeriv ℝ k g x - iteratedFDeriv ℝ k g a)) := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hg.contDiffAt.eventually (by simp)] with x hfx hgx
      apply DFunLike.ext
      rw [iteratedFDeriv_prodMk _ _ le_rfl, iteratedFDeriv_prodMk _ _ le_rfl] <;>
        simp [hfx, hgx, hf.contDiffAt, hg.contDiffAt]
    _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := by
      refine .of_norm_left ?_
      simp only [ContinuousMultilinearMap.opNorm_prod, ← Prod.norm_mk]
      exact (hf.isBigO.prod_left hg.isBigO).norm_left

variable (a) in
/-- Composition of two $C^{k+(α)}$ functions is a $C^{k+(α)}$ function,
provided that one of them is differentiable.

The latter condition follows automatically from the functions being $C^{k+(α)}$,
if `k ≠ 0`, see `comp` below. -/
/-
**ContDiffPointwiseHolderAt.comp_of_differentiableAt** 是 Mathlib 中的一个定理，位于命名空间 `
ContDiffPointwiseHolderAt`。
形式化陈述：comp_of_differentiableAt {g : F -> G} (hg : ContDiffPointwiseHolderAt k α 
g (f a)) (hf : ContDiffPointwiseHolderAt k α f a) (hd : DifferentiableAt Real g 
(f a) ∨ DifferentiableAt Real f a) : ContDiffPointwiseHolderAt k α (g ∘ f) a whe
re contDiffAt
参数：hg : ContDiffPointwiseHolderAt k α g (f a)；hf : ContDiffPointwiseHolderAt k α
 f a；hd : DifferentiableAt Real g (f a) ∨ DifferentiableAt Real f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `ContDiffPointwiseHolderAt.contDiffAt`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `ContDiffPointwiseHolderAt.continuousAt`：continuousAt (h : ContDiffPointw
iseHolderAt k α f a) : ContinuousAt f a
· 使用定理 `ContDiffAt.eventually`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type uF} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `iteratedFDeriv_comp`：iteratedFDeriv_comp (hg : ContDiffAt 𝕜 n g (f x)) (
hf : ContDiffAt 𝕜 n f x) {i : Nat} (hi : i <= n) : iteratedFDeriv 𝕜 i (g ∘ f) x 
= (ftaylo…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO`：taylorComp_sub
_taylorComp_isBigO {α H : Type*} [NormedAddCommGroup H] {l : Filter α} {p₁ p₂ : 
α -> FormalMultilinearSeries 𝕜 F G} {q₁ q₂ : α…
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousAt.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {a : α},   ContinuousAt f a →
 Contin…
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `ContDiffAt.continuousAt_iteratedFDeriv`：ContDiffAt.continuousAt_iterated
FDeriv {k : Nat} (hf : ContDiffAt 𝕜 n f x) (hk : k <= n) : ContinuousAt (iterate
dFDeriv 𝕜 k f) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
Composition of two $C^{k+(α)}$ functions is a $C^{k+(α)}$ function,
provided that one of them is differentiable.

The latter condition follows automatically from the functions being $C^{k+(α)}$,
if `k ≠ 0`, see `comp` below.
-/
theorem comp_of_differentiableAt {g : F → G} (hg : ContDiffPointwiseHolderAt k α g (f a))
    (hf : ContDiffPointwiseHolderAt k α f a)
    (hd : DifferentiableAt ℝ g (f a) ∨ DifferentiableAt ℝ f a) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a where
  contDiffAt := hg.contDiffAt.comp a hf.contDiffAt
  isBigO := calc
    (iteratedFDeriv ℝ k (g ∘ f) · - iteratedFDeriv ℝ k (g ∘ f) a)
      =ᶠ[𝓝 a] fun x ↦ (ftaylorSeries ℝ g (f x)).taylorComp (ftaylorSeries ℝ f x) k -
        (ftaylorSeries ℝ g (f a)).taylorComp (ftaylorSeries ℝ f a) k := by
      filter_upwards [hf.contDiffAt.eventually (by simp),
        hf.continuousAt.eventually (hg.contDiffAt.eventually (by simp))] with x hfx hgx
      rw [iteratedFDeriv_comp hgx hfx le_rfl,
        iteratedFDeriv_comp hg.contDiffAt hf.contDiffAt le_rfl]
    _ =O[𝓝 a] fun x ↦ ‖x - a‖ ^ (α : ℝ) := by
      apply FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO <;> intro i hi
      · exact ((hg.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).comp hf.continuousAt)
          |>.norm.isBoundedUnder_le
      · by_cases hfd : DifferentiableAt ℝ f a
        · refine ((hg.of_order_le hi).isBigO.comp_tendsto hf.continuousAt).trans ?_
          refine .rpow α.2.1 (.of_forall fun _ ↦ norm_nonneg _) <| .norm_norm ?_
          exact hfd.isBigO_sub
        · obtain rfl : k = 0 := by
            contrapose! hfd
            exact hf.differentiableAt hfd
          obtain rfl : i = 0 := by rwa [nonpos_iff_eq_zero] at hi
          refine .of_norm_left ?_
          simp only [ftaylorSeries, iteratedFDeriv_zero_eq_comp, Function.comp_apply, ← map_sub,
            LinearIsometryEquiv.norm_map, isBigO_norm_left]
          refine ((hd.resolve_right hfd).isBigO_sub.comp_tendsto hf.continuousAt).trans ?_
          exact (zero_order_iff.mp hf).2
      · exact (hf.contDiffAt.continuousAt_iteratedFDeriv (mod_cast hi)).norm.isBoundedUnder_le
      · exact isBoundedUnder_const
      · exact (hf.of_order_le hi).isBigO

variable (a) in
/-- Composition of two $C^{k+(α)}$ functions, `k ≠ 0`, is a $C^{k+(α)}$ function. -/
/-
**ContDiffPointwiseHolderAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseHol
derAt`。
形式化陈述：comp {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a)) (hf : ContD
iffPointwiseHolderAt k α f a) (hk : k != 0) : ContDiffPointwiseHolderAt k α (g ∘
 f) a
参数：hg : ContDiffPointwiseHolderAt k α g (f a)；hf : ContDiffPointwiseHolderAt k α
 f a；hk : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffPointwiseHolderAt.comp_of_differentiableAt`：comp_of_differentiab
leAt {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a)) (hf : ContDiffPoi
ntwiseHolderAt k α f a) (hd : Differenti…
· 使用定理 `ContDiffPointwiseHolderAt.differentiableAt`：differentiableAt (h : ContDi
ffPointwiseHolderAt k α f a) (hk : k != 0) : DifferentiableAt Real f a

--- 原说明 ---
Composition of two $C^{k+(α)}$ functions, `k ≠ 0`, is a $C^{k+(α)}$ function.
-/
theorem comp {g : F → G} (hg : ContDiffPointwiseHolderAt k α g (f a))
    (hf : ContDiffPointwiseHolderAt k α f a) (hk : k ≠ 0) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a :=
  hg.comp_of_differentiableAt a hf (.inl <| hg.differentiableAt hk)

variable (a) in
/-
**ContDiffPointwiseHolderAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseHol
derAt`。
形式化陈述：comp {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a)) (hf : ContD
iffPointwiseHolderAt k α f a) (hk : k != 0) : ContDiffPointwiseHolderAt k α (g ∘
 f) a
参数：hg : ContDiffPointwiseHolderAt k α g (f a)；hf : ContDiffPointwiseHolderAt k α
 f a；hk : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffPointwiseHolderAt.comp_of_differentiableAt`：comp_of_differentiab
leAt {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a)) (hf : ContDiffPoi
ntwiseHolderAt k α f a) (hd : Differenti…
· 使用定理 `ContDiffPointwiseHolderAt.differentiableAt`：differentiableAt (h : ContDi
ffPointwiseHolderAt k α f a) (hk : k != 0) : DifferentiableAt Real f a
-/
theorem comp₂_of_differentiableAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : F × G → H} {f₁ : E → F} {f₂ : E → G} (hg : ContDiffPointwiseHolderAt k α g (f₁ a, f₂ a))
    (hf₁ : ContDiffPointwiseHolderAt k α f₁ a) (hf₂ : ContDiffPointwiseHolderAt k α f₂ a)
    (hdiff : DifferentiableAt ℝ g (f₁ a, f₂ a) ∨
      DifferentiableAt ℝ f₁ a ∧ DifferentiableAt ℝ f₂ a) :
    ContDiffPointwiseHolderAt k α (fun x ↦ g (f₁ x, f₂ x)) a :=
  hg.comp_of_differentiableAt a (hf₁.prodMk hf₂) <| hdiff.imp_right fun h ↦
    h.left.prodMk h.right
/-
**ContDiffPointwiseHolderAt._root_.ContinuousLinearMap.contDiffPointwiseHolderAt
** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseHolderAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearMap.contDiffPointwiseHolderAt (f : E →L[ℝ] F) :
    ContDiffPointwiseHolderAt k α f a :=
  f.contDiff.contDiffAt.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) _
/-
**ContDiffPointwiseHolderAt._root_.ContinuousLinearEquiv.contDiffPointwiseHolder
At** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseHolderAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt (f : E ≃L[ℝ] F) :
    ContDiffPointwiseHolderAt k α f a :=
  f.toContinuousLinearMap.contDiffPointwiseHolderAt
/-
**ContDiffPointwiseHolderAt.continuousLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `
ContDiffPointwiseHolderAt`。
形式化陈述：continuousLinearMap_comp (hf : ContDiffPointwiseHolderAt k α f a) (g : F -
>L[Real] G) : ContDiffPointwiseHolderAt k α (g ∘ f) a
参数：hf : ContDiffPointwiseHolderAt k α f a；g : F ->L[Real] G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffPointwiseHolderAt.comp_of_differentiableAt`：comp_of_differentiab
leAt {g : F -> G} (hg : ContDiffPointwiseHolderAt k α g (f a)) (hf : ContDiffPoi
ntwiseHolderAt k α f a) (hd : Differenti…
· 使用定理 `ContinuousLinearMap.contDiffPointwiseHolderAt`：∀ {E : Type u_1} {F : Typ
e u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : Normed
AddCommGroup F]   [inst_3 : NormedS…
· 使用定理 `ContinuousLinearMap.differentiableAt`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Mo
dule 𝕜 E] [inst_3 : Topolo…
-/
theorem continuousLinearMap_comp (hf : ContDiffPointwiseHolderAt k α f a) (g : F →L[ℝ] G) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a :=
  g.contDiffPointwiseHolderAt.comp_of_differentiableAt a hf <| .inl g.differentiableAt

@[simp]
/-
**ContDiffPointwiseHolderAt._root_.ContinuousLinearEquiv.contDiffPointwiseHolder
At_left_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseHolderAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp (g : F ≃L[ℝ] G) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a ↔ ContDiffPointwiseHolderAt k α f a :=
  ⟨fun h ↦ by simpa [Function.comp_def] using h.continuousLinearMap_comp (g.symm : G →L[ℝ] F),
    fun h ↦ h.continuousLinearMap_comp (g : F →L[ℝ] G)⟩

@[simp]
/-
**ContDiffPointwiseHolderAt._root_.LinearIsometryEquiv.contDiffPointwiseHolderAt
_left_comp** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseHolderAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometryEquiv.contDiffPointwiseHolderAt_left_comp (g : F ≃ₗᵢ[ℝ] G) :
    ContDiffPointwiseHolderAt k α (g ∘ f) a ↔ ContDiffPointwiseHolderAt k α f a :=
  g.toContinuousLinearEquiv.contDiffPointwiseHolderAt_left_comp
/-
**ContDiffPointwiseHolderAt.id** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseHolde
rAt`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
{k : ℕ} {α : ↑unitInterval} {a : E},   ContDiffPointwiseHolderAt k α id a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.contDiffPointwiseHolderAt`：∀ {E : Type u_1} {F : Typ
e u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : Normed
AddCommGroup F]   [inst_3 : NormedS…
-/
protected theorem id : ContDiffPointwiseHolderAt k α id a :=
  ContinuousLinearMap.id ℝ E |>.contDiffPointwiseHolderAt
/-
**ContDiffPointwiseHolderAt.const** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseHo
lderAt`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {k :
 ℕ} {α : ↑unitInterval} {a : E} {b : F},   ContDiffPointwiseHolderAt k α (Functi
on.const E b) a
参数：Function.const E b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffPointwiseHolderAt`：ContDiffAt.contDiffPointwiseHolder
At {n : WithTop Nat∞} (h : ContDiffAt Real n f a) (hk : k < n) (α : I) : ContDif
fPointwiseHolderAt k α f a…
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
protected theorem const {b : F} : ContDiffPointwiseHolderAt k α (Function.const E b) a :=
  contDiffAt_const.contDiffPointwiseHolderAt (WithTop.coe_lt_top _) α

/-- The derivative of a $C^{k + (α)}$ function is a $C^{l + (α)}$ function, if `l < k`. -/
/-
**ContDiffPointwiseHolderAt.fderiv** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwiseH
olderAt`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {k l
 : ℕ} {α : ↑unitInterval} {f : E → F} {a : E},   ContDiffPointwiseHolderAt k α f
 a → l < k → ContDiffPointwiseHolderAt l α (fderiv ℝ f) a
参数：fderiv ℝ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.fderiv_right`：ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f 
x₀) (hmn : m + 1 <= n) : ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀
· 使用定理 `ContDiffPointwiseHolderAt.contDiffAt`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Asymptotics.IsBigO.of_norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' 
: α → E'} {l : Filter…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `iteratedFDeriv_succ_eq_comp_right`：iteratedFDeriv_succ_eq_comp_right {n 
: Nat} : iteratedFDeriv 𝕜 (n + 1) f x = ((continuousMultilinearCurryRightEquiv' 
𝕜 n E F).symm ∘ iterate…
· 使用定理 `LinearIsometryEquiv.dist_map`：dist_map (x y : E) : dist (e x) (e y) = di
st x y
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
· 使用定理 `ContDiffPointwiseHolderAt.isBigO`：∀ {E : Type u_1} {F : Type u_2} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup 
F]   [inst_3 : NormedS…
· 使用定理 `ContDiffPointwiseHolderAt.of_order_le`：of_order_le (hf : ContDiffPointwi
seHolderAt k α f a) (hl : l <= k) : ContDiffPointwiseHolderAt l α f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m

--- 原说明 ---
The derivative of a $C^{k + (α)}$ function is a $C^{l + (α)}$ function, if `l < 
k`.
-/
protected theorem fderiv (hf : ContDiffPointwiseHolderAt k α f a) (hl : l < k) :
    ContDiffPointwiseHolderAt l α (fderiv ℝ f) a where
  contDiffAt := hf.contDiffAt.fderiv_right (mod_cast hl)
  isBigO := .of_norm_left <| by
    simpa [iteratedFDeriv_succ_eq_comp_right, Function.comp_def, ← dist_eq_norm_sub]
      using hf.of_order_le (Nat.add_one_le_iff.mpr hl) |>.isBigO |>.norm_left

/-- If `f` is a $C^{k+(α)}$ function and `l + m ≤ k`, then $D^mf$ is a $C^{l + (α)}$ function. -/
/-
**ContDiffPointwiseHolderAt.iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPo
intwiseHolderAt`。
形式化陈述：∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : No
rmedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst_3 : NormedSpace ℝ F] {k l
 m : ℕ} {α : ↑unitInterval} {f : E → F} {a : E},   ContDiffPointwiseHolderAt k α
 f a → l + m ≤ k → ContDiffPointwiseHolderAt l α (iteratedFDeriv ℝ m f) a
参数：iteratedFDeriv ℝ m f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ContDiffPointwiseHolderAt.of_order_le`：of_order_le (hf : ContDiffPointwi
seHolderAt k α f a) (hl : l <= k) : ContDiffPointwiseHolderAt l α f a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `ContDiffPointwiseHolderAt.fderiv`：∀ {E : Type u_1} {F : Type u_2} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup 
F]   [inst_3 : NormedS…
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1

--- 原说明 ---
If `f` is a $C^{k+(α)}$ function and `l + m ≤ k`, then $D^mf$ is a $C^{l + (α)}$
 function.
-/
protected theorem iteratedFDeriv (hf : ContDiffPointwiseHolderAt k α f a) (hl : l + m ≤ k) :
    ContDiffPointwiseHolderAt l α (iteratedFDeriv ℝ m f) a := by
  induction m generalizing l with
  | zero =>
    simpa +unfoldPartialApp [iteratedFDeriv_zero_eq_comp] using hf.of_order_le hl
  | succ m ihm =>
    rw [← add_assoc, add_right_comm] at hl
    simpa +unfoldPartialApp [iteratedFDeriv_succ_eq_comp_left] using (ihm hl).fderiv l.lt_add_one
/-
**ContDiffPointwiseHolderAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Con
tDiffPointwiseHolderAt`。
形式化陈述：congr_of_eventuallyEq {g : E -> F} (hf : ContDiffPointwiseHolderAt k α f a
) (hfg : f =ᶠ[𝓝 a] g) : ContDiffPointwiseHolderAt k α g a where contDiffAt
参数：hf : ContDiffPointwiseHolderAt k α f a；hfg : f =ᶠ[𝓝 a] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.congr_of_eventuallyEq`：ContDiffAt.congr_of_eventuallyEq (h : 
ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) : ContDiffAt 𝕜 n f₁ x
· 使用定理 `ContDiffPointwiseHolderAt.contDiffAt`：∀ {E : Type u_1} {F : Type u_2} [i
nst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGr
oup F]   [inst_3 : NormedS…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g :
 α → F}, f₁ =ᶠ[l] f₂ →…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `Filter.EventuallyEq.iteratedFDeriv`：∀ (𝕜 : Type u) [inst : NontriviallyN
ormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Type uF} […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `ContDiffPointwiseHolderAt.isBigO`：∀ {E : Type u_1} {F : Type u_2} [inst 
: NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup 
F]   [inst_3 : NormedS…
-/
theorem congr_of_eventuallyEq {g : E → F} (hf : ContDiffPointwiseHolderAt k α f a)
    (hfg : f =ᶠ[𝓝 a] g) :
    ContDiffPointwiseHolderAt k α g a where
  contDiffAt := hf.contDiffAt.congr_of_eventuallyEq hfg.symm
  isBigO := by
    refine EventuallyEq.trans_isBigO (.sub ?_ ?_) hf.isBigO
    · exact hfg.symm.iteratedFDeriv ℝ _
    · rw [hfg.symm.iteratedFDeriv ℝ _ |>.self_of_nhds]
/-
**ContDiffPointwiseHolderAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ContDiffPointwi
seHolderAt`。
形式化陈述：clm_apply {f : E -> F ->L[Real] G} {g : E -> F} (hf : ContDiffPointwiseHol
derAt k α f a) (hg : ContDiffPointwiseHolderAt k α g a) : ContDiffPointwiseHolde
rAt k α (fun x => f x (g x)) a
参数：hf : ContDiffPointwiseHolderAt k α f a；hg : ContDiffPointwiseHolderAt k α g a
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffPointwiseHolderAt.comp₂_of_differentiableAt`：comp₂_of_differenti
ableAt {H : Type*} [NormedAddCommGroup H] [NormedSpace Real H] {g : F × G -> H} 
{f₁ : E -> F} {f₂ : E -> G} (hg : ContDif…
· 使用定理 `ContDiffAt.contDiffPointwiseHolderAt`：ContDiffAt.contDiffPointwiseHolder
At {n : WithTop Nat∞} (h : ContDiffAt Real n f a) (hk : k < n) (α : I) : ContDif
fPointwiseHolderAt k α f a…
· 使用定理 `ContDiffAt.clm_apply`：ContDiffAt.clm_apply {f : E -> F ->L[𝕜] G} {g : E 
-> F} (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun 
x => (f x)…
· 使用定理 `contDiffAt_fst`：contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : 
E × F -> E) p
· 使用定理 `contDiffAt_snd`：contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : 
E × F -> F) p
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
· 使用定理 `DifferentiableAt.clm_apply`：DifferentiableAt.clm_apply (hc : Differentia
bleAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) : DifferentiableAt 𝕜 (fun y => (c y) 
(u y)) x
· 使用定理 `DifferentiableAt.fst`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F
 : Type u_…
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `DifferentiableAt.snd`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F
 : Type u_…
-/
theorem clm_apply {f : E → F →L[ℝ] G} {g : E → F} (hf : ContDiffPointwiseHolderAt k α f a)
    (hg : ContDiffPointwiseHolderAt k α g a) :
    ContDiffPointwiseHolderAt k α (fun x ↦ f x (g x)) a :=
  (contDiffAt_fst.clm_apply contDiffAt_snd).contDiffPointwiseHolderAt (WithTop.coe_lt_top _) _
    |>.comp₂_of_differentiableAt a hf hg <| .inl (by fun_prop)

end ContDiffPointwiseHolderAt

