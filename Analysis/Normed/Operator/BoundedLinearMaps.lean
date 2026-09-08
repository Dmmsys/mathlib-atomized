/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded linear maps

This file defines a class stating that a map between normed vector spaces is (bi)linear and
continuous.
Instead of asking for continuity, the definition takes the equivalent condition (because the space
is normed) that `‖f x‖` is bounded by a multiple of `‖x‖`. Hence the "bounded" in the name refers to
`‖f x‖/‖x‖` rather than `‖f x‖` itself.

## Main definitions

* `IsBoundedLinearMap`: Class stating that a map `f : E → F` is linear and has `‖f x‖` bounded
  by a multiple of `‖x‖`.
* `IsBoundedBilinearMap`: Class stating that a map `f : E × F → G` is bilinear and continuous,
  but through the simpler to provide statement that `‖f (x, y)‖` is bounded by a multiple of
  `‖x‖ * ‖y‖`
* `IsBoundedBilinearMap.linearDeriv`: Derivative of a continuous bilinear map as a linear map.
* `IsBoundedBilinearMap.deriv`: Derivative of a continuous bilinear map as a continuous linear
  map. The proof that it is indeed the derivative is `IsBoundedBilinearMap.hasFDerivAt` in
  `Analysis.Calculus.FDeriv`.

## Main theorems

* `IsBoundedBilinearMap.continuous`: A bounded bilinear map is continuous.
* `ContinuousLinearEquiv.isOpen`: The continuous linear equivalences are an open subset of the
  set of continuous linear maps between a pair of Banach spaces.  Placed in this file because its
  proof uses `IsBoundedBilinearMap.continuous`.

## Notes

The main use of this file is `IsBoundedBilinearMap`.
The file `Mathlib/Analysis/NormedSpace/Multilinear/Basic.lean`
already expounds the theory of multilinear maps,
but the `2`-variables case is sufficiently simpler to currently deserve its own treatment.

`IsBoundedLinearMap` is effectively an unbundled version of `ContinuousLinearMap` (defined
in `Topology.Algebra.Module.Basic`, theory over normed spaces developed in
`Analysis.NormedSpace.OperatorNorm`), albeit the name disparity. A bundled
`ContinuousLinearMap` is to be preferred over an `IsBoundedLinearMap` hypothesis. Historical
artifact, really.
-/

@[expose] public section


noncomputable section

open Topology

open Filter (Tendsto)

open Metric ContinuousLinearMap

section Semiring

variable {𝕜 E F G : Type*} [Semiring 𝕜]
    [SeminormedAddCommGroup E] [Module 𝕜 E]
    [SeminormedAddCommGroup F] [Module 𝕜 F]
    [SeminormedAddCommGroup G] [Module 𝕜 G]
    {f g : E → F}

variable (𝕜 f) in
/-- A function `f` satisfies `IsBoundedLinearMap 𝕜 f` if it is linear and satisfies the
inequality `‖f x‖ ≤ M * ‖x‖` for some positive constant `M`.

(We put only the typeclasses strictly necessary for the definition, although the main case of
interest is when `𝕜` itself is a normed ring and `E, F` are normed modules.) -/
@[wikidata Q2342396]
/-
**IsBoundedLinearMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_1) →   {E : Type u_2} →     {F : Type u_3} →       [inst : Sem
iring 𝕜] →         [inst_1 : SeminormedAddCommGroup E] →           [_root_.Modul
e 𝕜 E] → [inst_3 : SeminormedAddCommGroup F] → [_root_.Module 𝕜 F] → (E → F) → P
rop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` satisfies `IsBoundedLinearMap 𝕜 f` if it is linear and satisfies 
the
inequality `‖f x‖ ≤ M * ‖x‖` for some positive constant `M`.

(We put only the typeclasses strictly necessary for the definition, although the
 main case of
interest is when `𝕜` itself is a normed ring and `E, F` are normed modules.)
-/
structure IsBoundedLinearMap : Prop
    extends IsLinearMap 𝕜 f where
  bound : ∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖
/-
**isBoundedLinearMap_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isBoundedLinearMap_iff {f : E -> F} : IsBoundedLinearMap 𝕜 f ↔ IsLinearMap
 𝕜 f ∧ exists M, 0 < M ∧ forall x : E, ‖f x‖ <= M * ‖x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.toIsLinearMap`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_…
· 使用定理 `IsBoundedLinearMap.bound`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_…
-/
lemma isBoundedLinearMap_iff {f : E → F} :
    IsBoundedLinearMap 𝕜 f ↔ IsLinearMap 𝕜 f ∧ ∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖ :=
  ⟨fun hf ↦ ⟨hf.toIsLinearMap, hf.bound⟩, fun ⟨hl, hm⟩ ↦ ⟨hl, hm⟩⟩
/-
**IsLinearMap.with_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearMap.with_bound {f : E -> F} (hf : IsLinearMap 𝕜 f) (M : Real) (h :
 forall x : E, ‖f x‖ <= M * ‖x‖) : IsBoundedLinearMap 𝕜 f
参数：hf : IsLinearMap 𝕜 f；M : Real；h : forall x : E, ‖f x‖ <= M * ‖x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
-/
theorem IsLinearMap.with_bound {f : E → F} (hf : IsLinearMap 𝕜 f) (M : ℝ)
    (h : ∀ x : E, ‖f x‖ ≤ M * ‖x‖) : IsBoundedLinearMap 𝕜 f :=
  ⟨hf,
    by_cases
      (fun (this : M ≤ 0) =>
        ⟨1, zero_lt_one, fun x =>
          (h x).trans <| mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
      fun (this : ¬M ≤ 0) => ⟨M, lt_of_not_ge this, h⟩⟩

namespace IsBoundedLinearMap

/-- Construct a linear map from a function `f` satisfying `IsBoundedLinearMap 𝕜 f`. -/
/-
**IsBoundedLinearMap.toLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：toLinearMap (f : E -> F) (h : IsBoundedLinearMap 𝕜 f) : E ->ₗ[𝕜] F
参数：f : E -> F；h : IsBoundedLinearMap 𝕜 f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.toIsLinearMap`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_…

--- 原说明 ---
Construct a linear map from a function `f` satisfying `IsBoundedLinearMap 𝕜 f`.
-/
def toLinearMap (f : E → F) (h : IsBoundedLinearMap 𝕜 f) : E →ₗ[𝕜] F :=
  IsLinearMap.mk' _ h.toIsLinearMap

/-- Construct a continuous linear map from `IsBoundedLinearMap`. -/
/-
**IsBoundedLinearMap.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `IsBoundedL
inearMap`。
形式化陈述：toContinuousLinearMap (f : E -> F) (hf : IsBoundedLinearMap 𝕜 f) : E ->L[𝕜
] F
参数：f : E -> F；hf : IsBoundedLinearMap 𝕜 f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a continuous linear map from `IsBoundedLinearMap`.
-/
def toContinuousLinearMap (f : E → F) (hf : IsBoundedLinearMap 𝕜 f) : E →L[𝕜] F :=
  { toLinearMap f hf with
    cont :=
      let ⟨C, _, hC⟩ := hf.bound
      AddMonoidHomClass.continuous_of_bound (toLinearMap f hf) C hC }
/-
**IsBoundedLinearMap.zero** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：zero : IsBoundedLinearMap 𝕜 fun _ : E => (0 : F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.with_bound`：IsLinearMap.with_bound {f : E -> F} (hf : IsLine
arMap 𝕜 f) (M : Real) (h : forall x : E, ‖f x‖ <= M * ‖x‖) : IsBoundedLinearMap 
𝕜 f
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem zero : IsBoundedLinearMap 𝕜 fun _ : E => (0 : F) :=
  (0 : E →ₗ[𝕜] F).isLinear.with_bound 0 <| by simp
/-
**IsBoundedLinearMap.id** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：id : IsBoundedLinearMap 𝕜 fun x : E => x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.with_bound`：IsLinearMap.with_bound {f : E -> F} (hf : IsLine
arMap 𝕜 f) (M : Real) (h : forall x : E, ‖f x‖ <= M * ‖x‖) : IsBoundedLinearMap 
𝕜 f
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem id : IsBoundedLinearMap 𝕜 fun x : E => x :=
  LinearMap.id.isLinear.with_bound 1 <| by simp
/-
**IsBoundedLinearMap.fst** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：fst : IsBoundedLinearMap 𝕜 fun x : E × F => x.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.with_bound`：IsLinearMap.with_bound {f : E -> F} (hf : IsLine
arMap 𝕜 f) (M : Real) (h : forall x : E, ‖f x‖ <= M * ‖x‖) : IsBoundedLinearMap 
𝕜 f
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem fst : IsBoundedLinearMap 𝕜 fun x : E × F => x.1 := by
  refine (LinearMap.fst 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_left _ _
/-
**IsBoundedLinearMap.snd** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：snd : IsBoundedLinearMap 𝕜 fun x : E × F => x.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.with_bound`：IsLinearMap.with_bound {f : E -> F} (hf : IsLine
arMap 𝕜 f) (M : Real) (h : forall x : E, ‖f x‖ <= M * ‖x‖) : IsBoundedLinearMap 
𝕜 f
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem snd : IsBoundedLinearMap 𝕜 fun x : E × F => x.2 := by
  refine (LinearMap.snd 𝕜 E F).isLinear.with_bound 1 fun x => ?_
  rw [one_mul]
  exact le_max_right _ _
/-
**IsBoundedLinearMap.smul** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：smul {𝕜' : Type*} (c : 𝕜') [SeminormedRing 𝕜'] [Module 𝕜' F] [IsBoundedSMu
l 𝕜' F] [SMulCommClass 𝕜 𝕜' F] (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMa
p 𝕜 (c • f)
参数：c : 𝕜'；hf : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.with_bound`：IsLinearMap.with_bound {f : E -> F} (hf : IsLine
arMap 𝕜 f) (M : Real) (h : forall x : E, ‖f x‖ <= M * ‖x‖) : IsBoundedLinearMap 
𝕜 f
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem smul {𝕜' : Type*} (c : 𝕜') [SeminormedRing 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
    [SMulCommClass 𝕜 𝕜' F] (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 (c • f) :=
  let ⟨hlf, M, _, hM⟩ := hf
  (c • hlf.mk' f).isLinear.with_bound (‖c‖ * M) fun x =>
    calc
      ‖c • f x‖ ≤ ‖c‖ * ‖f x‖ := norm_smul_le c (f x)
      _ ≤ ‖c‖ * (M * ‖x‖) := by grw [hM]
      _ = ‖c‖ * M * ‖x‖ := (mul_assoc _ _ _).symm
/-
**IsBoundedLinearMap.neg** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：neg (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 fun e => -f e
参数：hf : IsBoundedLinearMap 𝕜 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
· 使用定理 `IsBoundedLinearMap.toIsLinearMap`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `IsBoundedLinearMap.bound`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_…
-/
theorem neg (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 fun e => -f e :=
  ⟨(-hf.1.mk' _).isLinear, by simpa using hf.2⟩
/-
**IsBoundedLinearMap.add** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) : IsBounde
dLinearMap 𝕜 fun e => f e + g e
参数：hf : IsBoundedLinearMap 𝕜 f；hg : IsBoundedLinearMap 𝕜 g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.with_bound`：IsLinearMap.with_bound {f : E -> F} (hf : IsLine
arMap 𝕜 f) (M : Real) (h : forall x : E, ‖f x‖ <= M * ‖x‖) : IsBoundedLinearMap 
𝕜 f
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
· 使用定理 `norm_add_le_of_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a₁ a₂
 : E} {r₁ r₂ : ℝ}, ‖a₁‖ ≤ r₁ → ‖a₂‖ ≤ r₂ → ‖a₁ + a₂‖ ≤ r₁ + r₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e + g e :=
  let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
  (hlf.mk' _ + hlg.mk' _).isLinear.with_bound (Mf + Mg) fun x =>
    calc
      ‖f x + g x‖ ≤ Mf * ‖x‖ + Mg * ‖x‖ := norm_add_le_of_le (hMf x) (hMg x)
      _ ≤ (Mf + Mg) * ‖x‖ := by rw [add_mul]
/-
**IsBoundedLinearMap.sub** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：sub (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) : IsBounde
dLinearMap 𝕜 fun e => f e - g e
参数：hf : IsBoundedLinearMap 𝕜 f；hg : IsBoundedLinearMap 𝕜 g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsBoundedLinearMap.add`：add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBounde
dLinearMap 𝕜 g) : IsBoundedLinearMap 𝕜 fun e => f e + g e
· 使用定理 `IsBoundedLinearMap.neg`：neg (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLin
earMap 𝕜 fun e => -f e
-/
theorem sub (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e - g e := by simpa [sub_eq_add_neg] using add hf (neg hg)
/-
**IsBoundedLinearMap.comp** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：comp {g : F -> G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜
 f) : IsBoundedLinearMap 𝕜 (g ∘ f)
参数：hg : IsBoundedLinearMap 𝕜 g；hf : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.with_bound`：IsLinearMap.with_bound {f : E -> F} (hf : IsLine
arMap 𝕜 f) (M : Real) (h : forall x : E, ‖f x‖ <= M * ‖x‖) : IsBoundedLinearMap 
𝕜 f
· 使用定理 `IsBoundedLinearMap.toIsLinearMap`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_…
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem comp {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 (g ∘ f) :=
  let ⟨hlf, Mf, _, hMf⟩ := hf
  let ⟨hlg, Mg, _, hMg⟩ := hg
  (hg.1.mk' _).comp (hf.1.mk' _) |>.isLinear.with_bound (Mg * Mf) fun x ↦
    show ‖g (f x)‖ ≤ _ by grw [hMg, hMf, mul_assoc]
/-
**IsBoundedLinearMap.tendsto** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Semiring 𝕜] [inst_1
 : SeminormedAddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : Seminormed
AddCommGroup F] [inst_4 : _root_.Module 𝕜 F] {f : E → F} (x : E),   IsBoundedLin
earMap 𝕜 f → Filter.Tendsto f (nhds x) (nhds (f x))
参数：x : E；nhds x；nhds (f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
protected theorem tendsto (x : E) (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  hf.toContinuousLinearMap.continuous.tendsto x
/-
**IsBoundedLinearMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：continuous (hf : IsBoundedLinearMap 𝕜 f) : Continuous f
参数：hf : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem continuous (hf : IsBoundedLinearMap 𝕜 f) : Continuous f :=
  hf.toContinuousLinearMap.continuous
/-
**IsBoundedLinearMap.lim_zero_bounded_linear_map** 是 Mathlib 中的一个定理，位于命名空间 `IsBo
undedLinearMap`。
形式化陈述：lim_zero_bounded_linear_map (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 0
) (𝓝 0)
参数：hf : IsBoundedLinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.toIsLinearMap`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_…
· 使用定理 `IsBoundedLinearMap.tendsto`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root_.Mo
dule 𝕜 E] [inst_…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem lim_zero_bounded_linear_map (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 0) (𝓝 0) :=
  (hf.1.mk' _).map_zero ▸ hf.tendsto 0

section

open Asymptotics Filter

/-
**IsBoundedLinearMap.isBigO_id** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：isBigO_id (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) : f =O[l] fun x => x
参数：h : IsBoundedLinearMap 𝕜 f；l : Filter E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.bound`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3}
 [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root_.Modu
le 𝕜 E] [inst_…
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem isBigO_id (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) : f =O[l] fun x => x :=
  let ⟨_, _, hM⟩ := h.bound
  IsBigO.of_bound _ (mem_of_superset univ_mem fun x _ => hM x)
/-
**IsBoundedLinearMap.isBigO_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：isBigO_comp {E : Type*} {g : F -> G} (hg : IsBoundedLinearMap 𝕜 g) {f : E 
-> F} (l : Filter E) : (fun x' => g (f x')) =O[l] f
参数：hg : IsBoundedLinearMap 𝕜 g；l : Filter E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `IsBoundedLinearMap.isBigO_id`：isBigO_id (h : IsBoundedLinearMap 𝕜 f) (l 
: Filter E) : f =O[l] fun x => x
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem isBigO_comp {E : Type*} {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) {f : E → F}
    (l : Filter E) : (fun x' => g (f x')) =O[l] f :=
  (hg.isBigO_id ⊤).comp_tendsto le_top
/-
**IsBoundedLinearMap.isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：isBigO_sub {f : E -> F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) (x : E
) : (fun x' => f (x' - x)) =O[l] fun x' => x' - x
参数：h : IsBoundedLinearMap 𝕜 f；l : Filter E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedLinearMap.isBigO_comp`：isBigO_comp {E : Type*} {g : F -> G} (hg
 : IsBoundedLinearMap 𝕜 g) {f : E -> F} (l : Filter E) : (fun x' => g (f x')) =O
[l] f
-/
theorem isBigO_sub {f : E → F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  isBigO_comp h l

end

end IsBoundedLinearMap

variable (𝕜) in
/-- A map `f : E × F → G` satisfies `IsBoundedBilinearMap 𝕜 f` if it is bilinear and
continuous. -/
/-
**IsBoundedBilinearMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(𝕜 : Type u_1) →   {E : Type u_2} →     {F : Type u_3} →       {G : Type u
_4} →         [inst : Semiring 𝕜] →           [inst_1 : SeminormedAddCommGroup E
] →             [_root_.Module 𝕜 E] →               [inst_3 : SeminormedAddCommG
roup F] →                 [_root_.Module 𝕜 F] → [inst_5 : SeminormedAddCommGroup
 G] → [_root_.Module 𝕜 G] → (E × F → G) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map `f : E × F → G` satisfies `IsBoundedBilinearMap 𝕜 f` if it is bilinear and
continuous.
-/
structure IsBoundedBilinearMap (f : E × F → G) : Prop where
  add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y)
  smul_left : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
  add_right : ∀ (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂)
  smul_right : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)
  bound : ∃ C > 0, ∀ (x : E) (y : F), ‖f (x, y)‖ ≤ C * ‖x‖ * ‖y‖

namespace IsBoundedBilinearMap

variable {f : E × F → G}

/-
**IsBoundedBilinearMap.symm** 是 Mathlib 中的一个引理，位于命名空间 `IsBoundedBilinearMap`。
形式化陈述：symm (h : IsBoundedBilinearMap 𝕜 f) : IsBoundedBilinearMap 𝕜 (fun p => f (
p.2, p.1)) where add_left x₁ x₂ y
参数：h : IsBoundedBilinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedBilinearMap.add_right`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   
[inst_2 : _root_.Mod…
· 使用定理 `IsBoundedBilinearMap.smul_right`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Ty
pe u_3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]  
 [inst_2 : _root_.Mod…
· 使用定理 `IsBoundedBilinearMap.add_left`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type
 u_3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [
inst_2 : _root_.Mod…
· 使用定理 `IsBoundedBilinearMap.smul_left`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   
[inst_2 : _root_.Mod…
· 使用定理 `IsBoundedBilinearMap.bound`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [ins
t_2 : _root_.Mod…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
-/
lemma symm (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedBilinearMap 𝕜 (fun p ↦ f (p.2, p.1)) where
  add_left x₁ x₂ y := h.add_right _ _ _
  smul_left c x y := h.smul_right _ _ _
  add_right x y₁ y₂ := h.add_left _ _ _
  smul_right c x y := h.smul_left _ _ _
  bound := by
    obtain ⟨C, hC_pos, hC⟩ := h.bound
    exact ⟨C, hC_pos, fun x y ↦ (hC y x).trans_eq (by ring)⟩
/-
**IsBoundedBilinearMap.isBoundedLinearMap_right** 是 Mathlib 中的一个引理，位于命名空间 `IsBou
ndedBilinearMap`。
形式化陈述：isBoundedLinearMap_right (h : IsBoundedBilinearMap 𝕜 f) (x : E) : IsBounde
dLinearMap 𝕜 (fun y => f (x, y)) where map_add
参数：h : IsBoundedBilinearMap 𝕜 f；x : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedBilinearMap.add_right`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   
[inst_2 : _root_.Mod…
· 使用定理 `IsBoundedBilinearMap.smul_right`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Ty
pe u_3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]  
 [inst_2 : _root_.Mod…
· 使用定理 `IsBoundedBilinearMap.bound`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [ins
t_2 : _root_.Mod…
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `lt_max_of_lt_right`：lt_max_of_lt_right (h : a < c) : a < max b c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `max_cases`：∀ {α : Type u} [inst : LinearOrder α] (a b : α), max a b = a 
∧ b ≤ a ∨ max a b = b ∧ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
lemma isBoundedLinearMap_right (h : IsBoundedBilinearMap 𝕜 f) (x : E) :
    IsBoundedLinearMap 𝕜 (fun y ↦ f (x, y)) where
  map_add := h.add_right x
  map_smul := (h.smul_right · x ·)
  bound := by
    let ⟨C, hC_pos, hC⟩ := h.bound
    -- Using `C * ‖x‖` is tempting but `x` might be 0 and the constant must be positive!
    refine ⟨C * max ‖x‖ 1, by positivity, fun y ↦ (hC x y).trans ?_⟩
    rcases max_cases ‖x‖ 1 with hx | hx
    · grw [hx.1]
    · grw [hx.1, hx.2.le]
/-
**IsBoundedBilinearMap.isBoundedLinearMap_left** 是 Mathlib 中的一个引理，位于命名空间 `IsBoun
dedBilinearMap`。
形式化陈述：isBoundedLinearMap_left (h : IsBoundedBilinearMap 𝕜 f) (y : F) : IsBounded
LinearMap 𝕜 (fun x => f (x, y))
参数：h : IsBoundedBilinearMap 𝕜 f；y : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBoundedBilinearMap.isBoundedLinearMap_right`：isBoundedLinearMap_right 
(h : IsBoundedBilinearMap 𝕜 f) (x : E) : IsBoundedLinearMap 𝕜 (fun y => f (x, y)
) where map_add
· 使用引理 `IsBoundedBilinearMap.symm`：symm (h : IsBoundedBilinearMap 𝕜 f) : IsBound
edBilinearMap 𝕜 (fun p => f (p.2, p.1)) where add_left x₁ x₂ y
-/
lemma isBoundedLinearMap_left (h : IsBoundedBilinearMap 𝕜 f) (y : F) :
    IsBoundedLinearMap 𝕜 (fun x ↦ f (x, y)) :=
  h.symm.isBoundedLinearMap_right y
/-
**IsBoundedBilinearMap.map_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedBilinear
Map`。
形式化陈述：map_sub_left (h : IsBoundedBilinearMap 𝕜 f) {x y : E} {z : F} : f (x - y, 
z) = f (x, z) - f (y, z)
参数：h : IsBoundedBilinearMap 𝕜 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.map_sub`：map_sub {f : M -> M₂} (lin : IsLinearMap R f) (x y 
: M) : f (x - y) = f x - f y
· 使用定理 `IsBoundedLinearMap.toIsLinearMap`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_…
· 使用引理 `IsBoundedBilinearMap.isBoundedLinearMap_left`：isBoundedLinearMap_left (h
 : IsBoundedBilinearMap 𝕜 f) (y : F) : IsBoundedLinearMap 𝕜 (fun x => f (x, y))
-/
theorem map_sub_left (h : IsBoundedBilinearMap 𝕜 f) {x y : E} {z : F} :
    f (x - y, z) = f (x, z) - f (y, z) :=
  (h.isBoundedLinearMap_left z).map_sub x y
/-
**IsBoundedBilinearMap.map_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedBilinea
rMap`。
形式化陈述：map_sub_right (h : IsBoundedBilinearMap 𝕜 f) {x : E} {y z : F} : f (x, y -
 z) = f (x, y) - f (x, z)
参数：h : IsBoundedBilinearMap 𝕜 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.map_sub`：map_sub {f : M -> M₂} (lin : IsLinearMap R f) (x y 
: M) : f (x - y) = f x - f y
· 使用定理 `IsBoundedLinearMap.toIsLinearMap`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_…
· 使用引理 `IsBoundedBilinearMap.isBoundedLinearMap_right`：isBoundedLinearMap_right 
(h : IsBoundedBilinearMap 𝕜 f) (x : E) : IsBoundedLinearMap 𝕜 (fun y => f (x, y)
) where map_add
-/
theorem map_sub_right (h : IsBoundedBilinearMap 𝕜 f) {x : E} {y z : F} :
    f (x, y - z) = f (x, y) - f (x, z) :=
  (h.isBoundedLinearMap_right x).map_sub y z
/-
**IsBoundedBilinearMap.isBigO** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedBilinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Semi
ring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst
_3 : SeminormedAddCommGroup F] [inst_4 : _root_.Module 𝕜 F]   [inst_5 : Seminorm
edAddCommGroup G] [inst_6 : _root_.Module 𝕜 G] {f : E × F → G},   IsBoundedBilin
earMap 𝕜 f → f =O[⊤] fun p => ‖p.1‖ * ‖p.2‖
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedBilinearMap.bound`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_
3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [ins
t_2 : _root_.Mod…
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
protected theorem isBigO (h : IsBoundedBilinearMap 𝕜 f) :
    f =O[⊤] fun p : E × F => ‖p.1‖ * ‖p.2‖ :=
  let ⟨C, _, hC⟩ := h.bound
  Asymptotics.IsBigO.of_bound C <|
    Filter.Eventually.of_forall fun ⟨x, y⟩ => by simpa [mul_assoc] using hC x y
/-
**IsBoundedBilinearMap.isBigO_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedBilinearM
ap`。
形式化陈述：isBigO_comp {α : Type*} (H : IsBoundedBilinearMap 𝕜 f) {g : α -> E} {h : α
 -> F} {l : Filter α} : (fun x => f (g x, h x)) =O[l] fun x => ‖g x‖ * ‖h x‖
参数：H : IsBoundedBilinearMap 𝕜 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `IsBoundedBilinearMap.isBigO`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [in
st_2 : _root_.Mod…
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem isBigO_comp {α : Type*} (H : IsBoundedBilinearMap 𝕜 f) {g : α → E}
    {h : α → F} {l : Filter α} : (fun x => f (g x, h x)) =O[l] fun x => ‖g x‖ * ‖h x‖ :=
  H.isBigO.comp_tendsto le_top
/-
**IsBoundedBilinearMap.isBigO'** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedBilinearMap`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Type u_4} [inst : Semi
ring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst
_3 : SeminormedAddCommGroup F] [inst_4 : _root_.Module 𝕜 F]   [inst_5 : Seminorm
edAddCommGroup G] [inst_6 : _root_.Module 𝕜 G] {f : E × F → G},   IsBoundedBilin
earMap 𝕜 f → f =O[⊤] fun p => ‖p‖ * ‖p‖
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `IsBoundedBilinearMap.isBigO`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} {G : Type u_4} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [in
st_2 : _root_.Mod…
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.IsBigO.norm_norm`：∀ {α : Type u_1} {E' : Type u_6} {F' : Typ
e u_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F']  
 {f' : α → E'} {g'…
· 使用定理 `Asymptotics.isBigO_fst_prod'`：isBigO_fst_prod' {f' : α -> E' × F'} : (fu
n x => (f' x).1) =O[l] f'
· 使用定理 `Asymptotics.isBigO_snd_prod'`：isBigO_snd_prod' {f' : α -> E' × F'} : (fu
n x => (f' x).2) =O[l] f'
-/
protected theorem isBigO' (h : IsBoundedBilinearMap 𝕜 f) :
    f =O[⊤] fun p : E × F => ‖p‖ * ‖p‖ :=
  h.isBigO.trans <|
    (@Asymptotics.isBigO_fst_prod' _ E F _ _ _ _).norm_norm.mul
      (@Asymptotics.isBigO_snd_prod' _ E F _ _ _ _).norm_norm

open Asymptotics in
/-- Useful to use together with `Continuous.comp₂`. -/
/-
**IsBoundedBilinearMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedBilinearMa
p`。
形式化陈述：continuous (h : IsBoundedBilinearMap 𝕜 f) : Continuous f
参数：h : IsBoundedBilinearMap 𝕜 f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_sub_nhds_zero_iff`：∀ {G : Type w} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] [IsTopologicalAddGroup G] {α : Type u_1} {l : Filter α}   {x
 : G} {u : α → …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `IsBoundedBilinearMap.isBigO_comp`：isBigO_comp {α : Type*} (H : IsBounded
BilinearMap 𝕜 f) {g : α -> E} {h : α -> F} {l : Filter α} : (fun x => f (g x, h 
x)) =O[l] fun x => ‖g …
· 使用定理 `Asymptotics.IsLittleO.mul_isBigO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.IsLittleO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' 
: α → E'} {l : Filter…
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
· 使用定理 `Filter.Tendsto.isBigO_one`：∀ {α : Type u_1} (F : Type u_4) {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {f' : α → E'}   {l : Fil
ter α} [inst_2 …
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `Asymptotics.IsLittleO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R
 : Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filte
r α}   {f : α → R}, f =o[l…
· 使用定理 `Asymptotics.isLittleO_norm_left`：isLittleO_norm_left : (fun x => ‖f' x‖)
 =o[l] g ↔ f' =o[l] g
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ContinuousAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Useful to use together with `Continuous.comp₂`.
-/
theorem continuous (h : IsBoundedBilinearMap 𝕜 f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x ↦ tendsto_sub_nhds_zero_iff.1 ?_
  suffices Tendsto (fun y : E × F ↦ f (y.1 - x.1, y.2) + f (x.1, y.2 - x.2)) (𝓝 x) (𝓝 (0 + 0)) by
    simpa only [h.map_sub_left, h.map_sub_right, sub_add_sub_cancel, zero_add] using this
  apply Tendsto.add
  · rw [← isLittleO_one_iff ℝ, ← one_mul 1]
    refine h.isBigO_comp.trans_isLittleO ?_
    refine (IsLittleO.norm_left ?_).mul_isBigO (IsBigO.norm_left ?_)
    · exact (isLittleO_one_iff _).2 (tendsto_sub_nhds_zero_iff.2 (continuous_fst.tendsto _))
    · exact (continuous_snd.tendsto _).isBigO_one ℝ
  · rw [← isLittleO_one_iff ℝ]
    refine h.isBigO_comp.trans_isLittleO ?_
    apply IsLittleO.const_mul_left
    rw [isLittleO_norm_left, isLittleO_one_iff, ← sub_self x.2]
    exact continuous_snd.continuousAt.sub tendsto_const_nhds
/-
**IsBoundedBilinearMap.continuous_left** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedBilin
earMap`。
形式化陈述：continuous_left (h : IsBoundedBilinearMap 𝕜 f) {e₂ : F} : Continuous fun e
₁ => f (e₁, e₂)
参数：h : IsBoundedBilinearMap 𝕜 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `IsBoundedBilinearMap.continuous`：continuous (h : IsBoundedBilinearMap 𝕜 
f) : Continuous f
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem continuous_left (h : IsBoundedBilinearMap 𝕜 f) {e₂ : F} :
    Continuous fun e₁ => f (e₁, e₂) :=
  h.continuous.comp (by fun_prop)
/-
**IsBoundedBilinearMap.continuous_right** 是 Mathlib 中的一个定理，位于命名空间 `IsBoundedBili
nearMap`。
形式化陈述：continuous_right (h : IsBoundedBilinearMap 𝕜 f) {e₁ : E} : Continuous fun 
e₂ => f (e₁, e₂)
参数：h : IsBoundedBilinearMap 𝕜 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `IsBoundedBilinearMap.continuous`：continuous (h : IsBoundedBilinearMap 𝕜 
f) : Continuous f
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
theorem continuous_right (h : IsBoundedBilinearMap 𝕜 f) {e₁ : E} :
    Continuous fun e₂ => f (e₁, e₂) :=
  h.continuous.comp (by fun_prop)

end IsBoundedBilinearMap

end Semiring

section CommSemiring

variable {𝕜 A : Type*} [CommSemiring 𝕜] [SeminormedRing A] [Algebra 𝕜 A]

/-- Scalar multiplication (for a normed `𝕜`-algebra acting on a normed `𝕜`-module) as a bounded
bilinear map. -/
/-
**isBoundedBilinearMap_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBoundedBilinearMap_smul {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜
 E] [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] : IsBoundedBilinearMa
p 𝕜 fun p : A × E => p.1 • p.2 where add_left
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Scalar multiplication (for a normed `𝕜`-algebra acting on a normed `𝕜`-module) a
s a bounded
bilinear map.
-/
theorem isBoundedBilinearMap_smul {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E]
    [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] :
    IsBoundedBilinearMap 𝕜 fun p : A × E ↦ p.1 • p.2 where
  add_left := add_smul
  add_right := smul_add
  smul_left := smul_assoc
  smul_right c x := smul_comm x c
  bound := ⟨1, one_pos, fun x y ↦ by grw [one_mul, norm_smul_le]⟩

/-- Multiplication in a normed `𝕜`-algebra as a bounded bilinear map. -/
/-
**isBoundedBilinearMap_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBoundedBilinearMap_mul : IsBoundedBilinearMap 𝕜 fun p : A × A => p.1 * p
.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isBoundedBilinearMap_smul`：isBoundedBilinearMap_smul {E : Type*} [Semino
rmedAddCommGroup E] [Module 𝕜 E] [Module A E] [IsBoundedSMul A E] [IsScalarTower
 𝕜 A E] : IsBou…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Multiplication in a normed `𝕜`-algebra as a bounded bilinear map.
-/
theorem isBoundedBilinearMap_mul :
    IsBoundedBilinearMap 𝕜 fun p : A × A ↦ p.1 * p.2 :=
  isBoundedBilinearMap_smul

end CommSemiring

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*}
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A continuous linear map satisfies `IsBoundedLinearMap` -/
/-
**ContinuousLinearMap.isBoundedLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.isBoundedLinearMap (f : E ->L[𝕜] F) : IsBoundedLinearM
ap 𝕜 f
参数：f : E ->L[𝕜] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
· 使用定理 `ContinuousLinearMap.bound`：bound [RingHomIsometric σ₁₂] (f : E ->SL[σ₁₂]
 F) : exists C, 0 < C ∧ forall x : E, ‖f x‖ <= C * ‖x‖

--- 原说明 ---
A continuous linear map satisfies `IsBoundedLinearMap`
-/
theorem ContinuousLinearMap.isBoundedLinearMap (f : E →L[𝕜] F) : IsBoundedLinearMap 𝕜 f :=
  { f.toLinearMap.isLinear with bound := f.bound }

namespace IsBoundedLinearMap

variable {f g : E → F}

/-- A map between normed spaces is linear and continuous if and only if it is bounded. -/
/-
**IsBoundedLinearMap.isLinearMap_and_continuous_iff_isBoundedLinearMap** 是 Mathl
ib 中的一个定理，位于命名空间 `IsBoundedLinearMap`。
形式化陈述：isLinearMap_and_continuous_iff_isBoundedLinearMap (f : E -> F) : IsLinearM
ap 𝕜 f ∧ Continuous f ↔ IsBoundedLinearMap 𝕜 f where mp | ⟨hlin, hcont⟩ => Conti
nuousLinearMap.isBoundedLinearMap ⟨hlin.mk' _, hcont⟩ mpr h_bdd
参数：f : E -> F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBoundedLinearMap`：ContinuousLinearMap.isBoundedLin
earMap (f : E ->L[𝕜] F) : IsBoundedLinearMap 𝕜 f
· 使用定理 `IsBoundedLinearMap.toIsLinearMap`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : T
ype u_3} [inst : Semiring 𝕜] [inst_1 : SeminormedAddCommGroup E]   [inst_2 : _ro
ot_.Module 𝕜 E] [inst_…
· 使用定理 `IsBoundedLinearMap.continuous`：continuous (hf : IsBoundedLinearMap 𝕜 f) 
: Continuous f

--- 原说明 ---
A map between normed spaces is linear and continuous if and only if it is bounde
d.
-/
theorem isLinearMap_and_continuous_iff_isBoundedLinearMap (f : E → F) :
    IsLinearMap 𝕜 f ∧ Continuous f ↔ IsBoundedLinearMap 𝕜 f where
  mp | ⟨hlin, hcont⟩ => ContinuousLinearMap.isBoundedLinearMap ⟨hlin.mk' _, hcont⟩
  mpr h_bdd := ⟨h_bdd.toIsLinearMap, h_bdd.continuous⟩

end IsBoundedLinearMap

section

variable {ι : Type*} [Fintype ι]

/-- Taking the Cartesian product of two continuous multilinear maps is a bounded linear
operation. -/
/-
**isBoundedLinearMap_prod_multilinear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBoundedLinearMap_prod_multilinear {E : ι -> Type*} [forall i, Seminormed
AddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)] : IsBoundedLinearMap 𝕜 fun p
 : ContinuousMultilinearMap 𝕜 E F × ContinuousMultilinearMap 𝕜 E G => p.1.prod p
.2
参数：E i；E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBoundedLinearMap`：ContinuousLinearMap.isBoundedLin
earMap (f : E ->L[𝕜] F) : IsBoundedLinearMap 𝕜 f
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

--- 原说明 ---
Taking the Cartesian product of two continuous multilinear maps is a bounded lin
ear
operation.
-/
theorem isBoundedLinearMap_prod_multilinear {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] :
    IsBoundedLinearMap 𝕜 fun p : ContinuousMultilinearMap 𝕜 E F × ContinuousMultilinearMap 𝕜 E G =>
      p.1.prod p.2 :=
  (ContinuousMultilinearMap.prodL 𝕜 E F G).toContinuousLinearEquiv
    |>.toContinuousLinearMap.isBoundedLinearMap

/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
/-
**isBoundedLinearMap_continuousMultilinearMap_comp_linear** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：isBoundedLinearMap_continuousMultilinearMap_comp_linear (g : G ->L[𝕜] E) :
 IsBoundedLinearMap 𝕜 fun f : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F => f
.compContinuousLinearMap fun _ => g
参数：g : G ->L[𝕜] E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBoundedLinearMap`：ContinuousLinearMap.isBoundedLin
earMap (f : E ->L[𝕜] F) : IsBoundedLinearMap 𝕜 f
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …

--- 原说明 ---
Given a fixed continuous linear map `g`, associating to a continuous multilinear
 map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation.
-/
theorem isBoundedLinearMap_continuousMultilinearMap_comp_linear (g : G →L[𝕜] E) :
    IsBoundedLinearMap 𝕜 fun f : ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F =>
      f.compContinuousLinearMap fun _ => g :=
  (ContinuousMultilinearMap.compContinuousLinearMapL (ι := ι) (F := F) (fun _ ↦ g))
    |>.isBoundedLinearMap

end

section BilinearMap

variable {f : E × F → G}

/-
**ContinuousLinearMap.isBoundedBilinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.isBoundedBilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBou
ndedBilinearMap 𝕜 fun x : E × F => f x.1 x.2
参数：f : E ->L[𝕜] F ->L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.map_add₂`：map_add₂ (f : E ->SL[σ₁₃] F ->SL[σ₂₃] G) (
x x' : E) (y : F) : f (x + x') y = f x y + f x' y
· 使用定理 `ContinuousLinearMap.map_smul₂`：map_smul₂ (f : E ->L[𝕜₃] F ->SL[σ₂₃] G) (
c : 𝕜₃) (x : E) (y : F) : f (c • x) y = c • f x y
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ContinuousLinearMap.le_opNorm₂`：le_opNorm₂ [RingHomIsometric σ₁₃] (f : E
 ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : ‖f x y‖ <= ‖f‖ * ‖x‖ * ‖y‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem ContinuousLinearMap.isBoundedBilinearMap (f : E →L[𝕜] F →L[𝕜] G) :
    IsBoundedBilinearMap 𝕜 fun x : E × F => f x.1 x.2 :=
  { add_left := f.map_add₂
    smul_left := f.map_smul₂
    add_right := fun x => (f x).map_add
    smul_right := fun c x => (f x).map_smul c
    bound :=
      ⟨max ‖f‖ 1, zero_lt_one.trans_le (le_max_right _ _), fun x y =>
        (f.le_opNorm₂ x y).trans <| by
          gcongr; apply le_max_left ⟩ }

/-- A bounded bilinear map `f : E × F → G` defines a continuous linear map
`f : E →L[𝕜] F →L[𝕜] G`. -/
/-
**IsBoundedBilinearMap.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.toContinuousLinearMap (hf : IsBoundedBilinearMap 𝕜 f)
 : E ->L[𝕜] F ->L[𝕜] G
参数：hf : IsBoundedBilinearMap 𝕜 f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bounded bilinear map `f : E × F → G` defines a continuous linear map
`f : E →L[𝕜] F →L[𝕜] G`.
-/
def IsBoundedBilinearMap.toContinuousLinearMap (hf : IsBoundedBilinearMap 𝕜 f) :
    E →L[𝕜] F →L[𝕜] G :=
  LinearMap.mkContinuousOfExistsBound₂
    (LinearMap.mk₂ _ f.curry hf.add_left hf.smul_left hf.add_right hf.smul_right) <|
    hf.bound.imp fun _ ↦ And.right

@[simp]
/-
**IsBoundedBilinearMap.toContinuousLinearMap_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.toContinuousLinearMap_apply (hf : IsBoundedBilinearMa
p 𝕜 f) (x : E) (y : F) : hf.toContinuousLinearMap x y = f (x, y)
参数：hf : IsBoundedBilinearMap 𝕜 f；x : E；y : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma IsBoundedBilinearMap.toContinuousLinearMap_apply (hf : IsBoundedBilinearMap 𝕜 f)
    (x : E) (y : F) : hf.toContinuousLinearMap x y = f (x, y) := rfl

/-- Useful to use together with `Continuous.comp₂`. -/
/-
**ContinuousLinearMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`
。
形式化陈述：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Semiring R₁] [inst_1 : Semiring 
R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 : TopologicalSpace M₁] [inst_3 :
 AddCommMonoid M₁] {M₂ : Type u_6} [inst_4 : TopologicalSpace M₂]   [inst_5 : Ad
dCommMonoid M₂] [inst_6 : _root_.Module R₁ M₁] [inst_7 : _root_.Module R₂ M₂] (f
 : M₁ →SL[σ₁₂] M₂),   Continuous ⇑f
参数：f : M₁ →SL[σ₁₂] M₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…

--- 原说明 ---
Useful to use together with `Continuous.comp₂`.
-/
theorem ContinuousLinearMap.continuous₂ (f : E →L[𝕜] F →L[𝕜] G) :
    Continuous (Function.uncurry fun x y => f x y) :=
  f.isBoundedBilinearMap.continuous
/-
**isBoundedBilinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBoundedBilinearMap_comp : IsBoundedBilinearMap 𝕜 fun p : (F ->L[𝕜] G) × 
(E ->L[𝕜] F) => p.1.comp p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
-/
theorem isBoundedBilinearMap_comp :
    IsBoundedBilinearMap 𝕜 fun p : (F →L[𝕜] G) × (E →L[𝕜] F) => p.1.comp p.2 :=
  (compL 𝕜 E F G).isBoundedBilinearMap
/-
**ContinuousLinearMap.isBoundedLinearMap_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.isBoundedLinearMap_comp_left (g : F ->L[𝕜] G) : IsBoun
dedLinearMap 𝕜 fun f : E ->L[𝕜] F => ContinuousLinearMap.comp g f
参数：g : F ->L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBoundedBilinearMap.isBoundedLinearMap_right`：isBoundedLinearMap_right 
(h : IsBoundedBilinearMap 𝕜 f) (x : E) : IsBoundedLinearMap 𝕜 (fun y => f (x, y)
) where map_add
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `isBoundedBilinearMap_comp`：isBoundedBilinearMap_comp : IsBoundedBilinear
Map 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2
-/
theorem ContinuousLinearMap.isBoundedLinearMap_comp_left (g : F →L[𝕜] G) :
    IsBoundedLinearMap 𝕜 fun f : E →L[𝕜] F => ContinuousLinearMap.comp g f :=
  isBoundedBilinearMap_comp.isBoundedLinearMap_right g
/-
**ContinuousLinearMap.isBoundedLinearMap_comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：ContinuousLinearMap.isBoundedLinearMap_comp_right (f : E ->L[𝕜] F) : IsBou
ndedLinearMap 𝕜 fun g : F ->L[𝕜] G => ContinuousLinearMap.comp g f
参数：f : E ->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBoundedBilinearMap.isBoundedLinearMap_left`：isBoundedLinearMap_left (h
 : IsBoundedBilinearMap 𝕜 f) (y : F) : IsBoundedLinearMap 𝕜 (fun x => f (x, y))
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `isBoundedBilinearMap_comp`：isBoundedBilinearMap_comp : IsBoundedBilinear
Map 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2
-/
theorem ContinuousLinearMap.isBoundedLinearMap_comp_right (f : E →L[𝕜] F) :
    IsBoundedLinearMap 𝕜 fun g : F →L[𝕜] G => ContinuousLinearMap.comp g f :=
  (isBoundedBilinearMap_comp (G := G)).isBoundedLinearMap_left f
/-
**isBoundedBilinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBoundedBilinearMap_apply : IsBoundedBilinearMap 𝕜 fun p : (E ->L[𝕜] F) ×
 E => p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
-/
theorem isBoundedBilinearMap_apply : IsBoundedBilinearMap 𝕜 fun p : (E →L[𝕜] F) × E => p.1 p.2 :=
  (ContinuousLinearMap.flip (apply 𝕜 F : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F)).isBoundedBilinearMap

/-- The function `ContinuousLinearMap.smulRight`, associating to a continuous linear map
`f : E → 𝕜` and a scalar `c : F` the tensor product `f ⊗ c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
/-
**isBoundedBilinearMap_smulRight** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBoundedBilinearMap_smulRight : IsBoundedBilinearMap 𝕜 fun p => (Continuo
usLinearMap.smulRight : StrongDual 𝕜 E -> F -> E ->L[𝕜] F) p.1 p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
The function `ContinuousLinearMap.smulRight`, associating to a continuous linear
 map
`f : E → 𝕜` and a scalar `c : F` the tensor product `f ⊗ c` as a continuous line
ar map from `E` to
`F`, is a bounded bilinear map.
-/
theorem isBoundedBilinearMap_smulRight :
    IsBoundedBilinearMap 𝕜 fun p =>
      (ContinuousLinearMap.smulRight : StrongDual 𝕜 E → F → E →L[𝕜] F) p.1 p.2 :=
  (smulRightL 𝕜 E F).isBoundedBilinearMap

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
/-
**isBoundedBilinearMap_compMultilinear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBoundedBilinearMap_compMultilinear {ι : Type*} {E : ι -> Type*} [Fintype
 ι] [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)] : IsBou
ndedBilinearMap 𝕜 fun p : (F ->L[𝕜] G) × ContinuousMultilinearMap 𝕜 E F => p.1.c
ompContinuousMultilinearMap p.2
参数：E i；E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …

--- 原说明 ---
The composition of a continuous linear map with a continuous multilinear map is 
a bounded
bilinear operation.
-/
theorem isBoundedBilinearMap_compMultilinear {ι : Type*} {E : ι → Type*} [Fintype ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    IsBoundedBilinearMap 𝕜 fun p : (F →L[𝕜] G) × ContinuousMultilinearMap 𝕜 E F =>
      p.1.compContinuousMultilinearMap p.2 :=
  (compContinuousMultilinearMapL 𝕜 E F G).isBoundedBilinearMap

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here as a linear map `E × F →ₗ[𝕜] G`, then `IsBoundedBilinearMap.deriv`
strengthens it to a continuous linear map `E × F →L[𝕜] G`.
-/
/-
**IsBoundedBilinearMap.linearDeriv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.linearDeriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F
) : E × F ->ₗ[𝕜] G
参数：h : IsBoundedBilinearMap 𝕜 f；p : E × F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of
 a product.
We define this function here as a linear map `E × F →ₗ[𝕜] G`, then `IsBoundedBil
inearMap.deriv`
strengthens it to a continuous linear map `E × F →L[𝕜] G`.
-/
def IsBoundedBilinearMap.linearDeriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →ₗ[𝕜] G :=
  (h.toContinuousLinearMap.deriv₂ p).toLinearMap

/-- The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous linear map
from `E × F` to `G`. The statement that this is indeed the derivative of `f` is
`IsBoundedBilinearMap.hasFDerivAt` in `Analysis.Calculus.FDeriv`. -/
/-
**IsBoundedBilinearMap.deriv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.deriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E 
× F ->L[𝕜] G
参数：h : IsBoundedBilinearMap 𝕜 f；p : E × F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous
 linear map
from `E × F` to `G`. The statement that this is indeed the derivative of `f` is
`IsBoundedBilinearMap.hasFDerivAt` in `Analysis.Calculus.FDeriv`.
-/
def IsBoundedBilinearMap.deriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →L[𝕜] G :=
  h.toContinuousLinearMap.deriv₂ p

@[simp]
/-
**IsBoundedBilinearMap.deriv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.deriv_apply (h : IsBoundedBilinearMap 𝕜 f) (p q : E ×
 F) : h.deriv p q = f (p.1, q.2) + f (q.1, p.2)
参数：h : IsBoundedBilinearMap 𝕜 f；p q : E × F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsBoundedBilinearMap.deriv_apply (h : IsBoundedBilinearMap 𝕜 f) (p q : E × F) :
    h.deriv p q = f (p.1, q.2) + f (q.1, p.2) :=
  rfl

variable (𝕜) in
/-- The function `ContinuousLinearMap.mulLeftRight : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a bounded
bilinear map. -/
/-
**ContinuousLinearMap.mulLeftRight_isBoundedBilinear** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：ContinuousLinearMap.mulLeftRight_isBoundedBilinear (𝕜' : Type*) [Seminorme
dRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] : IsBoundedBilinearMap 𝕜 fun p : 𝕜' × 𝕜' => Conti
nuousLinearMap.mulLeftRight 𝕜 𝕜' p.1 p.2
参数：𝕜' : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBoundedBilinearMap`：ContinuousLinearMap.isBoundedB
ilinearMap (f : E ->L[𝕜] F ->L[𝕜] G) : IsBoundedBilinearMap 𝕜 fun x : E × F => f
 x.1 x.2
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
The function `ContinuousLinearMap.mulLeftRight : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a b
ounded
bilinear map.
-/
theorem ContinuousLinearMap.mulLeftRight_isBoundedBilinear (𝕜' : Type*) [SeminormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] :
    IsBoundedBilinearMap 𝕜 fun p : 𝕜' × 𝕜' => ContinuousLinearMap.mulLeftRight 𝕜 𝕜' p.1 p.2 :=
  (ContinuousLinearMap.mulLeftRight 𝕜 𝕜').isBoundedBilinearMap

/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
/-
**IsBoundedBilinearMap.isBoundedLinearMap_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBoundedBilinearMap.isBoundedLinearMap_deriv (h : IsBoundedBilinearMap 𝕜 
f) : IsBoundedLinearMap 𝕜 fun p : E × F => h.deriv p
参数：h : IsBoundedBilinearMap 𝕜 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.isBoundedLinearMap`：ContinuousLinearMap.isBoundedLin
earMap (f : E ->L[𝕜] F) : IsBoundedLinearMap 𝕜 f

--- 原说明 ---
Given a bounded bilinear map `f`, the map associating to a point `p` the derivat
ive of `f` at
`p` is itself a bounded linear map.
-/
theorem IsBoundedBilinearMap.isBoundedLinearMap_deriv (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 fun p : E × F => h.deriv p :=
  h.toContinuousLinearMap.deriv₂.isBoundedLinearMap

end BilinearMap

variable {X : Type*} [TopologicalSpace X]

@[continuity, fun_prop]
/-
**Continuous.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} (hg : Cont
inuous g) (hf : Continuous f) : Continuous fun x => (g x).comp (f x)
参数：hg : Continuous g；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.comp₂`：Continuous.comp₂ {g : X × Y -> Z} (hg : Continuous g) 
{e : W -> X} (he : Continuous e) {f : W -> Y} (hf : Continuous f) : Continuous f
un w =…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.continuous₂`：ContinuousLinearMap.continuous₂ (f : E 
->L[𝕜] F ->L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y)
-/
theorem Continuous.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    (hg : Continuous g) (hf : Continuous f) : Continuous fun x => (g x).comp (f x) :=
  (compL 𝕜 E F G).continuous₂.comp₂ hg hf

@[fun_prop]
/-
**ContinuousOn.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {s : Set
 X} (hg : ContinuousOn g s) (hf : ContinuousOn f s) : ContinuousOn (fun x => (g 
x).comp (f x)) s
参数：hg : ContinuousOn g s；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.continuous₂`：ContinuousLinearMap.continuous₂ (f : E 
->L[𝕜] F ->L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y)
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
-/
theorem ContinuousOn.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    {s : Set X} (hg : ContinuousOn g s) (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (g x).comp (f x)) s :=
  (compL 𝕜 E F G).continuous₂.comp_continuousOn (hg.prodMk hf)

@[fun_prop]
/-
**ContinuousAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {x : X} 
(hg : ContinuousAt g x) (hf : ContinuousAt f x) : ContinuousAt (fun x => (g x).c
omp (f x)) x
参数：hg : ContinuousAt g x；hf : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousLinearMap.continuous₂`：ContinuousLinearMap.continuous₂ (f : E 
->L[𝕜] F ->L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y)
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
-/
theorem ContinuousAt.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    {x : X} (hg : ContinuousAt g x) (hf : ContinuousAt f x) :
    ContinuousAt (fun x => (g x).comp (f x)) x :=
  (compL 𝕜 E F G).continuous₂.continuousAt.comp (hg.prodMk hf)

@[fun_prop]
/-
**ContinuousWithinAt.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {s
 : Set X} {x : X} (hg : ContinuousWithinAt g s x) (hf : ContinuousWithinAt f s x
) : ContinuousWithinAt (fun x => (g x).comp (f x)) s x
参数：hg : ContinuousWithinAt g s x；hf : ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousLinearMap.continuous₂`：ContinuousLinearMap.continuous₂ (f : E 
->L[𝕜] F ->L[𝕜] G) : Continuous (Function.uncurry fun x y => f x y)
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
-/
theorem ContinuousWithinAt.clm_comp {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    {s : Set X} {x : X} (hg : ContinuousWithinAt g s x) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (g x).comp (f x)) s x :=
  (compL 𝕜 E F G).continuous₂.continuousAt.comp_continuousWithinAt (hg.prodMk hf)

@[continuity, fun_prop]
/-
**Continuous.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.clm_apply {f : X -> E ->L[𝕜] F} {g : X -> E} (hf : Continuous f
) (hg : Continuous g) : Continuous (fun x => f x (g x))
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.comp₂`：Continuous.comp₂ {g : X × Y -> Z} (hg : Continuous g) 
{e : W -> X} (he : Continuous e) {f : W -> Y} (hf : Continuous f) : Continuous f
un w =…
· 使用定理 `IsBoundedBilinearMap.continuous`：continuous (h : IsBoundedBilinearMap 𝕜 
f) : Continuous f
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
-/
theorem Continuous.clm_apply {f : X → E →L[𝕜] F} {g : X → E}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x ↦ f x (g x)) :=
  isBoundedBilinearMap_apply.continuous.comp₂ hf hg

@[fun_prop]
/-
**ContinuousOn.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.clm_apply {f : X -> E ->L[𝕜] F} {g : X -> E} {s : Set X} (hf 
: ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => f x (g x)) 
s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `IsBoundedBilinearMap.continuous`：continuous (h : IsBoundedBilinearMap 𝕜 
f) : Continuous f
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
-/
theorem ContinuousOn.clm_apply {f : X → E →L[𝕜] F} {g : X → E}
    {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x ↦ f x (g x)) s :=
  (isBoundedBilinearMap_apply (𝕜 := 𝕜) (F := F)).continuous.comp_continuousOn (hf.prodMk hg)

@[continuity, fun_prop]
/-
**ContinuousAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.clm_apply {X} [TopologicalSpace X] {f : X -> E ->L[𝕜] F} {g :
 X -> E} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt 
(fun x => f x (g x)) x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAt.comp₂`：ContinuousAt.comp₂ {f : Y × Z -> W} {g : X -> Y} {h 
: X -> Z} {x : X} (hf : ContinuousAt f (g x, h x)) (hg : ContinuousAt g x) (hh :
 Continu…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `IsBoundedBilinearMap.continuous`：continuous (h : IsBoundedBilinearMap 𝕜 
f) : Continuous f
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
-/
theorem ContinuousAt.clm_apply {X} [TopologicalSpace X] {f : X → E →L[𝕜] F} {g : X → E} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x ↦ f x (g x)) x :=
  isBoundedBilinearMap_apply.continuous.continuousAt.comp₂ hf hg

@[continuity, fun_prop]
/-
**ContinuousWithinAt.clm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.clm_apply {X} [TopologicalSpace X] {f : X -> E ->L[𝕜] F
} {g : X -> E} {s : Set X} {x : X} (hf : ContinuousWithinAt f s x) (hg : Continu
ousWithinAt g s x) : ContinuousWithinAt (fun x => f x (g x)) s x
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `IsBoundedBilinearMap.continuous`：continuous (h : IsBoundedBilinearMap 𝕜 
f) : Continuous f
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `isBoundedBilinearMap_apply`：isBoundedBilinearMap_apply : IsBoundedBiline
arMap 𝕜 fun p : (E ->L[𝕜] F) × E => p.1 p.2
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
-/
theorem ContinuousWithinAt.clm_apply {X} [TopologicalSpace X] {f : X → E →L[𝕜] F} {g : X → E}
    {s : Set X} {x : X} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x ↦ f x (g x)) s x :=
  (isBoundedBilinearMap_apply (𝕜 := 𝕜) (F := F)).continuous.continuousAt.comp_continuousWithinAt
    (hf.prodMk hg)

@[fun_prop]
/-
**ContinuousWithinAt.continuousLinearMapCoprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.continuousLinearMapCoprod {f : X -> E ->L[𝕜] G} {g : X 
-> F ->L[𝕜] G} {s : Set X} {x : X} (hf : ContinuousWithinAt f s x) (hg : Continu
ousWithinAt g s x) : ContinuousWithinAt (fun x => (f x).coprod (g x)) s x
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousWithinAt.fun_add`：∀ {M : Type u_1} [inst : TopologicalSpace M]
 [inst_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace 
X] {f g : X → M}…
· 使用定理 `ContinuousWithinAt.clm_comp`：ContinuousWithinAt.clm_comp {g : X -> F ->L
[𝕜] G} {f : X -> E ->L[𝕜] F} {s : Set X} {x : X} (hg : ContinuousWithinAt g s x)
 (hf : Continuous…
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
-/
theorem ContinuousWithinAt.continuousLinearMapCoprod
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} {s : Set X} {x : X}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => (f x).coprod (g x)) s x := by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]
/-
**ContinuousAt.continuousLinearMapCoprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.continuousLinearMapCoprod {f : X -> E ->L[𝕜] G} {g : X -> F -
>L[𝕜] G} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt 
(fun x => (f x).coprod (g x)) x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousAt.fun_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `ContinuousAt.clm_comp`：ContinuousAt.clm_comp {g : X -> F ->L[𝕜] G} {f : 
X -> E ->L[𝕜] F} {x : X} (hg : ContinuousAt g x) (hf : ContinuousAt f x) : Conti
nuousAt (fu…
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
-/
theorem ContinuousAt.continuousLinearMapCoprod
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} {x : X}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun x => (f x).coprod (g x)) x := by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]
/-
**ContinuousOn.continuousLinearMapCoprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.continuousLinearMapCoprod {f : X -> E ->L[𝕜] G} {g : X -> F -
>L[𝕜] G} {s : Set X} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : Continuou
sOn (fun x => (f x).coprod (g x)) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousOn.fun_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `ContinuousOn.clm_comp`：ContinuousOn.clm_comp {g : X -> F ->L[𝕜] G} {f : 
X -> E ->L[𝕜] F} {s : Set X} (hg : ContinuousOn g s) (hf : ContinuousOn f s) : C
ontinuousOn…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem ContinuousOn.continuousLinearMapCoprod
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G} {s : Set X}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => (f x).coprod (g x)) s := by
  simp only [← comp_fst_add_comp_snd]
  fun_prop

@[fun_prop]
/-
**Continuous.continuousLinearMapCoprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.continuousLinearMapCoprod {f : X -> E ->L[𝕜] G} {g : X -> F ->L
[𝕜] G} (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => (f x).copr
od (g x))
参数：hf : Continuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.continuousLinearMapCoprod`：ContinuousOn.continuousLinearMap
Coprod {f : X -> E ->L[𝕜] G} {g : X -> F ->L[𝕜] G} {s : Set X} (hf : ContinuousO
n f s) (hg : ContinuousOn g …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
theorem Continuous.continuousLinearMapCoprod
    {f : X → E →L[𝕜] G} {g : X → F →L[𝕜] G}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => (f x).coprod (g x)) := by
  apply continuousOn_univ.mp
  fun_prop

end

namespace ContinuousLinearEquiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

open Set
open scoped Topology

/-!
### The set of continuous linear equivalences between two Banach spaces is open

In this section we establish that the set of continuous linear equivalences between two Banach
spaces is an open subset of the space of linear maps between them.
-/

/-
**ContinuousLinearEquiv.isOpen** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`
。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : S
eminormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   [CompleteSpace E], IsOpen 
(Set.range ContinuousLinearEquiv.toContinuousLinearMap)
参数：Set.range ContinuousLinearEquiv.toContinuousLinearMap。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsBoundedBilinearMap.continuous_right`：continuous_right (h : IsBoundedBi
linearMap 𝕜 f) {e₁ : E} : Continuous fun e₂ => f (e₁, e₂)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `isBoundedBilinearMap_comp`：isBoundedBilinearMap_comp : IsBoundedBilinear
Map 𝕜 fun p : (F ->L[𝕜] G) × (E ->L[𝕜] F) => p.1.comp p.2
· 使用定理 `ContinuousLinearEquiv.continuous_toFun`：∀ {R : Type u_1} {S : Type u_2} 
[inst : Semiring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2
 : RingHomInvPair σ σ'] [ins…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Units.isOpen`：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSer
ies R], IsOpen {x | IsUnit x}
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
### The set of continuous linear equivalences between two Banach spaces is open

In this section we establish that the set of continuous linear equivalences betw
een two Banach
spaces is an open subset of the space of linear maps between them.
-/
protected theorem isOpen [CompleteSpace E] : IsOpen (range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F)) := by
  rw [isOpen_iff_mem_nhds, forall_mem_range]
  refine fun e => IsOpen.mem_nhds ?_ (mem_range_self _)
  let O : (E →L[𝕜] F) → E →L[𝕜] E := fun f => (e.symm : F →L[𝕜] E).comp f
  have h_O : Continuous O := (isBoundedBilinearMap_comp (𝕜 := 𝕜) (F := F) (G := E)).continuous_right
  convert! show IsOpen (O ⁻¹' {x | IsUnit x}) from Units.isOpen.preimage h_O using 1
  ext f'
  constructor
  · rintro ⟨e', rfl⟩
    exact ⟨(e'.trans e.symm).toUnit, rfl⟩
  · rintro ⟨w, hw⟩
    use (unitsEquiv 𝕜 E w).trans e
    ext x
    simp [O, hw]
/-
**ContinuousLinearEquiv.nhds** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : S
eminormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F]   [CompleteSpace E] (e : E ≃
L[𝕜] F), Set.range ContinuousLinearEquiv.toContinuousLinearMap ∈ nhds ↑e
参数：e : E ≃L[𝕜] F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousLinearEquiv.isOpen`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {F : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem nhds [CompleteSpace E] (e : E ≃L[𝕜] F) :
    range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (e : E →L[𝕜] F) :=
  IsOpen.mem_nhds ContinuousLinearEquiv.isOpen (by simp)

end ContinuousLinearEquiv

