/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Iterate
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Instances.Rat

/-!
# A collection of specific limit computations

This file, by design, is independent of `NormedSpace` in the import hierarchy.  It contains
important specific limit computations in metric spaces, in ordered rings/fields, and in specific
instances of these such as `ℝ`, `ℝ≥0` and `ℝ≥0∞`.
-/

@[expose] public section

assert_not_exists Module.Basis NormedSpace

noncomputable section

open Set Function Filter Finset Metric Topology Nat uniformity NNReal ENNReal

variable {α : Type*} {β : Type*} {ι : Type*}

/-
**NNRat.tendsto_inv_atTop_nhds_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNRat.tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : Nat => (n : Rat>=
0)⁻¹) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
· 使用定理 `NNRat.instIsStrictOrderedRing`：IsStrictOrderedRing ℚ≥0
· 使用定理 `NNRat.instOrderTopology`：OrderTopology ℚ≥0
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNNRat`：Archimedean ℚ≥0
-/
theorem NNRat.tendsto_inv_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ (n : ℚ≥0)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
/-
**NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat (𝕜 : Type*) [Semiring 𝕜] 
[Algebra Rat>=0 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] : Tendsto (alg
ebraMap Rat>=0 𝕜 ∘ fun n : Nat => (n : Rat>=0)⁻¹) atTop (𝓝 0)
参数：𝕜 : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `NNRat.tendsto_inv_atTop_nhds_zero_nat`：NNRat.tendsto_inv_atTop_nhds_zero
_nat : Tendsto (fun n : Nat => (n : Rat>=0)⁻¹) atTop (𝓝 0)
-/
theorem NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat (𝕜 : Type*) [Semiring 𝕜]
    [Algebra ℚ≥0 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (algebraMap ℚ≥0 𝕜 ∘ fun n : ℕ ↦ (n : ℚ≥0)⁻¹) atTop (𝓝 0) := by
  convert! (continuous_algebraMap ℚ≥0 𝕜).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]
/-
**tendsto_inv_atTop_nhds_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero
 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] : Tendsto (fun n : Nat => (n 
: 𝕜)⁻¹) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat`：NNRat.tendsto_algebraM
ap_inv_atTop_nhds_zero_nat (𝕜 : Type*) [Semiring 𝕜] [Algebra Rat>=0 𝕜] [Topologi
calSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] …
-/
theorem tendsto_inv_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert! NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat 𝕜
  simp
/-
**tendsto_const_div_atTop_nhds_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_const_div_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [Ch
arZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] [ContinuousMul 𝕜] (C : 
𝕜) : Tendsto (fun n : Nat => C / n) atTop (𝓝 0)
参数：C : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_inv_atTop_nhds_zero_nat`：tendsto_inv_atTop_nhds_zero_nat {𝕜 : Ty
pe*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>
=0 𝕜] : Tendsto (fun …
-/
theorem tendsto_const_div_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] [ContinuousMul 𝕜] (C : 𝕜) :
    Tendsto (fun n : ℕ ↦ C / n) atTop (𝓝 0) := by
  simpa only [mul_zero, div_eq_mul_inv] using
    (tendsto_const_nhds (x := C)).mul tendsto_inv_atTop_nhds_zero_nat
/-
**tendsto_one_div_atTop_nhds_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_one_div_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [Char
Zero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] : Tendsto (fun n : Nat =>
 1 / (n : 𝕜)) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
-/
theorem tendsto_one_div_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ 1 / (n : 𝕜)) atTop (𝓝 0) := by
  simp [tendsto_inv_atTop_nhds_zero_nat]
/-
**EReal.tendsto_const_div_atTop_nhds_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EReal.tendsto_const_div_atTop_nhds_zero_nat {C : EReal} (h : C != ⊥) (h' :
 C != ⊤) : Tendsto (fun n : Nat => C / n) atTop (𝓝 0)
参数：h : C != ⊥；h' : C != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_toReal`：coe_toReal {x : EReal} (hx : x != ⊤) (h'x : x != ⊥) : 
(x.toReal : EReal) = x
· 使用定理 `EReal.coe_coe_eq_natCast`：coe_coe_eq_natCast (n : Nat) : (n : Real) = (n
 : EReal)
· 使用引理 `EReal.coe_div`：coe_div (a b : Real) : (a / b : Real) = (a : EReal) / (b 
: EReal)
· 使用定理 `EReal.coe_zero`：coe_zero : ((0 : Real) : EReal) = 0
· 使用定理 `EReal.tendsto_coe`：tendsto_coe {α : Type*} {f : Filter α} {m : α -> Real
} {a : Real} : Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
· 使用定理 `tendsto_const_div_atTop_nhds_zero_nat`：tendsto_const_div_atTop_nhds_zero
_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [Continu
ousSMul Rat>=0 𝕜] [Continuo…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNRat.instContinuousSMulOfIsScalarTowerOfRat`：∀ {R : Type u_1} [inst : T
opologicalSpace R] [inst_1 : MulAction ℚ R] [inst_2 : MulAction ℚ≥0 R] [IsScalar
Tower ℚ≥0 ℚ R]   [ContinuousSMul ℚ…
· 使用定理 `NNRat.instContinuousSMulRatReal`：ContinuousSMul ℚ ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
-/
theorem EReal.tendsto_const_div_atTop_nhds_zero_nat {C : EReal} (h : C ≠ ⊥) (h' : C ≠ ⊤) :
    Tendsto (fun n : ℕ ↦ C / n) atTop (𝓝 0) := by
  have : (fun n : ℕ ↦ C / n) = fun n : ℕ ↦ ((C.toReal / n : ℝ) : EReal) := by
    ext n
    nth_rw 1 [← coe_toReal h' h, ← coe_coe_eq_natCast n, ← coe_div C.toReal n]
  rw [this, ← coe_zero, tendsto_coe]
  exact _root_.tendsto_const_div_atTop_nhds_zero_nat C.toReal
/-
**tendsto_one_div_add_atTop_nhds_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_one_div_add_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [
CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] : Tendsto (fun n : Na
t => 1 / ((n : 𝕜) + 1)) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `tendsto_one_div_atTop_nhds_zero_nat`：tendsto_one_div_atTop_nhds_zero_nat
 {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousS
Mul Rat>=0 𝕜] : Tendsto (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem tendsto_one_div_add_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ 1 / ((n : 𝕜) + 1)) atTop (𝓝 0) :=
  suffices Tendsto (fun n : ℕ ↦ 1 / (↑(n + 1) : 𝕜)) atTop (𝓝 0) by simpa
  (tendsto_add_atTop_iff_nat 1).2 tendsto_one_div_atTop_nhds_zero_nat
/-
**tendsto_algebraMap_inv_atTop_nhds_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_algebraMap_inv_atTop_nhds_zero_nat {𝕜 : Type*} (A : Type*) [Semifi
eld 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] [Semiring A] 
[Algebra 𝕜 A] [TopologicalSpace A] [ContinuousSMul 𝕜 A] : Tendsto (algebraMap 𝕜 
A ∘ fun n : Nat => (n : 𝕜)⁻¹) atTop (𝓝 0)
参数：A : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `tendsto_inv_atTop_nhds_zero_nat`：tendsto_inv_atTop_nhds_zero_nat {𝕜 : Ty
pe*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>
=0 𝕜] : Tendsto (fun …
-/
theorem tendsto_algebraMap_inv_atTop_nhds_zero_nat {𝕜 : Type*} (A : Type*)
    [Semifield 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜]
    [Semiring A] [Algebra 𝕜 A] [TopologicalSpace A] [ContinuousSMul 𝕜 A] :
    Tendsto (algebraMap 𝕜 A ∘ fun n : ℕ ↦ (n : 𝕜)⁻¹) atTop (𝓝 0) := by
  convert! (continuous_algebraMap 𝕜 A).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

/-- The limit of `n / (n + x)` is 1, for any constant `x` (valid in `ℝ` or any topological division
algebra over `ℚ≥0`, e.g., `ℂ`). -/
/-
**tendsto_natCast_div_add_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_natCast_div_add_atTop {𝕜 : Type*} [DivisionSemiring 𝕜] [Topologica
lSpace 𝕜] [CharZero 𝕜] [ContinuousSMul Rat>=0 𝕜] [IsTopologicalSemiring 𝕜] [Cont
inuousInv₀ 𝕜] (x : 𝕜) : Tendsto (fun n : Nat => (n : 𝕜) / (n + x)) atTop (𝓝 1)
参数：x : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_div'`：add_div' (a b c : K) (hc : c != 0) : b + a / c = (b * c + a) /
 c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The limit of `n / (n + x)` is 1, for any constant `x` (valid in `ℝ` or any topol
ogical division
algebra over `ℚ≥0`, e.g., `ℂ`).
-/
theorem tendsto_natCast_div_add_atTop {𝕜 : Type*} [DivisionSemiring 𝕜] [TopologicalSpace 𝕜]
    [CharZero 𝕜] [ContinuousSMul ℚ≥0 𝕜] [IsTopologicalSemiring 𝕜] [ContinuousInv₀ 𝕜] (x : 𝕜) :
    Tendsto (fun n : ℕ ↦ (n : 𝕜) / (n + x)) atTop (𝓝 1) := by
  convert! Tendsto.congr' ((eventually_ne_atTop 0).mp (Eventually.of_forall fun n hn ↦ _)) _
  · exact fun n : ℕ ↦ 1 / (1 + x / n)
  · simp [Nat.cast_ne_zero.mpr hn, add_div']
  · have : 𝓝 (1 : 𝕜) = 𝓝 (1 / (1 + x * (0 : 𝕜))) := by
      rw [mul_zero, add_zero, div_one]
    rw [this]
    refine tendsto_const_nhds.div (tendsto_const_nhds.add ?_) (by simp)
    simp_rw [div_eq_mul_inv]
    exact tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat
/-
**tendsto_add_mul_div_add_mul_atTop_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_add_mul_div_add_mul_atTop_nhds {𝕜 : Type*} [Semifield 𝕜] [CharZero
 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul Rat>=0 𝕜] [IsTopologicalSemiring 𝕜] [Co
ntinuousInv₀ 𝕜] (a b c : 𝕜) {d : 𝕜} (hd : d != 0) : Tendsto (fun k : Nat => (a +
 c * k) / (b + d * k)) atTop (𝓝 (c / d))
参数：a b c : 𝕜；hd : d != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
（共 74 条，此处仅展示前 30 条）
-/
theorem tendsto_add_mul_div_add_mul_atTop_nhds {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] [IsTopologicalSemiring 𝕜] [ContinuousInv₀ 𝕜]
    (a b c : 𝕜) {d : 𝕜} (hd : d ≠ 0) :
    Tendsto (fun k : ℕ ↦ (a + c * k) / (b + d * k)) atTop (𝓝 (c / d)) := by
  apply Filter.Tendsto.congr'
  case f₁ => exact fun k ↦ (a * (↑k)⁻¹ + c) / (b * (↑k)⁻¹ + d)
  · refine (eventually_ne_atTop 0).mp (Eventually.of_forall ?_)
    intro h hx
    dsimp
    field (discharger := norm_cast)
  · apply Filter.Tendsto.div _ _ hd
    all_goals
      apply zero_add (_ : 𝕜) ▸ Filter.Tendsto.add_const _ _
      apply mul_zero (_ : 𝕜) ▸ Filter.Tendsto.const_mul _ _
      exact tendsto_inv_atTop_nhds_zero_nat

/-- For any positive `m : ℕ`, `((n % m : ℕ) : ℝ) / (n : ℝ)` tends to `0` as `n` tends to `∞`. -/
/-
**tendsto_mod_div_atTop_nhds_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_mod_div_atTop_nhds_zero_nat {m : Nat} (hm : 0 < m) : Tendsto (fun 
n : Nat => ((n % m : Nat) : Real) / (n : Real)) atTop (𝓝 0)
参数：hm : 0 < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `tendsto_bdd_div_atTop_nhds_zero`：tendsto_bdd_div_atTop_nhds_zero {f g : 
α -> 𝕜} {b B : 𝕜} (hb : forallᶠ x in l, b <= f x) (hB : forallᶠ x in l, f x <= B
) (hg : Tendsto g l a…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop

--- 原说明 ---
For any positive `m : ℕ`, `((n % m : ℕ) : ℝ) / (n : ℝ)` tends to `0` as `n` tend
s to `∞`.
-/
theorem tendsto_mod_div_atTop_nhds_zero_nat {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n % m : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have h0 : ∀ᶠ n : ℕ in atTop, 0 ≤ (fun n : ℕ => ((n % m : ℕ) : ℝ)) n := by aesop
  exact tendsto_bdd_div_atTop_nhds_zero h0
    (.of_forall (fun n ↦ cast_le.mpr (mod_lt n hm).le)) tendsto_natCast_atTop_atTop

/-- If `a ≠ 0`, `(a * x + c)⁻¹` tends to `0` as `x` tends to `∞`. -/
/-
**tendsto_mul_add_inv_atTop_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_mul_add_inv_atTop_nhds_zero (a c : Real) (ha : a != 0) : Tendsto (
fun x => (a * x + c)⁻¹) atTop (𝓝 0)
参数：a c : Real；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atBot_zero`：tendsto_inv_atBot_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atBot (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.tendsto_atBot_add_const_right`：∀ {α : Type u_1} {G : Type u_2} [i
nst : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filt
er α)   {f : α → G} (C : G…
· 使用定理 `Filter.Tendsto.const_mul_atTop_of_neg`：∀ {α : Type u_1} {β : Type u_2} [
inst : Field α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} 
  {f : β → α} {r : α}, r < …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
· 使用定理 `Filter.tendsto_atTop_add_const_right`：∀ {α : Type u_1} {G : Type u_2} [i
nst : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filt
er α)   {f : α → G} (C : G…
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …

--- 原说明 ---
If `a ≠ 0`, `(a * x + c)⁻¹` tends to `0` as `x` tends to `∞`.
-/
theorem tendsto_mul_add_inv_atTop_nhds_zero (a c : ℝ) (ha : a ≠ 0) :
    Tendsto (fun x => (a * x + c)⁻¹) atTop (𝓝 0) := by
  obtain ha' | ha' := lt_or_gt_of_ne ha
  · exact tendsto_inv_atBot_zero.comp
      (tendsto_atBot_add_const_right _ c (tendsto_id.const_mul_atTop_of_neg ha'))
  · exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ c (tendsto_id.const_mul_atTop ha'))
/-
**Filter.EventuallyEq.div_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.div_mul_cancel {α G : Type*} [GroupWithZero G] {f g : 
α -> G} {l : Filter α} (hg : Tendsto g l (𝓟 {0}ᶜ)) : (fun x => f x / g x * g x) 
=ᶠ[l] fun x => f x
参数：hg : Tendsto g l (𝓟 {0}ᶜ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `Filter.preimage_mem_comap`：preimage_mem_comap (ht : t in g) : m ⁻¹' t in
 comap m g
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Filter.EventuallyEq.div_mul_cancel {α G : Type*} [GroupWithZero G] {f g : α → G}
    {l : Filter α} (hg : Tendsto g l (𝓟 {0}ᶜ)) : (fun x ↦ f x / g x * g x) =ᶠ[l] fun x ↦ f x := by
  filter_upwards [hg.le_comap <| preimage_mem_comap (m := g) (mem_principal_self {0}ᶜ)] with x hx
  simp_all

/-- If `g` tends to `∞`, then eventually for all `x` we have `(f x / g x) * g x = f x`. -/
/-
**Filter.EventuallyEq.div_mul_cancel_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.div_mul_cancel_atTop {α K : Type*} [DivisionSemiring K
] [LinearOrder K] [IsStrictOrderedRing K] {f g : α -> K} {l : Filter α} (hg : Te
ndsto g l atTop) : (fun x => f x / g x * g x) =ᶠ[l] fun x => f x
参数：hg : Tendsto g l atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.div_mul_cancel`：Filter.EventuallyEq.div_mul_cancel {
α G : Type*} [GroupWithZero G] {f g : α -> G} {l : Filter α} (hg : Tendsto g l (
𝓟 {0}ᶜ)) : (fun x => f x…
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `g` tends to `∞`, then eventually for all `x` we have `(f x / g x) * g x = f 
x`.
-/
theorem Filter.EventuallyEq.div_mul_cancel_atTop {α K : Type*}
    [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRing K]
    {f g : α → K} {l : Filter α} (hg : Tendsto g l atTop) :
    (fun x ↦ f x / g x * g x) =ᶠ[l] fun x ↦ f x :=
  div_mul_cancel <| hg.mono_right <| le_principal_iff.mpr <|
    mem_of_superset (Ioi_mem_atTop 0) <| by simp

/-- If when `x` tends to `∞`, `g` tends to `∞` and `f x / g x` tends to a positive
  constant, then `f` tends to `∞`. -/
/-
**Filter.Tendsto.num** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.num {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrdere
dRing K] [TopologicalSpace K] [OrderTopology K] {f g : α -> K} {l : Filter α} (h
g : Tendsto g l atTop) {a : K} (ha : 0 < a) (hlim : Tendsto (fun x => f x / g x)
 l (𝓝 a)) : Tendsto f l atTop
参数：hg : Tendsto g l atTop；ha : 0 < a；hlim : Tendsto (fun x => f x / g x) l (𝓝 a)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.div_mul_cancel_atTop`：Filter.EventuallyEq.div_mul_ca
ncel_atTop {α K : Type*} [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRi
ng K] {f g : α -> K} {l : Filt…
· 使用定理 `Filter.Tendsto.pos_mul_atTop`：Filter.Tendsto.pos_mul_atTop {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atTop) : Tendsto (fun x => f 
x * g x) l atTop

--- 原说明 ---
If when `x` tends to `∞`, `g` tends to `∞` and `f x / g x` tends to a positive
  constant, then `f` tends to `∞`.
-/
theorem Filter.Tendsto.num {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K]
    {f g : α → K} {l : Filter α} (hg : Tendsto g l atTop) {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto f l atTop :=
  (hlim.pos_mul_atTop ha hg).congr' (EventuallyEq.div_mul_cancel_atTop hg)

/-- If when `x` tends to `∞`, `g` tends to `∞` and `f x / g x` tends to a positive
  constant, then `f` tends to `∞`. -/
/-
**Filter.Tendsto.den** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.den {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrdere
dRing K] [TopologicalSpace K] [OrderTopology K] [ContinuousInv K] {f g : α -> K}
 {l : Filter α} (hf : Tendsto f l atTop) {a : K} (ha : 0 < a) (hlim : Tendsto (f
un x => f x / g x) l (𝓝 a)) : Tendsto g l atTop
参数：hf : Tendsto f l atTop；ha : 0 < a；hlim : Tendsto (fun x => f x / g x) l (𝓝 a)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Filter.Tendsto.inv`：Filter.Tendsto.inv {f : α -> G} {l : Filter α} {y : 
G} (h : Tendsto f l (𝓝 y)) : Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹)
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.div_mul_cancel_atTop`：Filter.EventuallyEq.div_mul_ca
ncel_atTop {α K : Type*} [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRi
ng K] {f g : α -> K} {l : Filt…
· 使用定理 `Filter.Tendsto.pos_mul_atTop`：Filter.Tendsto.pos_mul_atTop {C : 𝕜} (hC :
 0 < C) (hf : Tendsto f l (𝓝 C)) (hg : Tendsto g l atTop) : Tendsto (fun x => f 
x * g x) l atTop
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
If when `x` tends to `∞`, `g` tends to `∞` and `f x / g x` tends to a positive
  constant, then `f` tends to `∞`.
-/
theorem Filter.Tendsto.den {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K]
    [ContinuousInv K] {f g : α → K} {l : Filter α} (hf : Tendsto f l atTop) {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto g l atTop :=
  have hlim' : Tendsto (fun x => g x / f x) l (𝓝 a⁻¹) := by
    simp_rw [← inv_div (f _)]
    exact Filter.Tendsto.inv (f := fun x => f x / g x) hlim
  (hlim'.pos_mul_atTop (inv_pos_of_pos ha) hf).congr' (.div_mul_cancel_atTop hf)

/-- If when `x` tends to `∞`, `f x / g x` tends to a positive constant, then `f` tends to `∞` if
  and only if `g` tends to `∞`. -/
/-
**Filter.Tendsto.num_atTop_iff_den_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.num_atTop_iff_den_atTop {α K : Type*} [Field K] [LinearOrde
r K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] [ContinuousI
nv K] {f g : α -> K} {l : Filter α} {a : K} (ha : 0 < a) (hlim : Tendsto (fun x 
=> f x / g x) l (𝓝 a)) : Tendsto f l atTop ↔ Tendsto g l atTop
参数：ha : 0 < a；hlim : Tendsto (fun x => f x / g x) l (𝓝 a)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.den`：Filter.Tendsto.den {α K : Type*} [Field K] [LinearOr
der K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] [Continuou
sInv K] …
· 使用定理 `Filter.Tendsto.num`：Filter.Tendsto.num {α K : Type*} [Field K] [LinearOr
der K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] {f g : α -
> K} {l …

--- 原说明 ---
If when `x` tends to `∞`, `f x / g x` tends to a positive constant, then `f` ten
ds to `∞` if
  and only if `g` tends to `∞`.
-/
theorem Filter.Tendsto.num_atTop_iff_den_atTop {α K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
    [OrderTopology K] [ContinuousInv K] {f g : α → K} {l : Filter α} {a : K} (ha : 0 < a)
    (hlim : Tendsto (fun x => f x / g x) l (𝓝 a)) :
    Tendsto f l atTop ↔ Tendsto g l atTop :=
  ⟨fun hf ↦ hf.den ha hlim, fun hg ↦ hg.num ha hlim⟩

/-! ### Powers -/


/-
**tendsto_add_one_pow_atTop_atTop_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_add_one_pow_atTop_atTop_of_pos [Semiring α] [LinearOrder α] [IsStr
ictOrderedRing α] [Archimedean α] {r : α} (h : 0 < r) : Tendsto (fun n : Nat => 
(r + 1) ^ n) atTop atTop
参数：h : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_atTop_of_monotone'`：tendsto_atTop_atTop_of_monotone
' [Preorder ι] [LinearOrder α] {u : ι -> α} (h : Monotone u) (H : ¬BddAbove (ran
ge u)) : Tendsto u atTop atTo…
· 使用引理 `pow_right_mono₀`：pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h 
: 1 <= a) : Monotone (a ^ ·)
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_bddAbove_iff`：not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set 
α} : ¬BddAbove s ↔ forall x, exists y in s, x < y
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)
· 使用定理 `add_one_pow_unbounded_of_pos`：add_one_pow_unbounded_of_pos (x : R) (hy :
 0 < y) : exists n : Nat, x < (y + 1) ^ n

--- 原说明 ---
### Powers
-/
theorem tendsto_add_one_pow_atTop_atTop_of_pos
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] {r : α}
    (h : 0 < r) : Tendsto (fun n : ℕ ↦ (r + 1) ^ n) atTop atTop :=
  tendsto_atTop_atTop_of_monotone' (pow_right_mono₀ <| le_add_of_nonneg_left h.le) <|
    not_bddAbove_iff.2 fun _ ↦ Set.exists_range_iff.2 <| add_one_pow_unbounded_of_pos _ h
/-
**tendsto_pow_atTop_atTop_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_atTop_atTop_of_one_lt [Semiring α] [LinearOrder α] [IsStrictOr
deredRing α] [ExistsAddOfLE α] [Archimedean α] {r : α} (h : 1 < r) : Tendsto (fu
n n : Nat => r ^ n) atTop atTop
参数：h : 1 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pos_add_of_lt'`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [ExistsAddOfLE α] {a b : α} [AddLeftReflectLT α],   a < b → ∃ c, 0 <
 c ∧ a + c …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tendsto_add_one_pow_atTop_atTop_of_pos`：tendsto_add_one_pow_atTop_atTop_
of_pos [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] {r :
 α} (h : 0 < r) : Tendsto (f…
-/
theorem tendsto_pow_atTop_atTop_of_one_lt
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean α] {r : α}
    (h : 1 < r) : Tendsto (fun n : ℕ ↦ r ^ n) atTop atTop := by
  obtain ⟨r, r0, rfl⟩ := exists_pos_add_of_lt' h
  rw [add_comm]
  exact tendsto_add_one_pow_atTop_atTop_of_pos r0
/-
**tendsto_pow_atTop_nhds_zero_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_atTop_nhds_zero_of_lt_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrd
er 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜] [Archimedean 𝕜] [TopologicalSpac
e 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 <= r) (h₂ : r < 1) : Tendsto (fun n : Nat
 => r ^ n) atTop (𝓝 0)
参数：h₁ : 0 <= r；h₂ : r < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tendsto_pow_atTop_atTop_of_one_lt`：tendsto_pow_atTop_atTop_of_one_lt [Se
miring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean
 α] {r : α} (h : 1 < r)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_lt_inv₀`：one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
-/
theorem tendsto_pow_atTop_nhds_zero_of_lt_one {𝕜 : Type*}
    [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  h₁.eq_or_lt.elim
    (fun hr ↦ (tendsto_add_atTop_iff_nat 1).mp <| by
      simp [_root_.pow_succ, ← hr])
    (fun hr ↦
      have := (one_lt_inv₀ hr).2 h₂ |> tendsto_pow_atTop_atTop_of_one_lt
      (tendsto_inv_atTop_zero.comp this).congr fun n ↦ by simp)
/-
**tendsto_pow_atTop_nhds_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_4} [inst : Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrdere
dRing 𝕜] [Archimedean 𝕜]   [inst_4 : TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 
𝕜},   Filter.Tendsto (fun n => r ^ n) Filter.atTop (nhds 0) ↔ |r| < 1
参数：fun n => r ^ n；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_zero_iff_abs_tendsto_zero`：∀ {G : Type u_1} [inst : TopologicalS
pace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G
]   [OrderTopology G] {…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `not_tendsto_nhds_of_tendsto_atTop`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{l : Filter β} [l.NeBot…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
（共 42 条，此处仅展示前 30 条）
-/
@[simp] theorem tendsto_pow_atTop_nhds_zero_iff {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) ↔ |r| < 1 := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine ⟨fun h ↦ by_contra (fun hr_le ↦ ?_), fun h ↦ ?_⟩
  · by_cases hr : 1 = |r|
    · replace h : Tendsto (fun n : ℕ ↦ |r| ^ n) atTop (𝓝 0) := by simpa only [← abs_pow, h]
      simp only [hr.symm, one_pow] at h
      exact zero_ne_one <| tendsto_nhds_unique h tendsto_const_nhds
    · apply @not_tendsto_nhds_of_tendsto_atTop 𝕜 ℕ _ _ _ _ atTop _ (fun n ↦ |r| ^ n) _ 0 _
      · refine (pow_right_strictMono₀ <| lt_of_le_of_ne (le_of_not_gt hr_le)
          hr).monotone.tendsto_atTop_atTop (fun b ↦ ?_)
        obtain ⟨n, hn⟩ := (pow_unbounded_of_one_lt b (lt_of_le_of_ne (le_of_not_gt hr_le) hr))
        exact ⟨n, le_of_lt hn⟩
      · simpa only [← abs_pow]
  · simpa only [← abs_pow] using! (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg r)) h
/-
**tendsto_pow_atTop_nhdsWithin_zero_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_atTop_nhdsWithin_zero_of_lt_one {𝕜 : Type*} [Semifield 𝕜] [Lin
earOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜] [Archimedean 𝕜] [Topologic
alSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) : Tendsto (fun n 
: Nat => r ^ n) atTop (𝓝[>] 0)
参数：h₁ : 0 < r；h₂ : r < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`：tendsto_pow_atTop_nhds_zero_of_lt
_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAd
dOfLE 𝕜] [Archimedean 𝕜] [T…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
-/
theorem tendsto_pow_atTop_nhdsWithin_zero_of_lt_one {𝕜 : Type*}
    [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜]
    [Archimedean 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝[>] 0) :=
  tendsto_inf.2
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one h₁.le h₂,
      tendsto_principal.2 <| Eventually.of_forall fun _ ↦ pow_pos h₁ _⟩
/-
**uniformity_basis_dist_pow_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformity_basis_dist_pow_of_lt_one {α : Type*} [PseudoMetricSpace α] {r :
 Real} (h₀ : 0 < r) (h₁ : r < 1) : (uniformity α).HasBasis (fun _ : Nat => True)
 fun k => { p : α × α | dist p.1 p.2 < r ^ k }
参数：h₀ : 0 < r；h₁ : r < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mk_uniformity_basis`：∀ {α : Type u} [inst : PseudoMetricSpace α] 
{β : Type u_3} {p : β → Prop} {f : β → ℝ},   (∀ (i : β), p i → 0 < f i) →     (∀
 ⦃ε : ℝ⦄, 0 < ε …
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `trivial`：True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `exists_pow_lt_of_lt_one`：exists_pow_lt_of_lt_one (hx : 0 < x) (hy : y < 
1) : exists n : Nat, y ^ n < x
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
-/
theorem uniformity_basis_dist_pow_of_lt_one {α : Type*} [PseudoMetricSpace α] {r : ℝ} (h₀ : 0 < r)
    (h₁ : r < 1) :
    (uniformity α).HasBasis (fun _ : ℕ ↦ True) fun k ↦ { p : α × α | dist p.1 p.2 < r ^ k } :=
  Metric.mk_uniformity_basis (fun _ _ ↦ pow_pos h₀ _) fun _ ε0 ↦
    (exists_pow_lt_of_lt_one ε0 h₁).imp fun _ hk ↦ ⟨trivial, hk.le⟩
/-
**geom_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geom_lt {u : Nat -> Real} {c : Real} (hc : 0 <= c) {n : Nat} (hn : 0 < n) 
(h : forall k < n, c * u k < u (k + 1)) : c ^ n * u 0 < u n
参数：hc : 0 <= c；hn : 0 < n；h : forall k < n, c * u k < u (k + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.seq_pos_lt_seq_of_le_of_lt`：seq_pos_lt_seq_of_le_of_lt (hf : Mo
notone f) {n : Nat} (hn : 0 < n) (h₀ : x 0 <= y 0) (hx : forall k < n, x (k + 1)
 <= f (x k)) (hy : forall…
· 使用引理 `monotone_mul_left_of_nonneg`：monotone_mul_left_of_nonneg [PosMulMono M₀]
 (ha : 0 <= a) : Monotone fun x => a * x
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem geom_lt {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n)
    (h : ∀ k < n, c * u k < u (k + 1)) : c ^ n * u 0 < u n := by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h
  · simp
  · simp [_root_.pow_succ', mul_assoc]
/-
**geom_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geom_le {u : Nat -> Real} {c : Real} (hc : 0 <= c) (n : Nat) (h : forall k
 < n, c * u k <= u (k + 1)) : c ^ n * u 0 <= u n
参数：hc : 0 <= c；n : Nat；h : forall k < n, c * u k <= u (k + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.seq_le_seq`：seq_le_seq (hf : Monotone f) (n : Nat) (h₀ : x 0 <=
 y 0) (hx : forall k < n, x (k + 1) <= f (x k)) (hy : forall k < n, f (y k) <= y
 (k + 1))…
· 使用引理 `monotone_mul_left_of_nonneg`：monotone_mul_left_of_nonneg [PosMulMono M₀]
 (ha : 0 <= a) : Monotone fun x => a * x
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem geom_le {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k < n, c * u k ≤ u (k + 1)) :
    c ^ n * u 0 ≤ u n := by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h <;>
    simp [_root_.pow_succ', mul_assoc]
/-
**lt_geom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_geom {u : Nat -> Real} {c : Real} (hc : 0 <= c) {n : Nat} (hn : 0 < n) 
(h : forall k < n, u (k + 1) < c * u k) : u n < c ^ n * u 0
参数：hc : 0 <= c；hn : 0 < n；h : forall k < n, u (k + 1) < c * u k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.seq_pos_lt_seq_of_lt_of_le`：seq_pos_lt_seq_of_lt_of_le (hf : Mo
notone f) {n : Nat} (hn : 0 < n) (h₀ : x 0 <= y 0) (hx : forall k < n, x (k + 1)
 < f (x k)) (hy : forall …
· 使用引理 `monotone_mul_left_of_nonneg`：monotone_mul_left_of_nonneg [PosMulMono M₀]
 (ha : 0 <= a) : Monotone fun x => a * x
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem lt_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n)
    (h : ∀ k < n, u (k + 1) < c * u k) : u n < c ^ n * u 0 := by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_lt_of_le hn _ h _
  · simp
  · simp [_root_.pow_succ', mul_assoc]
/-
**le_geom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_geom {u : Nat -> Real} {c : Real} (hc : 0 <= c) (n : Nat) (h : forall k
 < n, u (k + 1) <= c * u k) : u n <= c ^ n * u 0
参数：hc : 0 <= c；n : Nat；h : forall k < n, u (k + 1) <= c * u k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.seq_le_seq`：seq_le_seq (hf : Monotone f) (n : Nat) (h₀ : x 0 <=
 y 0) (hx : forall k < n, x (k + 1) <= f (x k)) (hy : forall k < n, f (y k) <= y
 (k + 1))…
· 使用引理 `monotone_mul_left_of_nonneg`：monotone_mul_left_of_nonneg [PosMulMono M₀]
 (ha : 0 <= a) : Monotone fun x => a * x
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem le_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k < n, u (k + 1) ≤ c * u k) :
    u n ≤ c ^ n * u 0 := by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ h _ <;>
    simp [_root_.pow_succ', mul_assoc]

/-- If a sequence `v` of real numbers satisfies `k * v n ≤ v (n+1)` with `1 < k`,
then it goes to +∞. -/
/-
**tendsto_atTop_of_geom_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_atTop_of_geom_le {v : Nat -> Real} {c : Real} (h₀ : 0 < v 0) (hc :
 1 < c) (hu : forall n, c * v n <= v (n + 1)) : Tendsto v atTop atTop
参数：h₀ : 0 < v 0；hc : 1 < c；hu : forall n, c * v n <= v (n + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `geom_le`：geom_le {u : Nat -> Real} {c : Real} (hc : 0 <= c) (n : Nat) (h
 : forall k < n, c * u k <= u (k + 1)) : c ^ n * u 0 <= u n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.Tendsto.atTop_mul_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `tendsto_pow_atTop_atTop_of_one_lt`：tendsto_pow_atTop_atTop_of_one_lt [Se
miring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean
 α] {r : α} (h : 1 < r)…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α

--- 原说明 ---
If a sequence `v` of real numbers satisfies `k * v n ≤ v (n+1)` with `1 < k`,
then it goes to +∞.
-/
theorem tendsto_atTop_of_geom_le {v : ℕ → ℝ} {c : ℝ} (h₀ : 0 < v 0) (hc : 1 < c)
    (hu : ∀ n, c * v n ≤ v (n + 1)) : Tendsto v atTop atTop :=
  (tendsto_atTop_mono fun n ↦ geom_le (zero_le_one.trans hc.le) n fun k _ ↦ hu k) <|
    (tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const h₀
/-
**NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one {r : Real>=0} (hr : r < 1) : 
Tendsto (fun n : Nat => r ^ n) atTop (𝓝 0)
参数：hr : r < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {x : R
eal>=0} : Tendsto (fun a => (m a : Real)) f (𝓝 (x : Real)) ↔ Tendsto m f (𝓝 x)
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`：tendsto_pow_atTop_nhds_zero_of_lt
_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAd
dOfLE 𝕜] [Archimedean 𝕜] [T…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
theorem NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one {r : ℝ≥0} (hr : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  NNReal.tendsto_coe.1 <| by
    simp only [NNReal.coe_pow, NNReal.coe_zero,
      _root_.tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hr]

@[simp]
/-
**NNReal.tendsto_pow_atTop_nhds_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {r : NNReal}, Filter.Tendsto (fun n => r ^ n) Filter.atTop (nhds 0) ↔ r 
< 1
参数：fun n => r ^ n；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_pow_atTop_nhds_zero_iff`：∀ {𝕜 : Type u_4} [inst : Field 𝕜] [inst
_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Archimedean 𝕜]   [inst_4 : Topologi
calSpace 𝕜] [OrderTop…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.tendsto_coe`：tendsto_coe {f : Filter α} {m : α -> Real>=0} {x : R
eal>=0} : Tendsto (fun a => (m a : Real)) f (𝓝 (x : Real)) ↔ Tendsto m f (𝓝 x)
· 使用定理 `NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`：NNReal.tendsto_pow_atTop_n
hds_zero_of_lt_one {r : Real>=0} (hr : r < 1) : Tendsto (fun n : Nat => r ^ n) a
tTop (𝓝 0)
-/
protected theorem NNReal.tendsto_pow_atTop_nhds_zero_iff {r : ℝ≥0} :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) ↔ r < 1 :=
  ⟨fun h => by simpa [coe_pow, coe_zero, abs_eq, coe_lt_one, val_eq_coe] using
    tendsto_pow_atTop_nhds_zero_iff.mp <| tendsto_coe.mpr h, tendsto_pow_atTop_nhds_zero_of_lt_one⟩
/-
**ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one {r : Real>=0∞} (hr : r < 1) 
: Tendsto (fun n : Nat => r ^ n) atTop (𝓝 0)
参数：hr : r < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_coe`：lt_iff_exists_coe : a < b ↔ exists p : Real>=
0, a = p ∧ ↑p < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`：NNReal.tendsto_pow_atTop_n
hds_zero_of_lt_one {r : Real>=0} (hr : r < 1) : Tendsto (fun n : Nat => r ^ n) a
tTop (𝓝 0)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one {r : ℝ≥0∞} (hr : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) := by
  rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
  rw [← ENNReal.coe_zero]
  norm_cast at *
  apply NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr

@[simp]
/-
**ENNReal.tendsto_pow_atTop_nhds_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : ENNReal}, Filter.Tendsto (fun n => r ^ n) Filter.atTop (nhds 0) ↔ r
 < 1
参数：fun n => r ^ n；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ENNReal.top_ne_zero`：⊤ ≠ 0
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.EventuallyEq.tendsto`：Filter.EventuallyEq.tendsto {l : Filter α} 
{f : α -> X} (hf : f =ᶠ[l] fun _ => x) : Tendsto f l (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `ENNReal.pow_eq_top_iff`：∀ {a : ENNReal} {n : ℕ}, a ^ n = ⊤ ↔ a = ⊤ ∧ n ≠
 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NNReal.tendsto_pow_atTop_nhds_zero_iff`：∀ {r : NNReal}, Filter.Tendsto (
fun n => r ^ n) Filter.atTop (nhds 0) ↔ r < 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用定理 `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`：ENNReal.tendsto_pow_atTop
_nhds_zero_of_lt_one {r : Real>=0∞} (hr : r < 1) : Tendsto (fun n : Nat => r ^ n
) atTop (𝓝 0)
-/
protected theorem ENNReal.tendsto_pow_atTop_nhds_zero_iff {r : ℝ≥0∞} :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) ↔ r < 1 := by
  refine ⟨fun h ↦ ?_, tendsto_pow_atTop_nhds_zero_of_lt_one⟩
  lift r to NNReal
  · refine fun hr ↦ top_ne_zero (tendsto_nhds_unique (EventuallyEq.tendsto ?_) (hr ▸ h))
    exact eventually_atTop.mpr ⟨1, fun _ hn ↦ pow_eq_top_iff.mpr ⟨rfl, Nat.pos_iff_ne_zero.mp hn⟩⟩
  rw [← coe_zero] at h
  norm_cast at h ⊢
  exact NNReal.tendsto_pow_atTop_nhds_zero_iff.mp h

@[simp]
/-
**ENNReal.tendsto_pow_atTop_nhds_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : ENNReal}, Filter.Tendsto (fun n => r ^ n) Filter.atTop (nhds ⊤) ↔ 1
 < r
参数：fun n => r ^ n；nhds ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.one_lt_top`：1 < ⊤
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `pow_le_one₀`：pow_le_one₀ [PosMulMono M₀] {n : Nat} (ha₀ : 0 <= a) (ha₁ :
 a <= 1) : a ^ n <= 1
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.Tendsto.inv`：Filter.Tendsto.inv {f : α -> G} {l : Filter α} {y : 
G} (h : Tendsto f l (𝓝 y)) : Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹)
· 使用定理 `ENNReal.instContinuousInv`：ContinuousInv ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 31 条，此处仅展示前 30 条）
-/
protected theorem ENNReal.tendsto_pow_atTop_nhds_top_iff {r : ℝ≥0∞} :
    Tendsto (fun n ↦ r ^ n) atTop (𝓝 ∞) ↔ 1 < r := by
  refine ⟨?_, ?_⟩
  · contrapose!
    intro r_le_one h_tends
    specialize h_tends (Ioi_mem_nhds one_lt_top)
    simp only [Filter.mem_map, mem_atTop_sets, Set.mem_preimage, Set.mem_Ioi] at h_tends
    obtain ⟨n, hn⟩ := h_tends
    exact lt_irrefl _ <| lt_of_lt_of_le (hn n le_rfl) <| pow_le_one₀ zero_le r_le_one
  · intro r_gt_one
    have obs := @Tendsto.inv ℝ≥0∞ ℕ _ _ _ (fun n ↦ (r⁻¹) ^ n) atTop 0
    simp only [ENNReal.tendsto_pow_atTop_nhds_zero_iff, inv_zero] at obs
    simpa [← ENNReal.inv_pow] using obs <| ENNReal.inv_lt_one.mpr r_gt_one
/-
**ENNReal.eq_zero_of_le_mul_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ENNReal.eq_zero_of_le_mul_pow {x r : Real>=0∞} {ε : Real>=0} (hr : r < 1) 
(h : forall n : Nat, x <= ε * r ^ n) : x = 0
参数：hr : r < 1；h : forall n : Nat, x <= ε * r ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one`：ENNReal.tendsto_pow_atTop
_nhds_zero_of_lt_one {r : Real>=0∞} (hr : r < 1) : Tendsto (fun n : Nat => r ^ n
) atTop (𝓝 0)
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
lemma ENNReal.eq_zero_of_le_mul_pow {x r : ℝ≥0∞} {ε : ℝ≥0} (hr : r < 1)
    (h : ∀ n : ℕ, x ≤ ε * r ^ n) : x = 0 := by
  rw [← nonpos_iff_eq_zero]
  refine ge_of_tendsto' (f := fun (n : ℕ) ↦ ε * r ^ n) (x := atTop) ?_ h
  rw [← mul_zero (M₀ := ℝ≥0∞) (a := ε)]
  exact Tendsto.const_mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr coe_ne_top)

/-! ### Geometric series -/

section Geometric

/-
**hasSum_geometric_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_geometric_of_lt_one {r : Real} (h₁ : 0 <= r) (h₂ : r < 1) : HasSum 
(fun n : Nat => r ^ n) (1 - r)⁻¹
参数：h₁ : 0 <= r；h₂ : r < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`：tendsto_pow_atTop_nhds_zero_of_lt
_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAd
dOfLE 𝕜] [Archimedean 𝕜] [T…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasSum_iff_tendsto_nat_of_nonneg`：hasSum_iff_tendsto_nat_of_nonneg {f : 
Nat -> Real} (hf : forall i, 0 <= f i) (r : Real) : HasSum f r ↔ Tendsto (fun n 
: Nat => ∑ i in Finset…
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `geom_sum_eq`：geom_sum_eq (h : x != 1) (n : Nat) : ∑ i in range n, x ^ i 
= (x ^ n - 1) / (x - 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `neg_inv`：neg_inv : -a⁻¹ = (-a)⁻¹
（共 31 条，此处仅展示前 30 条）
-/
theorem hasSum_geometric_of_lt_one {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ :=
  have : r ≠ 1 := ne_of_lt h₂
  have : Tendsto (fun n ↦ (r ^ n - 1) * (r - 1)⁻¹) atTop (𝓝 ((0 - 1) * (r - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds
  (hasSum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr <| by
    simp_all [neg_inv, geom_sum_eq, div_eq_mul_inv]
/-
**summable_geometric_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_geometric_of_lt_one {r : Real} (h₁ : 0 <= r) (h₂ : r < 1) : Summa
ble fun n : Nat => r ^ n
参数：h₁ : 0 <= r；h₂ : r < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasSum_geometric_of_lt_one`：hasSum_geometric_of_lt_one {r : Real} (h₁ : 
0 <= r) (h₂ : r < 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
-/
theorem summable_geometric_of_lt_one {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Summable fun n : ℕ ↦ r ^ n :=
  ⟨_, hasSum_geometric_of_lt_one h₁ h₂⟩
/-
**tsum_geometric_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_geometric_of_lt_one {r : Real} (h₁ : 0 <= r) (h₂ : r < 1) : ∑' n : Na
t, r ^ n = (1 - r)⁻¹
参数：h₁ : 0 <= r；h₂ : r < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_geometric_of_lt_one`：hasSum_geometric_of_lt_one {r : Real} (h₁ : 
0 <= r) (h₂ : r < 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
-/
theorem tsum_geometric_of_lt_one {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  (hasSum_geometric_of_lt_one h₁ h₂).tsum_eq
/-
**hasSum_geometric_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_geometric_two : HasSum (fun n : Nat => ((1 : Real) / 2) ^ n) 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `hasSum_geometric_of_lt_one`：hasSum_geometric_of_lt_one {r : Real} (h₁ : 
0 <= r) (h₂ : r < 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
-/
theorem hasSum_geometric_two : HasSum (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) 2 := by
  convert! hasSum_geometric_of_lt_one _ _ <;> norm_num
/-
**summable_geometric_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_geometric_two : Summable fun n : Nat => ((1 : Real) / 2) ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasSum_geometric_two`：hasSum_geometric_two : HasSum (fun n : Nat => ((1 
: Real) / 2) ^ n) 2
-/
theorem summable_geometric_two : Summable fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n :=
  ⟨_, hasSum_geometric_two⟩
/-
**summable_geometric_two_encode** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_geometric_two_encode {ι : Type*} [Encodable ι] : Summable fun i :
 ι => (1 / 2 : Real) ^ Encodable.encode i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `summable_geometric_two`：summable_geometric_two : Summable fun n : Nat =>
 ((1 : Real) / 2) ^ n
· 使用定理 `Encodable.encode_injective`：∀ {α : Type u_1} [inst : Encodable α], Funct
ion.Injective Encodable.encode
-/
theorem summable_geometric_two_encode {ι : Type*} [Encodable ι] :
    Summable fun i : ι ↦ (1 / 2 : ℝ) ^ Encodable.encode i :=
  summable_geometric_two.comp_injective Encodable.encode_injective
/-
**tsum_geometric_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_geometric_two : (∑' n : Nat, ((1 : Real) / 2) ^ n) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_geometric_two`：hasSum_geometric_two : HasSum (fun n : Nat => ((1 
: Real) / 2) ^ n) 2
-/
theorem tsum_geometric_two : (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 :=
  hasSum_geometric_two.tsum_eq
/-
**sum_geometric_two_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_geometric_two_le (n : Nat) : (∑ i in range n, (1 / (2 : Real)) ^ i) <=
 2
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_geometric_two`：tsum_geometric_two : (∑' n : Nat, ((1 : Real) / 2) ^
 n) = 2
· 使用定理 `Summable.sum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilt
er ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [i
nst_3 : To…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `summable_geometric_two`：summable_geometric_two : Summable fun n : Nat =>
 ((1 : Real) / 2) ^ n
-/
theorem sum_geometric_two_le (n : ℕ) : (∑ i ∈ range n, (1 / (2 : ℝ)) ^ i) ≤ 2 := by
  have : ∀ i, 0 ≤ (1 / (2 : ℝ)) ^ i := by
    intro i
    apply pow_nonneg
    norm_num
  convert! summable_geometric_two.sum_le_tsum (range n) (fun i _ ↦ this i)
  exact tsum_geometric_two.symm
/-
**tsum_geometric_inv_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_geometric_inv_two : (∑' n : Nat, (2 : Real)⁻¹ ^ n) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `tsum_geometric_two`：tsum_geometric_two : (∑' n : Nat, ((1 : Real) / 2) ^
 n) = 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
-/
theorem tsum_geometric_inv_two : (∑' n : ℕ, (2 : ℝ)⁻¹ ^ n) = 2 :=
  (inv_eq_one_div (2 : ℝ)).symm ▸ tsum_geometric_two

/-- The sum of `2⁻¹ ^ i` for `n ≤ i` equals `2 * 2⁻¹ ^ n`. -/
/-
**tsum_geometric_inv_two_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_geometric_inv_two_ge (n : Nat) : (∑' i, ite (n <= i) ((2 : Real)⁻¹ ^ 
i) 0) = 2 * 2⁻¹ ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Summable.indicator`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace
 α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace
 α], Sum…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `summable_geometric_two`：summable_geometric_two : Summable fun n : Nat =>
 ((1 : Real) / 2) ^ n
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ite_eq_right_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y 
: α}, (if p then x else y) = y ↔ p → x = y
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.sum_add_tsum_nat_add`：∀ {G : Type u_2} [inst : AddCommGroup G] 
[inst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] {f : ℕ → G} 
  (k : ℕ), Summable…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The sum of `2⁻¹ ^ i` for `n ≤ i` equals `2 * 2⁻¹ ^ n`.
-/
theorem tsum_geometric_inv_two_ge (n : ℕ) :
    (∑' i, ite (n ≤ i) ((2 : ℝ)⁻¹ ^ i) 0) = 2 * 2⁻¹ ^ n := by
  have A : Summable fun i : ℕ ↦ ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0 := by
    simpa only [← piecewise_eq_indicator, one_div]
      using! summable_geometric_two.indicator {i | n ≤ i}
  have B : ((Finset.range n).sum fun i : ℕ ↦ ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0) = 0 :=
    Finset.sum_eq_zero fun i hi ↦
      ite_eq_right_iff.2 fun h ↦ (lt_irrefl _ ((Finset.mem_range.1 hi).trans_le h)).elim
  simp [-inv_pow, ← Summable.sum_add_tsum_nat_add n A, B, pow_add, _root_.tsum_mul_right,
    tsum_geometric_inv_two]
/-
**hasSum_geometric_two'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_geometric_two' (a : Real) : HasSum (fun n : Nat => a / 2 / 2 ^ n) a
参数：a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isNNRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsRat a (Int.ofNat n) d → Mathlib.Meta
.NormNum.IsNNRat a n d
· 使用定理 `Mathlib.Meta.NormNum.isRat_sub`：isRat_sub {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} (hf : f = HSub.hSub) (ra : IsRat 
a na da) (rb : IsRat…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
（共 39 条，此处仅展示前 30 条）
-/
theorem hasSum_geometric_two' (a : ℝ) : HasSum (fun n : ℕ ↦ a / 2 / 2 ^ n) a := by
  convert!
    HasSum.mul_left (a / 2)
      (hasSum_geometric_of_lt_one (le_of_lt one_half_pos) one_half_lt_one) using 1
  · funext n
    simp only [one_div, inv_pow]
    rfl
  · norm_num
/-
**summable_geometric_two'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_geometric_two' (a : Real) : Summable fun n : Nat => a / 2 / 2 ^ n
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasSum_geometric_two'`：hasSum_geometric_two' (a : Real) : HasSum (fun n 
: Nat => a / 2 / 2 ^ n) a
-/
theorem summable_geometric_two' (a : ℝ) : Summable fun n : ℕ ↦ a / 2 / 2 ^ n :=
  ⟨a, hasSum_geometric_two' a⟩
/-
**tsum_geometric_two'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_geometric_two' (a : Real) : ∑' n : Nat, a / 2 / 2 ^ n = a
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_geometric_two'`：hasSum_geometric_two' (a : Real) : HasSum (fun n 
: Nat => a / 2 / 2 ^ n) a
-/
theorem tsum_geometric_two' (a : ℝ) : ∑' n : ℕ, a / 2 / 2 ^ n = a :=
  (hasSum_geometric_two' a).tsum_eq

/-- **Sum of a Geometric Series** -/
/-
**NNReal.hasSum_geometric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNReal.hasSum_geometric {r : Real>=0} (hr : r < 1) : HasSum (fun n : Nat =
> r ^ n) (1 - r)⁻¹
参数：hr : r < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.hasSum_coe`：hasSum_coe {f : α -> Real>=0} {r : Real>=0} : HasSum 
(fun a => (f a : Real)) (r : Real) L ↔ HasSum f r L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_sub`：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `hasSum_geometric_of_lt_one`：hasSum_geometric_of_lt_one {r : Real} (h₁ : 
0 <= r) (h₂ : r < 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r

--- 原说明 ---
**Sum of a Geometric Series**
-/
theorem NNReal.hasSum_geometric {r : ℝ≥0} (hr : r < 1) : HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ := by
  apply NNReal.hasSum_coe.1
  push_cast
  rw [NNReal.coe_sub (le_of_lt hr)]
  exact hasSum_geometric_of_lt_one r.coe_nonneg hr
/-
**NNReal.summable_geometric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNReal.summable_geometric {r : Real>=0} (hr : r < 1) : Summable fun n : Na
t => r ^ n
参数：hr : r < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.hasSum_geometric`：NNReal.hasSum_geometric {r : Real>=0} (hr : r <
 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
-/
theorem NNReal.summable_geometric {r : ℝ≥0} (hr : r < 1) : Summable fun n : ℕ ↦ r ^ n :=
  ⟨_, NNReal.hasSum_geometric hr⟩
/-
**NNReal.tsum_geometric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNReal.tsum_geometric {r : Real>=0} (hr : r < 1) : ∑' n : Nat, r ^ n = (1 
- r)⁻¹
参数：hr : r < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `NNReal.hasSum_geometric`：NNReal.hasSum_geometric {r : Real>=0} (hr : r <
 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
-/
theorem NNReal.tsum_geometric {r : ℝ≥0} (hr : r < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  (NNReal.hasSum_geometric hr).tsum_eq

@[deprecated (since := "2026-03-18")] alias tsum_geometric_nnreal := NNReal.tsum_geometric

/-- The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite number,
and for `1 ≤ r` the RHS equals `∞`. -/
@[simp]
/-
**ENNReal.tsum_geometric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ENNReal.tsum_geometric (r : Real>=0∞) : ∑' n : Nat, r ^ n = (1 - r)⁻¹
参数：r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_coe`：lt_iff_exists_coe : a < b ↔ exists p : Real>=
0, a = p ∧ ↑p < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `ENNReal.coe_sub`：∀ {r p : NNReal}, ↑(r - p) = ↑r - ↑p
· 使用定理 `ENNReal.coe_one`：↑1 = 1
· 使用定理 `ENNReal.tsum_coe_eq`：∀ {α : Type u_1} {r : NNReal} {f : α → NNReal}, Has
Sum f r → ∑' (a : α), ↑(f a) = ↑r
· 使用定理 `NNReal.hasSum_geometric`：NNReal.hasSum_geometric {r : Real>=0} (hr : r <
 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `ENNReal.tsum_eq_iSup_nat`：∀ {f : ℕ → ENNReal}, ∑' (i : ℕ), f i = ⨆ i, ∑ 
a ∈ Finset.range i, f a
· 使用定理 `iSup_eq_top`：iSup_eq_top : iSup f = ⊤ ↔ forall b < ⊤, exists i, b < f i
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite numbe
r,
and for `1 ≤ r` the RHS equals `∞`.
-/
theorem ENNReal.tsum_geometric (r : ℝ≥0∞) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ := by
  rcases lt_or_ge r 1 with hr | hr
  · rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
    norm_cast at *
    convert! ENNReal.tsum_coe_eq (NNReal.hasSum_geometric hr)
    rw [ENNReal.coe_inv <| ne_of_gt <| tsub_pos_iff_lt.2 hr, coe_sub, coe_one]
  · rw [tsub_eq_zero_iff_le.mpr hr, ENNReal.inv_zero, ENNReal.tsum_eq_iSup_nat, iSup_eq_top]
    refine fun a ha ↦
      (ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 ha)).imp fun n hn ↦ lt_of_lt_of_le hn ?_
    calc
      (n : ℝ≥0∞) = ∑ i ∈ range n, 1 := by rw [sum_const, nsmul_one, card_range]
      _ ≤ ∑ i ∈ range n, r ^ i := by gcongr; apply one_le_pow₀ hr
/-
**ENNReal.tsum_geometric_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ENNReal.tsum_geometric_add_one (r : Real>=0∞) : ∑' n : Nat, r ^ (n + 1) = 
r * (1 - r)⁻¹
参数：r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `ENNReal.tsum_geometric`：ENNReal.tsum_geometric (r : Real>=0∞) : ∑' n : N
at, r ^ n = (1 - r)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ENNReal.tsum_geometric_add_one (r : ℝ≥0∞) : ∑' n : ℕ, r ^ (n + 1) = r * (1 - r)⁻¹ := by
  simp only [_root_.pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
/-
**ENNReal.tsum_two_zpow_neg_add_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ENNReal.tsum_two_zpow_neg_add_one : ∑' m : Nat, 2 ^ (-1 - m : Int) = (1 : 
Real>=0∞)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_sub_left`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -
a - b = -(b + a)
· 使用定理 `ENNReal.zpow_neg`：∀ (x : ENNReal) (m : ℤ), x ^ (-m) = (x ^ m)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `ENNReal.inv_pow`：∀ {a : ENNReal} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
· 使用定理 `ENNReal.tsum_geometric_add_one`：ENNReal.tsum_geometric_add_one (r : Real
>=0∞) : ∑' n : Nat, r ^ (n + 1) = r * (1 - r)⁻¹
· 使用定理 `ENNReal.one_sub_inv_two`：one_sub_inv_two : (1 : Real>=0∞) - 2⁻¹ = 2⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `NeZero.ne'`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], 0 ≠
 n
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `ENNReal.top_ne_ofNat`：∀ {n : ℕ} [inst : n.AtLeastTwo], ⊤ ≠ OfNat.ofNat n
-/
lemma ENNReal.tsum_two_zpow_neg_add_one :
    ∑' m : ℕ, 2 ^ (-1 - m : ℤ) = (1 : ℝ≥0∞) := by
  simp_rw [neg_sub_left, ENNReal.zpow_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add, zpow_natCast,
    ENNReal.inv_pow, ENNReal.tsum_geometric_add_one, one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 2)) (Ne.symm top_ne_ofNat)

open Encodable
/-
**ENNReal.tsum_geometric_two** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∑' (n : ℕ), 2⁻¹ ^ n = 2
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_geometric`：ENNReal.tsum_geometric (r : Real>=0∞) : ∑' n : N
at, r ^ n = (1 - r)⁻¹
· 使用定理 `ENNReal.one_sub_inv_two`：one_sub_inv_two : (1 : Real>=0∞) - 2⁻¹ = 2⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma ENNReal.tsum_geometric_two : ∑' n, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by simp
/-
**ENNReal.tsum_geometric_two_encode_le_two** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ENNReal.tsum_geometric_two_encode_le_two {ι : Type*} [Encodable ι] : ∑' i 
: ι, (2⁻¹ : Real>=0∞) ^ encode i <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.tsum_comp_le_tsum_of_injective`：tsum_comp_le_tsum_of_injective {
f : α -> β} (hf : Injective f) (g : β -> Real>=0∞) : ∑' x, g (f x) <= ∑' y, g y
· 使用定理 `Encodable.encode_injective`：∀ {α : Type u_1} [inst : Encodable α], Funct
ion.Injective Encodable.encode
· 使用定理 `ENNReal.tsum_geometric_two`：∑' (n : ℕ), 2⁻¹ ^ n = 2
-/
lemma ENNReal.tsum_geometric_two_encode_le_two {ι : Type*} [Encodable ι] :
    ∑' i : ι, (2⁻¹ : ℝ≥0∞) ^ encode i ≤ 2 :=
  (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_eq ENNReal.tsum_geometric_two
/-
**tsum_geometric_lt_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_geometric_lt_top {r : Real>=0∞} : ∑' n, r ^ n < ∞ ↔ r < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_geometric`：ENNReal.tsum_geometric (r : Real>=0∞) : ∑' n : N
at, r ^ n = (1 - r)⁻¹
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma tsum_geometric_lt_top {r : ℝ≥0∞} : ∑' n, r ^ n < ∞ ↔ r < 1 := by simp
/-
**tsum_geometric_encode_lt_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_geometric_encode_lt_top {r : Real>=0∞} (hr : r < 1) {ι : Type*} [Enco
dable ι] : ∑' i : ι, (r : Real>=0∞) ^ encode i < ∞
参数：hr : r < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ENNReal.tsum_comp_le_tsum_of_injective`：tsum_comp_le_tsum_of_injective {
f : α -> β} (hf : Injective f) (g : β -> Real>=0∞) : ∑' x, g (f x) <= ∑' y, g y
· 使用定理 `Encodable.encode_injective`：∀ {α : Type u_1} [inst : Encodable α], Funct
ion.Injective Encodable.encode
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_geometric`：ENNReal.tsum_geometric (r : Real>=0∞) : ∑' n : N
at, r ^ n = (1 - r)⁻¹
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
lemma tsum_geometric_encode_lt_top {r : ℝ≥0∞} (hr : r < 1) {ι : Type*} [Encodable ι] :
    ∑' i : ι, (r : ℝ≥0∞) ^ encode i < ∞ :=
  (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_lt <| by simpa

end Geometric

/-!
### Sequences with geometrically decaying distance in metric spaces

In this paragraph, we discuss sequences in metric spaces or emetric spaces for which the distance
between two consecutive terms decays geometrically. We show that such sequences are Cauchy
sequences, and bound their distances to the limit. We also discuss series with geometrically
decaying terms.
-/


section EDistLeGeometric

variable [PseudoEMetricSpace α] (r C : ℝ≥0∞) (hr : r < 1) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀ n, edist (f n) (f (n + 1)) ≤ C * r ^ n)

include hr hC hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence. -/
/-
**cauchySeq_of_edist_le_geometric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_edist_le_geometric : CauchySeq f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_of_edist_le_of_tsum_ne_top`：cauchySeq_of_edist_le_of_tsum_ne_t
op {f : Nat -> α} (d : Nat -> Real>=0∞) (hf : forall n, edist (f n) (f n.succ) <
= d n) (hd : tsum d != ∞) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `ENNReal.tsum_geometric`：ENNReal.tsum_geometric (r : Real>=0∞) : ∑' n : N
at, r ^ n = (1 - r)⁻¹
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.Finiteness.inv_ne_top`：∀ {a : ENNReal}, a ≠ 0 → a⁻¹ ≠ ⊤

--- 原说明 ---
If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence.
-/
theorem cauchySeq_of_edist_le_geometric : CauchySeq f := by
  refine cauchySeq_of_edist_le_of_tsum_ne_top _ hu ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  finiteness [(tsub_pos_iff_lt.2 hr).ne']

include hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
/-
**edist_le_of_edist_le_geometric_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝
 a)) (n : Nat) : edist (f n) a <= C * r ^ n / (1 - r)
参数：ha : Tendsto f atTop (𝓝 a)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `ENNReal.tsum_geometric`：ENNReal.tsum_geometric (r : Real>=0∞) : ∑' n : N
at, r ^ n = (1 - r)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `edist_le_tsum_of_edist_le_of_tendsto`：edist_le_tsum_of_edist_le_of_tends
to {f : Nat -> α} (d : Nat -> Real>=0∞) (hf : forall n, edist (f n) (f n.succ) <
= d n) {a : α} (ha : Tends…

--- 原说明 ---
If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`.
-/
theorem edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    edist (f n) a ≤ C * r ^ n / (1 - r) := by
  convert! edist_le_tsum_of_edist_le_of_tendsto _ hu ha _
  simp only [pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_geometric, div_eq_mul_inv, mul_assoc]

include hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
/-
**edist_le_of_edist_le_geometric_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝
 a)) (n : Nat) : edist (f n) a <= C * r ^ n / (1 - r)
参数：ha : Tendsto f atTop (𝓝 a)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `ENNReal.tsum_mul_left`：∀ {α : Type u_1} {a : ENNReal} {f : α → ENNReal},
 ∑' (i : α), a * f i = a * ∑' (i : α), f i
· 使用定理 `ENNReal.tsum_geometric`：ENNReal.tsum_geometric (r : Real>=0∞) : ∑' n : N
at, r ^ n = (1 - r)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `edist_le_tsum_of_edist_le_of_tendsto`：edist_le_tsum_of_edist_le_of_tends
to {f : Nat -> α} (d : Nat -> Real>=0∞) (hf : forall n, edist (f n) (f n.succ) <
= d n) {a : α} (ha : Tends…

--- 原说明 ---
If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`.
-/
theorem edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    edist (f 0) a ≤ C / (1 - r) := by
  simpa only [_root_.pow_zero, mul_one] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

end EDistLeGeometric

section EDistLeGeometricTwo

variable [PseudoEMetricSpace α] (C : ℝ≥0∞) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀ n, edist (f n) (f (n + 1)) ≤ C / 2 ^ n) {a : α} (ha : Tendsto f atTop (𝓝 a))

include hC hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequence. -/
/-
**cauchySeq_of_edist_le_geometric_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_edist_le_geometric_two : CauchySeq f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `cauchySeq_of_edist_le_geometric`：cauchySeq_of_edist_le_geometric : Cauch
ySeq f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.inv_pow`：∀ {a : ENNReal} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n

--- 原说明 ---
If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequen
ce.
-/
theorem cauchySeq_of_edist_le_geometric_two : CauchySeq f := by
  simp only [div_eq_mul_inv, ENNReal.inv_pow] at hu
  refine cauchySeq_of_edist_le_geometric 2⁻¹ C ?_ hC hu
  simp

include hu ha in
/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`. -/
/-
**edist_le_of_edist_le_geometric_two_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_of_edist_le_geometric_two_of_tendsto (n : Nat) : edist (f n) a <=
 2 * C / 2 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.inv_pow`：∀ {a : ENNReal} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.one_sub_inv_two`：one_sub_inv_two : (1 : Real>=0∞) - 2⁻¹ = 2⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `edist_le_of_edist_le_geometric_of_tendsto`：edist_le_of_edist_le_geometri
c_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat) : edist (f n) a <= C
 * r ^ n / (1 - r)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`.
-/
theorem edist_le_of_edist_le_geometric_two_of_tendsto (n : ℕ) : edist (f n) a ≤ 2 * C / 2 ^ n := by
  simp only [div_eq_mul_inv, ENNReal.inv_pow] at *
  rw [mul_assoc, mul_comm]
  convert! edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n using 1
  rw [ENNReal.one_sub_inv_two, div_eq_mul_inv, inv_inv]

include hu ha in
/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`. -/
/-
**edist_le_of_edist_le_geometric_two_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_of_edist_le_geometric_two_of_tendsto (n : Nat) : edist (f n) a <=
 2 * C / 2 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ENNReal.inv_pow`：∀ {a : ENNReal} {n : ℕ}, (a ^ n)⁻¹ = a⁻¹ ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.one_sub_inv_two`：one_sub_inv_two : (1 : Real>=0∞) - 2⁻¹ = 2⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `edist_le_of_edist_le_geometric_of_tendsto`：edist_le_of_edist_le_geometri
c_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat) : edist (f n) a <= C
 * r ^ n / (1 - r)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`.
-/
theorem edist_le_of_edist_le_geometric_two_of_tendsto₀ : edist (f 0) a ≤ 2 * C := by
  simpa only [_root_.pow_zero, div_eq_mul_inv, inv_one, mul_one] using
    edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

end EDistLeGeometricTwo

section LeGeometric

variable [PseudoMetricSpace α] {r C : ℝ} {f : ℕ → α}

section
variable (hr : r < 1) (hu : ∀ n, dist (f n) (f (n + 1)) ≤ C * r ^ n)
include hr hu

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence. -/
/-
**aux_hasSum_of_le_geometric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：aux_hasSum_of_le_geometric : HasSum (fun n : Nat => C * r ^ n) (C / (1 - r
))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sign_cases_of_C_mul_pow_nonneg`：sign_cases_of_C_mul_pow_nonneg [PosMulSt
rictMono R] (h : forall n, 0 <= a * b ^ n) : a = 0 ∨ 0 < a ∧ 0 <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `hasSum_geometric_of_lt_one`：hasSum_geometric_of_lt_one {r : Real} (h₁ : 
0 <= r) (h₂ : r < 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹

--- 原说明 ---
If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy
 sequence.
-/
theorem aux_hasSum_of_le_geometric : HasSum (fun n : ℕ ↦ C * r ^ n) (C / (1 - r)) := by
  rcases sign_cases_of_C_mul_pow_nonneg fun n ↦ dist_nonneg.trans (hu n) with (rfl | ⟨_, r₀⟩)
  · simp [hasSum_zero]
  · refine HasSum.mul_left C ?_
    simpa using hasSum_geometric_of_lt_one r₀ hr

variable (r C)

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`. -/
/-
**cauchySeq_of_le_geometric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_le_geometric : CauchySeq f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_of_dist_le_of_summable`：cauchySeq_of_dist_le_of_summable (d : 
Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n) (hd : Summable d) : C
auchySeq f
· 使用定理 `aux_hasSum_of_le_geometric`：aux_hasSum_of_le_geometric : HasSum (fun n :
 Nat => C * r ^ n) (C / (1 - r))

--- 原说明 ---
If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy
 sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`.
-/
theorem cauchySeq_of_le_geometric : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
/-
**dist_le_of_le_geometric_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_of_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n
 : Nat) : dist (f n) a <= C * r ^ n / (1 - r)
参数：ha : Tendsto f atTop (𝓝 a)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aux_hasSum_of_le_geometric`：aux_hasSum_of_le_geometric : HasSum (fun n :
 Nat => C * r ^ n) (C / (1 - r))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_right_comm`：mul_div_right_comm : a * b / c = a / c * b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `dist_le_tsum_of_dist_le_of_tendsto`：dist_le_tsum_of_dist_le_of_tendsto (
d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n) (hd : Summable d)
 {a : α} (ha : Tendsto f…

--- 原说明 ---
If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance fr
om
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`.
-/
theorem dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    dist (f 0) a ≤ C / (1 - r) :=
  (aux_hasSum_of_le_geometric hr hu).tsum_eq ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩ ha

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
/-
**dist_le_of_le_geometric_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_of_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n
 : Nat) : dist (f n) a <= C * r ^ n / (1 - r)
参数：ha : Tendsto f atTop (𝓝 a)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `aux_hasSum_of_le_geometric`：aux_hasSum_of_le_geometric : HasSum (fun n :
 Nat => C * r ^ n) (C / (1 - r))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_right_comm`：mul_div_right_comm : a * b / c = a / c * b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.mul_left`：HasSum.mul_left (a₂) (h : HasSum f a₁ L) : HasSum (fun 
i => a₂ * f i) (a₂ * a₁) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `dist_le_tsum_of_dist_le_of_tendsto`：dist_le_tsum_of_dist_le_of_tendsto (
d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n) (hd : Summable d)
 {a : α} (ha : Tendsto f…

--- 原说明 ---
If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance fr
om
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`.
-/
theorem dist_le_of_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ C * r ^ n / (1 - r) := by
  have := aux_hasSum_of_le_geometric hr hu
  convert! dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n
  simp only [pow_add, mul_left_comm C, mul_div_right_comm]
  rw [mul_comm]
  exact (this.mul_left _).tsum_eq.symm

end

variable (hu₂ : ∀ n, dist (f n) (f (n + 1)) ≤ C / 2 / 2 ^ n)
include hu₂

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy sequence. -/
/-
**cauchySeq_of_le_geometric_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_le_geometric_two : CauchySeq f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `cauchySeq_of_dist_le_of_summable`：cauchySeq_of_dist_le_of_summable (d : 
Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n) (hd : Summable d) : C
auchySeq f
· 使用定理 `hasSum_geometric_two'`：hasSum_geometric_two' (a : Real) : HasSum (fun n 
: Nat => a / 2 / 2 ^ n) a

--- 原说明 ---
If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy se
quence.
-/
theorem cauchySeq_of_le_geometric_two : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ hu₂ <| ⟨_, hasSum_geometric_two' C⟩

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`. -/
/-
**dist_le_of_le_geometric_two_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)
) (n : Nat) : dist (f n) a <= C / 2 ^ n
参数：ha : Tendsto f atTop (𝓝 a)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.div_const`：HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (
fun i => f i / b) (a / b) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `hasSum_geometric_two'`：hasSum_geometric_two' (a : Real) : HasSum (fun n 
: Nat => a / 2 / 2 ^ n) a
· 使用定理 `dist_le_tsum_of_dist_le_of_tendsto`：dist_le_tsum_of_dist_le_of_tendsto (
d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n) (hd : Summable d)
 {a : α} (ha : Tendsto f…
· 使用定理 `summable_geometric_two'`：summable_geometric_two' (a : Real) : Summable f
un n : Nat => a / 2 / 2 ^ n

--- 原说明 ---
If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`.
-/
theorem dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    dist (f 0) a ≤ C :=
  tsum_geometric_two' C ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`. -/
/-
**dist_le_of_le_geometric_two_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)
) (n : Nat) : dist (f n) a <= C / 2 ^ n
参数：ha : Tendsto f atTop (𝓝 a)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.div_const`：HasSum.div_const (h : HasSum f a L) (b : α) : HasSum (
fun i => f i / b) (a / b) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `hasSum_geometric_two'`：hasSum_geometric_two' (a : Real) : HasSum (fun n 
: Nat => a / 2 / 2 ^ n) a
· 使用定理 `dist_le_tsum_of_dist_le_of_tendsto`：dist_le_tsum_of_dist_le_of_tendsto (
d : Nat -> Real) (hf : forall n, dist (f n) (f n.succ) <= d n) (hd : Summable d)
 {a : α} (ha : Tendsto f…
· 使用定理 `summable_geometric_two'`：summable_geometric_two' (a : Real) : Summable f
un n : Nat => a / 2 / 2 ^ n

--- 原说明 ---
If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`.
-/
theorem dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ C / 2 ^ n := by
  convert! dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n
  simp only [add_comm n, pow_add, ← div_div]
  symm
  exact ((hasSum_geometric_two' C).div_const _).tsum_eq

end LeGeometric

/-! ### Summability tests based on comparison with geometric series -/


/-- A series whose terms are bounded by the terms of a converging geometric series converges. -/
/-
**summable_one_div_pow_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_one_div_pow_of_le {m : Real} {f : Nat -> Nat} (hm : 1 < m) (fi : 
forall i, i <= f i) : Summable fun i => 1 / m ^ f i
参数：hm : 1 < m；fi : forall i, i <= f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_div_le_one_div`：one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a
 <= 1 / b ↔ b <= a
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `pow_right_mono₀`：pow_right_mono₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (h 
: 1 <= a) : Monotone (a ^ ·)
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用引理 `one_div_nonneg`：one_div_nonneg : 0 <= 1 / a ↔ 0 <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `one_div_lt`：one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A series whose terms are bounded by the terms of a converging geometric series c
onverges.
-/
theorem summable_one_div_pow_of_le {m : ℝ} {f : ℕ → ℕ} (hm : 1 < m) (fi : ∀ i, i ≤ f i) :
    Summable fun i ↦ 1 / m ^ f i := by
  refine .of_nonneg_of_le (fun a ↦ by positivity) (fun a ↦ ?_)
      (summable_geometric_of_lt_one (one_div_nonneg.mpr (zero_le_one.trans hm.le))
        ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one.le.trans_lt hm)))
  rw [div_pow, one_pow]
  refine (one_div_le_one_div ?_ ?_).mpr (pow_right_mono₀ hm.le (fi a)) <;>
    exact pow_pos (zero_lt_one.trans hm) _

/-! ### Positive sequences with small sums on countable types -/


/-- For any positive `ε`, define on an encodable type a positive sequence with sum less than `ε` -/
/-
**posSumOfEncodable** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：posSumOfEncodable {ε : Real} (hε : 0 < ε) (ι) [Encodable ι] : { ε' : ι -> 
Real // (forall i, 0 < ε' i) ∧ exists c, HasSum ε' c ∧ c <= ε }
参数：hε : 0 < ε；ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `hasSum_geometric_two'`：hasSum_geometric_two' (a : Real) : HasSum (fun n 
: Nat => a / 2 / 2 ^ n) a

--- 原说明 ---
For any positive `ε`, define on an encodable type a positive sequence with sum l
ess than `ε`
-/
def posSumOfEncodable {ε : ℝ} (hε : 0 < ε) (ι) [Encodable ι] :
    { ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c ≤ ε } := by
  let f n := ε / 2 / 2 ^ n
  have hf : HasSum f ε := hasSum_geometric_two' _
  have f0 : ∀ n, 0 < f n := fun n ↦ div_pos (half_pos hε) (pow_pos zero_lt_two _)
  refine ⟨f ∘ Encodable.encode, fun i ↦ f0 _, ?_⟩
  rcases hf.summable.comp_injective (@Encodable.encode_injective ι _) with ⟨c, hg⟩
  refine ⟨c, hg, hasSum_le_inj _ (@Encodable.encode_injective ι _) ?_ ?_ hg hf⟩
  · intro i _
    exact le_of_lt (f0 _)
  · intro n
    exact le_rfl
/-
**Set.Countable.exists_pos_hasSum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Countable.exists_pos_hasSum_le {ι : Type*} {s : Set ι} (hs : s.Countab
le) {ε : Real} (hε : 0 < ε) : exists ε' : ι -> Real, (forall i, 0 < ε' i) ∧ exis
ts c, HasSum (fun i : s => ε' i) c ∧ c <= ε
参数：hs : s.Countable；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem Set.Countable.exists_pos_hasSum_le {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : ℝ}
    (hε : 0 < ε) : ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ ∃ c, HasSum (fun i : s ↦ ε' i) c ∧ c ≤ ε := by
  classical
  have := hs.toEncodable
  rcases posSumOfEncodable hε s with ⟨f, hf0, ⟨c, hfc, hcε⟩⟩
  refine ⟨fun i ↦ if h : i ∈ s then f ⟨i, h⟩ else 1, fun i ↦ ?_, ⟨c, ?_, hcε⟩⟩
  · conv_rhs => simp
    split_ifs
    exacts [hf0 _, zero_lt_one]
  · simpa only [Subtype.coe_prop, dif_pos, Subtype.coe_eta]
/-
**Set.Countable.exists_pos_forall_sum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Countable.exists_pos_forall_sum_le {ι : Type*} {s : Set ι} (hs : s.Cou
ntable) {ε : Real} (hε : 0 < ε) : exists ε' : ι -> Real, (forall i, 0 < ε' i) ∧ 
forall t : Finset ι, ↑t subseteq s -> ∑ i in t, ε' i <= ε
参数：hs : s.Countable；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.exists_pos_hasSum_le`：Set.Countable.exists_pos_hasSum_le {
ι : Type*} {s : Set ι} (hs : s.Countable) {ε : Real} (hε : 0 < ε) : exists ε' : 
ι -> Real, (forall i, 0 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subtype_of_mem`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι
} [inst : AddCommMonoid M] (f : ι → M) {p : ι → Prop}   [inst_1 : DecidablePred 
p], (∀ x ∈ s, p…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sum_le_hasSum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [
inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 :
 To…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Set.Countable.exists_pos_forall_sum_le {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : ℝ}
    (hε : 0 < ε) : ∃ ε' : ι → ℝ,
    (∀ i, 0 < ε' i) ∧ ∀ t : Finset ι, ↑t ⊆ s → ∑ i ∈ t, ε' i ≤ ε := by
  classical
  rcases hs.exists_pos_hasSum_le hε with ⟨ε', hpos, c, hε'c, hcε⟩
  refine ⟨ε', hpos, fun t ht ↦ ?_⟩
  rw [← sum_subtype_of_mem _ ht]
  refine (sum_le_hasSum _ ?_ hε'c).trans hcε
  exact fun _ _ ↦ (hpos _).le

namespace NNReal

/-
**NNReal.exists_pos_sum_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：exists_pos_sum_of_countable {ε : Real>=0} (hε : ε != 0) (ι) [Countable ι] 
: exists ε' : ι -> Real>=0, (forall i, 0 < ε' i) ∧ exists c, HasSum ε' c ∧ c < ε
参数：hε : ε != 0；ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_encodable`：nonempty_encodable (α : Type*) [Countable α] : Nonem
pty (Encodable α)
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_lt_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ < ↑r₂ ↔ r₁ < r₂
· 使用定理 `hasSum_le`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [inst
 : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : To…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `hasSum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [i
nst_1 : TopologicalSpace α] {L : SummationFilter β},   HasSum (fun x => 0) 0 L
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `NNReal.hasSum_coe`：hasSum_coe {f : α -> Real>=0} {r : Real>=0} : HasSum 
(fun a => (f a : Real)) (r : Real) L ↔ HasSum f r L
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
-/
theorem exists_pos_sum_of_countable {ε : ℝ≥0} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c < ε := by
  cases nonempty_encodable ι
  obtain ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε)
  obtain ⟨ε', hε', c, hc, hcε⟩ := posSumOfEncodable a0 ι
  exact
    ⟨fun i ↦ ⟨ε' i, (hε' i).le⟩, fun i ↦ NNReal.coe_lt_coe.1 <| hε' i,
      ⟨c, hasSum_le (fun i ↦ (hε' i).le) hasSum_zero hc⟩, NNReal.hasSum_coe.1 hc,
      aε.trans_le' <| NNReal.coe_le_coe.1 hcε⟩

end NNReal

namespace ENNReal

/-
**ENNReal.exists_pos_sum_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_pos_sum_of_countable {ε : Real>=0∞} (hε : ε != 0) (ι) [Countable ι]
 : exists ε' : ι -> Real>=0, (forall i, 0 < ε' i) ∧ (∑' i, (ε' i : Real>=0∞)) < 
ε
参数：hε : ε != 0；ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_coe`：lt_iff_exists_coe : a < b ↔ exists p : Real>=
0, a = p ∧ ↑p < b
· 使用定理 `NNReal.exists_pos_sum_of_countable`：exists_pos_sum_of_countable {ε : Rea
l>=0} (hε : ε != 0) (ι) [Countable ι] : exists ε' : ι -> Real>=0, (forall i, 0 <
 ε' i) ∧ exists c, HasSu…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_coe_eq`：∀ {α : Type u_1} {r : NNReal} {f : α → NNReal}, Has
Sum f r → ∑' (a : α), ↑(f a) = ↑r
-/
theorem exists_pos_sum_of_countable {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ (∑' i, (ε' i : ℝ≥0∞)) < ε := by
  rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, _⟩
  rcases NNReal.exists_pos_sum_of_countable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩
  exact ⟨ε', hp, (ENNReal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩
/-
**ENNReal.exists_pos_sum_of_countable'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_pos_sum_of_countable' {ε : Real>=0∞} (hε : ε != 0) (ι) [Countable ι
] : exists ε' : ι -> Real>=0∞, (forall i, 0 < ε' i) ∧ ∑' i, ε' i < ε
参数：hε : ε != 0；ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.exists_pos_sum_of_countable`：exists_pos_sum_of_countable {ε : Re
al>=0∞} (hε : ε != 0) (ι) [Countable ι] : exists ε' : ι -> Real>=0, (forall i, 0
 < ε' i) ∧ (∑' i, (ε' i :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
-/
theorem exists_pos_sum_of_countable' {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0∞, (∀ i, 0 < ε' i) ∧ ∑' i, ε' i < ε :=
  let ⟨δ, δpos, hδ⟩ := exists_pos_sum_of_countable hε ι
  ⟨fun i ↦ δ i, fun i ↦ ENNReal.coe_pos.2 (δpos i), hδ⟩
/-
**ENNReal.exists_pos_tsum_mul_lt_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal
`。
形式化陈述：exists_pos_tsum_mul_lt_of_countable {ε : Real>=0∞} (hε : ε != 0) {ι} [Coun
table ι] (w : ι -> Real>=0∞) (hw : forall i, w i != ∞) : exists δ : ι -> Real>=0
, (forall i, 0 < δ i) ∧ (∑' i, (w i * δ i : Real>=0∞)) < ε
参数：hε : ε != 0；w : ι -> Real>=0∞；hw : forall i, w i != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ENNReal.exists_pos_sum_of_countable`：exists_pos_sum_of_countable {ε : Re
al>=0∞} (hε : ε != 0) (ι) [Countable ι] : exists ε' : ι -> Real>=0, (forall i, 0
 < ε' i) ∧ (∑' i, (ε' i :…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_div`：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.mul_le_of_le_div'`：mul_le_of_le_div' (h : a <= b / c) : c * a <=
 b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `ENNReal.div_le_div`：∀ {a b c d : ENNReal}, a ≤ b → d ≤ c → a / c ≤ b / d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.coe_le_coe._gcongr_2`：∀ {r q : NNReal}, r ≤ q → ↑r ≤ ↑q
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem exists_pos_tsum_mul_lt_of_countable {ε : ℝ≥0∞} (hε : ε ≠ 0) {ι} [Countable ι] (w : ι → ℝ≥0∞)
    (hw : ∀ i, w i ≠ ∞) : ∃ δ : ι → ℝ≥0, (∀ i, 0 < δ i) ∧ (∑' i, (w i * δ i : ℝ≥0∞)) < ε := by
  lift w to ι → ℝ≥0 using hw
  rcases exists_pos_sum_of_countable hε ι with ⟨δ', Hpos, Hsum⟩
  have : ∀ i, 0 < max 1 (w i) := fun i ↦ zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨fun i ↦ δ' i / max 1 (w i), fun i ↦ div_pos (Hpos _) (this i), ?_⟩
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i ↦ ?_) Hsum
  rw [coe_div (this i).ne']
  refine mul_le_of_le_div' ?_
  grw [← le_max_right]

end ENNReal

/-!
### Factorial
-/


/-
**factorial_tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：factorial_tendsto_atTop : Tendsto Nat.factorial atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_atTop_of_monotone`：tendsto_atTop_atTop_of_monotone 
[Preorder α] [Preorder β] {f : α -> β} (hf : Monotone f) (h : forall b, exists a
, b <= f a) : Tendsto f atTo…
· 使用定理 `Nat.factorial_le`：factorial_le {m n} (h : m <= n) : m ! <= n !
· 使用定理 `Nat.self_le_factorial`：∀ (n : ℕ), n ≤ n.factorial

--- 原说明 ---
### Factorial
-/
theorem factorial_tendsto_atTop : Tendsto Nat.factorial atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ ↦ Nat.factorial_le) fun n ↦ ⟨n, n.self_le_factorial⟩
/-
**tendsto_factorial_div_pow_self_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_factorial_div_pow_self_atTop : Tendsto (fun n => n ! / (n : Real) 
^ n : Nat -> Real) atTop (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_const_div_atTop_nhds_zero_nat`：tendsto_const_div_atTop_nhds_zero
_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [Continu
ousSMul Rat>=0 𝕜] [Continuo…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNRat.instContinuousSMulOfIsScalarTowerOfRat`：∀ {R : Type u_1} [inst : T
opologicalSpace R] [inst_1 : MulAction ℚ R] [inst_2 : MulAction ℚ≥0 R] [IsScalar
Tower ℚ≥0 ℚ R]   [ContinuousSMul ℚ…
· 使用定理 `NNRat.instContinuousSMulRatReal`：ContinuousSMul ℚ ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
（共 63 条，此处仅展示前 30 条）
-/
theorem tendsto_factorial_div_pow_self_atTop :
    Tendsto (fun n ↦ n ! / (n : ℝ) ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat 1)
    (Eventually.of_forall fun n ↦
      div_nonneg (mod_cast n.factorial_pos.le)
        (pow_nonneg (mod_cast n.zero_le) _))
    (by
      refine (eventually_gt_atTop 0).mono fun n hn ↦ ?_
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne.symm with ⟨k, rfl⟩
      rw [factorial_eq_prod_range_add_one, pow_eq_prod_const, div_eq_mul_inv, ← inv_eq_one_div,
        prod_natCast, Nat.cast_succ, ← Finset.prod_inv_distrib, ← prod_mul_distrib,
        Finset.prod_range_succ']
      simp only [one_mul, Nat.cast_add, zero_add, Nat.cast_one]
      refine
            mul_le_of_le_one_left (inv_nonneg.mpr <| mod_cast hn.le) (prod_le_one ?_ ?_) <;>
          intro x hx <;>
        rw [Finset.mem_range] at hx
      · positivity
      · refine (div_le_one <| mod_cast hn).mpr ?_
        norm_cast
        lia)

/-!
### Ceil and floor
-/


section

/-
**tendsto_nat_floor_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nat_floor_atTop {α : Type*} [Semiring α] [LinearOrder α] [IsStrict
OrderedRing α] [FloorSemiring α] : Tendsto (fun x : α => ⌊x⌋₊) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Nat.floor_mono`：floor_mono : Monotone (floor : R -> Nat)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem tendsto_nat_floor_atTop {α : Type*}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] :
    Tendsto (fun x : α ↦ ⌊x⌋₊) atTop atTop :=
  Nat.floor_mono.tendsto_atTop_atTop fun x ↦ ⟨max 0 (x + 1), by simp [Nat.le_floor_iff]⟩
/-
**tendsto_nat_ceil_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_nat_ceil_atTop {α : Type*} [Semiring α] [LinearOrder α] [IsStrictO
rderedRing α] [FloorSemiring α] : Tendsto (fun x : α => ⌈x⌉₊) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Nat.ceil_mono`：ceil_mono : Monotone (ceil : R -> Nat)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.ceil_natCast`：ceil_natCast (n : Nat) : ⌈(n : R)⌉₊ = n
-/
lemma tendsto_nat_ceil_atTop {α : Type*}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] :
    Tendsto (fun x : α ↦ ⌈x⌉₊) atTop atTop := by
  refine Nat.ceil_mono.tendsto_atTop_atTop (fun x ↦ ⟨x, ?_⟩)
  simp only [Nat.ceil_natCast, le_refl]
/-
**tendsto_nat_floor_mul_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_nat_floor_mul_atTop {α : Type _} [Semifield α] [LinearOrder α] [Is
StrictOrderedRing α] [FloorSemiring α] [Archimedean α] (a : α) (ha : 0 < a) : Te
ndsto (fun (x : Nat) => ⌊a * x⌋₊) atTop atTop
参数：a : α；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_nat_floor_atTop`：tendsto_nat_floor_atTop {α : Type*} [Semiring α
] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] : Tendsto (fun x : α
 => ⌊x⌋₊) atT…
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
lemma tendsto_nat_floor_mul_atTop {α : Type _}
    [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α]
    [Archimedean α] (a : α) (ha : 0 < a) : Tendsto (fun (x : ℕ) => ⌊a * x⌋₊) atTop atTop :=
  Tendsto.comp tendsto_nat_floor_atTop
    <| Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop

variable {R : Type*} [TopologicalSpace R] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [OrderTopology R] [FloorRing R]
/-
**tendsto_nat_floor_mul_div_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nat_floor_mul_div_atTop {a : R} (ha : 0 <= a) : Tendsto (fun x => 
(⌊a * x⌋₊ : R) / x) atTop (𝓝 a)
参数：ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `FloorRing.archimedean`：∀ (K : Type u_5) [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K] [FloorRing K], Archimedean K
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1
（共 76 条，此处仅展示前 30 条）
-/
theorem tendsto_nat_floor_mul_div_atTop {a : R} (ha : 0 ≤ a) :
    Tendsto (fun x ↦ (⌊a * x⌋₊ : R) / x) atTop (𝓝 a) := by
  have A : Tendsto (fun x : R ↦ a - x⁻¹) atTop (𝓝 (a - 0)) :=
    tendsto_const_nhds.sub tendsto_inv_atTop_zero
  rw [sub_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' A tendsto_const_nhds
  · refine eventually_atTop.2 ⟨1, fun x hx ↦ ?_⟩
    simp only [le_div_iff₀ (zero_lt_one.trans_le hx), _root_.sub_mul,
      inv_mul_cancel₀ (zero_lt_one.trans_le hx).ne']
    have := Nat.lt_floor_add_one (a * x)
    linarith
  · refine eventually_atTop.2 ⟨1, fun x hx ↦ ?_⟩
    rw [div_le_iff₀ (zero_lt_one.trans_le hx)]
    simp [Nat.floor_le (mul_nonneg ha (zero_le_one.trans hx))]
/-
**tendsto_nat_floor_div_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nat_floor_div_atTop : Tendsto (fun x => (⌊x⌋₊ : R) / x) atTop (𝓝 1
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `tendsto_nat_floor_mul_div_atTop`：tendsto_nat_floor_mul_div_atTop {a : R}
 (ha : 0 <= a) : Tendsto (fun x => (⌊a * x⌋₊ : R) / x) atTop (𝓝 a)
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
-/
theorem tendsto_nat_floor_div_atTop : Tendsto (fun x ↦ (⌊x⌋₊ : R) / x) atTop (𝓝 1) := by
  simpa using tendsto_nat_floor_mul_div_atTop (zero_le_one' R)
/-
**tendsto_nat_ceil_mul_div_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nat_ceil_mul_div_atTop {a : R} (ha : 0 <= a) : Tendsto (fun x => (
⌈a * x⌉₊ : R) / x) atTop (𝓝 a)
参数：ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `FloorRing.archimedean`：∀ (K : Type u_5) [inst : Field K] [inst_1 : Linea
rOrder K] [IsStrictOrderedRing K] [FloorRing K], Archimedean K
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `Nat.le_ceil`：le_ceil (a : R) : a <= ⌈a⌉₊
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
（共 41 条，此处仅展示前 30 条）
-/
theorem tendsto_nat_ceil_mul_div_atTop {a : R} (ha : 0 ≤ a) :
    Tendsto (fun x ↦ (⌈a * x⌉₊ : R) / x) atTop (𝓝 a) := by
  have A : Tendsto (fun x : R ↦ a + x⁻¹) atTop (𝓝 (a + 0)) :=
    tendsto_const_nhds.add tendsto_inv_atTop_zero
  rw [add_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A
  · refine eventually_atTop.2 ⟨1, fun x hx ↦ ?_⟩
    rw [le_div_iff₀ (zero_lt_one.trans_le hx)]
    exact Nat.le_ceil _
  · refine eventually_atTop.2 ⟨1, fun x hx ↦ ?_⟩
    simp [div_le_iff₀ (zero_lt_one.trans_le hx), inv_mul_cancel₀ (zero_lt_one.trans_le hx).ne',
      (Nat.ceil_lt_add_one (mul_nonneg ha (zero_le_one.trans hx))).le, add_mul]
/-
**tendsto_nat_ceil_div_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nat_ceil_div_atTop : Tendsto (fun x => (⌈x⌉₊ : R) / x) atTop (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `tendsto_nat_ceil_mul_div_atTop`：tendsto_nat_ceil_mul_div_atTop {a : R} (
ha : 0 <= a) : Tendsto (fun x => (⌈a * x⌉₊ : R) / x) atTop (𝓝 a)
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
-/
theorem tendsto_nat_ceil_div_atTop : Tendsto (fun x ↦ (⌈x⌉₊ : R) / x) atTop (𝓝 1) := by
  simpa using tendsto_nat_ceil_mul_div_atTop (zero_le_one' R)
/-
**Nat.tendsto_div_const_atTop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.tendsto_div_const_atTop {n : Nat} (hn : n != 0) : Tendsto (· / n) atTo
p atTop
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Tendsto.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (l₁ : F
ilter α) (l₂ : Filter β),   Filter.Tendsto f l₁ l₂ = (Filter.map f l₁ ≤ l₂)
· 使用定理 `Filter.map_div_atTop_eq_nat`：map_div_atTop_eq_nat (k : Nat) (hk : 0 < k)
 : map (fun a => a / k) atTop = atTop
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma Nat.tendsto_div_const_atTop {n : ℕ} (hn : n ≠ 0) : Tendsto (· / n) atTop atTop := by
  rw [Tendsto, map_div_atTop_eq_nat n hn.bot_lt]

end

