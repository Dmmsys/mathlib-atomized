/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Definition of `mulExpNegMulSq` and properties

`mulExpNegMulSq` is the mapping `fun (ε : ℝ) (x : ℝ) => x * Real.exp (- (ε * x * x))`. By
composition, it can be used to transform a function `g : E → ℝ` into a bounded function
`mulExpNegMulSq ε ∘ g : E → ℝ = fun x => g x * Real.exp (-ε * g x * g x)` with useful
boundedness and convergence properties.

## Main Properties

- `abs_mulExpNegMulSq_le`: For fixed `ε > 0`, the mapping `x ↦ mulExpNegMulSq ε x` is
  bounded by `Real.sqrt ε⁻¹`;
- `tendsto_mulExpNegMulSq`: For fixed `x : ℝ`, the mapping `mulExpNegMulSq ε x`
  converges pointwise to `x` as `ε → 0`;
- `lipschitzWith_one_mulExpNegMulSq`: For fixed `ε > 0`, the mapping `mulExpNegMulSq ε` is
  Lipschitz with constant `1`;
- `abs_mulExpNegMulSq_comp_le_norm`: For a fixed bounded continuous function `g`, the mapping
  `mulExpNegMulSq ε ∘ g` is bounded by `norm g`, uniformly in `ε ≥ 0`;
-/

@[expose] public section

open NNReal ENNReal BoundedContinuousFunction Filter

open scoped Topology

namespace Real

/-! ### Definition and properties of `fun x => x * Real.exp (- (ε * x * x))` -/

/--
Mapping `fun ε x => x * Real.exp (- (ε * x * x))`. By composition, it can be used to transform
functions into bounded functions.
-/
noncomputable
/-
**Real.mulExpNegMulSq** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：mulExpNegMulSq (ε x : Real)
参数：ε x : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulExpNegMulSq (ε x : ℝ) := x * exp (-(ε * x * x))
/-
**Real.mulExpNegSq_apply** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mulExpNegSq_apply (ε x : Real) : mulExpNegMulSq ε x = x * exp (-(ε * x * x
))
参数：ε x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulExpNegSq_apply (ε x : ℝ) : mulExpNegMulSq ε x = x * exp (-(ε * x * x)) := rfl
/-
**Real.neg_mulExpNegMulSq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：neg_mulExpNegMulSq_neg (ε x : Real) : - mulExpNegMulSq ε (-x) = mulExpNegM
ulSq ε x
参数：ε x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_mulExpNegMulSq_neg (ε x : ℝ) : - mulExpNegMulSq ε (-x) = mulExpNegMulSq ε x := by
  simp [mulExpNegMulSq]
/-
**Real.mulExpNegMulSq_one_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：mulExpNegMulSq_one_le_one (x : Real) : mulExpNegMulSq 1 x <= 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 86 条，此处仅展示前 30 条）
-/
theorem mulExpNegMulSq_one_le_one (x : ℝ) : mulExpNegMulSq 1 x ≤ 1 := by
  simp only [mulExpNegMulSq, one_mul]
  rw [← le_div_iff₀ (exp_pos (-(x * x))), exp_neg, div_inv_eq_mul, one_mul]
  apply le_trans _ (add_one_le_exp (x * x))
  nlinarith
/-
**Real.neg_one_le_mulExpNegMulSq_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：neg_one_le_mulExpNegMulSq_one (x : Real) : -1 <= mulExpNegMulSq 1 x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.neg_mulExpNegMulSq_neg`：neg_mulExpNegMulSq_neg (ε x : Real) : - mul
ExpNegMulSq ε (-x) = mulExpNegMulSq ε x
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.mulExpNegMulSq_one_le_one`：mulExpNegMulSq_one_le_one (x : Real) : m
ulExpNegMulSq 1 x <= 1
-/
theorem neg_one_le_mulExpNegMulSq_one (x : ℝ) : -1 ≤ mulExpNegMulSq 1 x := by
  rw [← neg_mulExpNegMulSq_neg, neg_le_neg_iff]
  exact mulExpNegMulSq_one_le_one (-x)
/-
**Real.abs_mulExpNegMulSq_one_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_mulExpNegMulSq_one_le_one (x : Real) : |mulExpNegMulSq 1 x| <= 1
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Real.neg_one_le_mulExpNegMulSq_one`：neg_one_le_mulExpNegMulSq_one (x : R
eal) : -1 <= mulExpNegMulSq 1 x
· 使用定理 `Real.mulExpNegMulSq_one_le_one`：mulExpNegMulSq_one_le_one (x : Real) : m
ulExpNegMulSq 1 x <= 1
-/
theorem abs_mulExpNegMulSq_one_le_one (x : ℝ) : |mulExpNegMulSq 1 x| ≤ 1 :=
  abs_le.mpr ⟨neg_one_le_mulExpNegMulSq_one x, mulExpNegMulSq_one_le_one x⟩

variable {ε : ℝ}

@[continuity, fun_prop]
/-
**Real.continuous_mulExpNegMulSq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：continuous_mulExpNegMulSq : Continuous (fun x => mulExpNegMulSq ε x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `Continuous.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : 
X → G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
-/
theorem continuous_mulExpNegMulSq : Continuous (fun x => mulExpNegMulSq ε x) :=
  Continuous.mul continuous_id (by fun_prop)

@[continuity, fun_prop]
/-
**Real._root_.Continuous.mulExpNegMulSq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.mulExpNegMulSq {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : Continuous f) : Continuous (fun x => mulExpNegMulSq ε (f x)) :=
  continuous_mulExpNegMulSq.comp hf
/-
**Real.differentiableAt_mulExpNegMulSq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_mulExpNegMulSq (y : Real) : DifferentiableAt Real (mulExp
NegMulSq ε) y
参数：y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.mul`：DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x)
 (hb : DifferentiableAt 𝕜 b x) : DifferentiableAt 𝕜 (a * b) x
· 使用定理 `differentiableAt_fun_id`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [in
st_3 : Topolo…
· 使用定理 `DifferentiableAt.exp`：DifferentiableAt.exp (hc : DifferentiableAt Real f
 x) : DifferentiableAt Real (fun x => Real.exp (f x)) x
· 使用定理 `DifferentiableAt.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `DifferentiableAt.fun_mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {x : E} {𝔸 :…
· 使用定理 `DifferentiableAt.const_mul`：DifferentiableAt.const_mul (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => b * a y) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
-/
theorem differentiableAt_mulExpNegMulSq (y : ℝ) :
    DifferentiableAt ℝ (mulExpNegMulSq ε) y :=
  DifferentiableAt.mul differentiableAt_fun_id (by fun_prop)
/-
**Real.differentiable_mulExpNegMulSq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {ε : ℝ}, Differentiable ℝ ε.mulExpNegMulSq
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.differentiableAt_mulExpNegMulSq`：differentiableAt_mulExpNegMulSq (y
 : Real) : DifferentiableAt Real (mulExpNegMulSq ε) y
-/
@[fun_prop] theorem differentiable_mulExpNegMulSq : Differentiable ℝ (mulExpNegMulSq ε) :=
  fun _ => differentiableAt_mulExpNegMulSq _
/-
**Real.hasDerivAt_mulExpNegMulSq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_mulExpNegMulSq (y : Real) : HasDerivAt (mulExpNegMulSq ε) (exp 
(-(ε * y * y)) + y * (exp (-(ε * y * y)) * (-2 * ε * y))) y
参数：y : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `HasDerivAt.mul`：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) : HasDerivAt (c * d) (c' * d x + c x * d') x
· 使用定理 `hasDerivAt_id'`：hasDerivAt_id' : HasDerivAt (fun x : 𝕜 => x) 1 x
· 使用定理 `HasDerivAt.exp`：HasDerivAt.exp (hf : HasDerivAt f f' x) : HasDerivAt (fu
n x => Real.exp (f x)) (Real.exp (f x) * f') x
· 使用定理 `HasDerivAt.congr_deriv`：HasDerivAt.congr_deriv (h : HasDerivAt f f' x) (
h' : f' = g') : HasDerivAt f g' x
· 使用定理 `HasDerivAt.neg`：HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f)
 (-f') x
· 使用定理 `HasDerivAt.const_mul`：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d'
 x) : HasDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
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
（共 45 条，此处仅展示前 30 条）
-/
theorem hasDerivAt_mulExpNegMulSq (y : ℝ) :
    HasDerivAt (mulExpNegMulSq ε)
    (exp (-(ε * y * y)) + y * (exp (-(ε * y * y)) * (-2 * ε * y))) y := by
  nth_rw 1 [← one_mul (exp (-(ε * y * y)))]
  apply HasDerivAt.mul (hasDerivAt_id' y)
  apply HasDerivAt.exp (HasDerivAt.congr_deriv (HasDerivAt.neg
    (HasDerivAt.mul (HasDerivAt.const_mul ε (hasDerivAt_id' y)) (hasDerivAt_id' y))) (by ring))
/-
**Real.deriv_mulExpNegMulSq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_mulExpNegMulSq (y : Real) : deriv (mulExpNegMulSq ε) y = exp (-(ε * 
y * y)) + y * (exp (-(ε * y * y)) * (-2 * ε * y))
参数：y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.hasDerivAt_mulExpNegMulSq`：hasDerivAt_mulExpNegMulSq (y : Real) : H
asDerivAt (mulExpNegMulSq ε) (exp (-(ε * y * y)) + y * (exp (-(ε * y * y)) * (-2
 * ε * y))) y
-/
theorem deriv_mulExpNegMulSq (y : ℝ) : deriv (mulExpNegMulSq ε) y =
    exp (-(ε * y * y)) + y * (exp (-(ε * y * y)) * (-2 * ε * y)) :=
  HasDerivAt.deriv (hasDerivAt_mulExpNegMulSq y)
/-
**Real.norm_deriv_mulExpNegMulSq_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：norm_deriv_mulExpNegMulSq_le_one (hε : 0 < ε) (x : Real) : ‖deriv (mulExpN
egMulSq ε) x‖ <= 1
参数：hε : 0 < ε；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.deriv_mulExpNegMulSq`：deriv_mulExpNegMulSq (y : Real) : deriv (mulE
xpNegMulSq ε) y = exp (-(ε * y * y)) + y * (exp (-(ε * y * y)) * (-2 * ε * y))
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
（共 77 条，此处仅展示前 30 条）
-/
theorem norm_deriv_mulExpNegMulSq_le_one (hε : 0 < ε) (x : ℝ) :
    ‖deriv (mulExpNegMulSq ε) x‖ ≤ 1 := by
  rw [norm_eq_abs, deriv_mulExpNegMulSq]
  have heq : exp (-(ε * x * x)) + x * (exp (-(ε * x * x)) * (-2 * ε * x))
      = exp (-(ε * x * x)) * (1 - 2 * (ε * x * x)) := by ring
  rw [heq, abs_mul, abs_exp]
  set y := ε * x * x with hy
  have hynonneg : 0 ≤ y := by
    rw [hy, mul_assoc]
    exact mul_nonneg hε.le (mul_self_nonneg x)
  apply mul_le_of_le_inv_mul₀ (zero_le_one' ℝ) (exp_nonneg _)
  simp only [← exp_neg (-y), neg_neg, mul_one, abs_le, neg_le_sub_iff_le_add, tsub_le_iff_right]
  refine ⟨le_trans two_mul_le_exp ((le_add_iff_nonneg_left (exp y)).mpr zero_le_one), ?_⟩
  exact le_trans (one_le_exp hynonneg) (le_add_of_nonneg_right (by simp [hynonneg]))
/-
**Real.nnnorm_deriv_mulExpNegMulSq_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：nnnorm_deriv_mulExpNegMulSq_le_one (hε : 0 < ε) (x : Real) : ‖deriv (mulEx
pNegMulSq ε) x‖₊ <= 1
参数：hε : 0 < ε；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `Real.norm_deriv_mulExpNegMulSq_le_one`：norm_deriv_mulExpNegMulSq_le_one 
(hε : 0 < ε) (x : Real) : ‖deriv (mulExpNegMulSq ε) x‖ <= 1
-/
theorem nnnorm_deriv_mulExpNegMulSq_le_one (hε : 0 < ε) (x : ℝ) :
    ‖deriv (mulExpNegMulSq ε) x‖₊ ≤ 1 := by
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact norm_deriv_mulExpNegMulSq_le_one hε x

/-- For fixed `ε > 0`, the mapping `mulExpNegMulSq ε` is Lipschitz with constant `1` -/
/-
**Real.lipschitzWith_one_mulExpNegMulSq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：lipschitzWith_one_mulExpNegMulSq (hε : 0 < ε) : LipschitzWith 1 (mulExpNeg
MulSq ε)
参数：hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lipschitzWith_of_nnnorm_deriv_le`：∀ {𝕜 : Type u_3} {G : Type u_4} [inst 
: RCLike 𝕜] [inst_1 : NormedAddCommGroup G] [inst_2 : NormedSpace 𝕜 G] {f : 𝕜 → 
G}   {C : NNReal}, Dif…
· 使用定理 `Real.differentiable_mulExpNegMulSq`：∀ {ε : ℝ}, Differentiable ℝ ε.mulExp
NegMulSq
· 使用定理 `Real.nnnorm_deriv_mulExpNegMulSq_le_one`：nnnorm_deriv_mulExpNegMulSq_le_
one (hε : 0 < ε) (x : Real) : ‖deriv (mulExpNegMulSq ε) x‖₊ <= 1

--- 原说明 ---
For fixed `ε > 0`, the mapping `mulExpNegMulSq ε` is Lipschitz with constant `1`
-/
theorem lipschitzWith_one_mulExpNegMulSq (hε : 0 < ε) :
    LipschitzWith 1 (mulExpNegMulSq ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_mulExpNegMulSq
  exact nnnorm_deriv_mulExpNegMulSq_le_one hε
/-
**Real.mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one** 是 Mathlib 中的一个定理，位于命名空间 `
Real`。
形式化陈述：mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one (hε : 0 < ε) (x : Real) : mu
lExpNegMulSq ε x = (√ε)⁻¹ * mulExpNegMulSq 1 (sqrt ε * x)
参数：hε : 0 < ε；x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one (hε : 0 < ε) (x : ℝ) :
    mulExpNegMulSq ε x = (√ε)⁻¹ * mulExpNegMulSq 1 (sqrt ε * x) := by
  grind [mulExpNegMulSq]

/-- For fixed `ε > 0`, the mapping `x ↦ mulExpNegMulSq ε x` is bounded by `(√ε)⁻¹`. -/
/-
**Real.abs_mulExpNegMulSq_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_mulExpNegMulSq_le (hε : 0 < ε) {x : Real} : |mulExpNegMulSq ε x| <= (√
ε)⁻¹
参数：hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one`：mulExpNegMulSq_eq_sq
rt_mul_mulExpNegMulSq_one (hε : 0 < ε) (x : Real) : mulExpNegMulSq ε x = (√ε)⁻¹ 
* mulExpNegMulSq 1 (sqrt ε * x)
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.abs_mulExpNegMulSq_one_le_one`：abs_mulExpNegMulSq_one_le_one (x : R
eal) : |mulExpNegMulSq 1 x| <= 1

--- 原说明 ---
For fixed `ε > 0`, the mapping `x ↦ mulExpNegMulSq ε x` is bounded by `(√ε)⁻¹`.
-/
theorem abs_mulExpNegMulSq_le (hε : 0 < ε) {x : ℝ} : |mulExpNegMulSq ε x| ≤ (√ε)⁻¹ := by
  rw [mulExpNegMulSq_eq_sqrt_mul_mulExpNegMulSq_one hε x, abs_mul, abs_of_pos (by positivity)]
  apply mul_le_of_le_one_right
  · positivity
  · exact abs_mulExpNegMulSq_one_le_one (√ε * x)
/-
**Real.dist_mulExpNegMulSq_le_two_mul_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dist_mulExpNegMulSq_le_two_mul_sqrt (hε : 0 < ε) (x y : Real) : dist (mulE
xpNegMulSq ε x) (mulExpNegMulSq ε y) <= 2 * (√ε)⁻¹
参数：hε : 0 < ε；x y : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `dist_zero_left`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 
dist 0 a = ‖a‖
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.abs_mulExpNegMulSq_le`：abs_mulExpNegMulSq_le (hε : 0 < ε) {x : Real
} : |mulExpNegMulSq ε x| <= (√ε)⁻¹
-/
theorem dist_mulExpNegMulSq_le_two_mul_sqrt (hε : 0 < ε) (x y : ℝ) :
    dist (mulExpNegMulSq ε x) (mulExpNegMulSq ε y) ≤ 2 * (√ε)⁻¹ := by
  apply le_trans (dist_triangle (mulExpNegMulSq ε x) 0 (mulExpNegMulSq ε y))
  simp only [dist_zero_right, norm_eq_abs, dist_zero_left, two_mul]
  exact add_le_add (abs_mulExpNegMulSq_le hε) (abs_mulExpNegMulSq_le hε)
/-
**Real.dist_mulExpNegMulSq_le_dist** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：dist_mulExpNegMulSq_le_dist (hε : 0 < ε) {x y : Real} : dist (mulExpNegMul
Sq ε x) (mulExpNegMulSq ε y) <= dist x y
参数：hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.lipschitzWith_one_mulExpNegMulSq`：lipschitzWith_one_mulExpNegMulSq 
(hε : 0 < ε) : LipschitzWith 1 (mulExpNegMulSq ε)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_le_toReal`：toReal_le_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal <= b.toReal ↔ a <= b
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ENNReal.coe_one`：↑1 = 1
-/
theorem dist_mulExpNegMulSq_le_dist (hε : 0 < ε) {x y : ℝ} :
    dist (mulExpNegMulSq ε x) (mulExpNegMulSq ε y) ≤ dist x y := by
  have h := lipschitzWith_one_mulExpNegMulSq hε x y
  rwa [ENNReal.coe_one, one_mul, ← (toReal_le_toReal (edist_ne_top _ _) (edist_ne_top _ _))] at h

/-- For fixed `x : ℝ`, the mapping `mulExpNegMulSq ε x` converges pointwise to `x` as `ε → 0` -/
/-
**Real.tendsto_mulExpNegMulSq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：tendsto_mulExpNegMulSq {x : Real} : Tendsto (fun ε => mulExpNegMulSq ε x) 
(𝓝 0) (𝓝 x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Continuous.rexp`：Continuous.rexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `Continuous.fun_neg`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Neg G]   [ContinuousNeg G] {f : 
X → G}, …
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…

--- 原说明 ---
For fixed `x : ℝ`, the mapping `mulExpNegMulSq ε x` converges pointwise to `x` a
s `ε → 0`
-/
theorem tendsto_mulExpNegMulSq {x : ℝ} :
    Tendsto (fun ε => mulExpNegMulSq ε x) (𝓝 0) (𝓝 x) := by
  have : x = (fun ε : ℝ => mulExpNegMulSq ε x) 0 := by
    simp only [mulExpNegMulSq, zero_mul, neg_zero, exp_zero, mul_one]
  nth_rw 2 [this]
  apply Continuous.tendsto (Continuous.mul continuous_const (by fun_prop))

/-- For a fixed bounded function `g`, `mulExpNegMulSq ε ∘ g` is bounded by `norm g`,
uniformly in `ε ≥ 0`. -/
/-
**Real.abs_mulExpNegMulSq_comp_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：abs_mulExpNegMulSq_comp_le_norm {E : Type*} [TopologicalSpace E] {x : E} (
g : BoundedContinuousFunction E Real) (hε : 0 <= ε) : |(mulExpNegMulSq ε ∘ g) x|
 <= ‖g‖
参数：g : BoundedContinuousFunction E Real；hε : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `Real.abs_exp`：abs_exp (x : Real) : |exp x| = exp x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Real.exp_le_one_iff`：exp_le_one_iff {x : Real} : exp x <= 1 ↔ x <= 0
· 使用定理 `Left.neg_nonpos_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖

--- 原说明 ---
For a fixed bounded function `g`, `mulExpNegMulSq ε ∘ g` is bounded by `norm g`,
uniformly in `ε ≥ 0`.
-/
theorem abs_mulExpNegMulSq_comp_le_norm {E : Type*} [TopologicalSpace E] {x : E}
    (g : BoundedContinuousFunction E ℝ) (hε : 0 ≤ ε) :
    |(mulExpNegMulSq ε ∘ g) x| ≤ ‖g‖ := by
  simp only [Function.comp_apply, mulExpNegMulSq, abs_mul, abs_exp]
  apply le_trans (mul_le_of_le_one_right (abs_nonneg (g x)) _) (g.norm_coe_le_norm x)
  rw [exp_le_one_iff, Left.neg_nonpos_iff, mul_assoc]
  exact mul_nonneg hε (mul_self_nonneg (g x))

end Real

