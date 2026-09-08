/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.MeasureTheory.Group.GeometryOfNumbers
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Convex Bodies

The file contains the definitions of several convex bodies lying in the mixed space `ℝ^r₁ × ℂ^r₂`
associated to a number field of signature `K` and proves several existence theorems by applying
*Minkowski Convex Body Theorem* to those.

## Main definitions and results

* `NumberField.mixedEmbedding.convexBodyLT`: The set of points `x` such that `‖x w‖ < f w` for all
  infinite places `w` with `f : InfinitePlace K → ℝ≥0`.

* `NumberField.mixedEmbedding.convexBodySum`: The set of points `x` such that
  `∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B`

* `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt`: Let `I` be a fractional ideal of `K`.
  Assume that `f` is such that `minkowskiBound K I < volume (convexBodyLT K f)`, then there exists a
  nonzero algebraic number `a` in `I` such that `w a < f w` for all infinite places `w`.

* `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_of_norm_le`: Let `I` be a fractional ideal
  of `K`. Assume that `B` is such that `minkowskiBound K I < volume (convexBodySum K B)` (see
  `convexBodySum_volume` for the computation of this volume), then there exists a nonzero algebraic
  number `a` in `I` such that `|Norm a| < (B / d) ^ d` where `d` is the degree of `K`.

## Tags

number field, infinite places
-/

@[expose] public section

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace Module

section convexBodyLT

open Metric NNReal

variable (f : InfinitePlace K → ℝ≥0)

/-- The convex body defined by `f`: the set of points `x : E` such that `‖x w‖ < f w` for all
infinite places `w`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**NumberField.mixedEmbedding.convexBodyLT** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberFie
ld.mixedEmbedding`。
形式化陈述：convexBodyLT : Set (mixedSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev convexBodyLT : Set (mixedSpace K) :=
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => ball 0 (f w)))
/-
**NumberField.mixedEmbedding.convexBodyLT_mem** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.mixedEmbedding`。
形式化陈述：convexBodyLT_mem {x : K} : mixedEmbedding K x in (convexBodyLT K f) ↔ fora
ll w : InfinitePlace K, w x < f w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RingHom.pi_apply`：∀ {I : Type u} {f : I → Type u_1} {γ : Type u_2} [inst
 : (i : I) → NonAssocSemiring (f i)] [inst_1 : NonAssocSemiring γ]   (g : (i : I
) → γ …
· 使用定理 `NumberField.InfinitePlace.embedding_of_isReal_apply`：embedding_of_isReal
_apply {w : InfinitePlace K} (hw : IsReal w) (x : K) : ((embedding_of_isReal hw)
 x : Complex) = (embedding w) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.InfinitePlace.norm_embedding_eq`：norm_embedding_eq (w : Infi
nitePlace K) (x : K) : ‖(embedding w) x‖ = w x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem convexBodyLT_mem {x : K} :
    mixedEmbedding K x ∈ (convexBodyLT K f) ↔ ∀ w : InfinitePlace K, w x < f w := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, mem_ball_zero_iff, RingHom.pi_apply, ← Complex.norm_real,
    embedding_of_isReal_apply, Subtype.forall, ← forall₂_or_left, ← not_isReal_iff_isComplex, em,
    forall_true_left, norm_embedding_eq]
/-
**NumberField.mixedEmbedding.convexBodyLT_neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.mixedEmbedding`。
形式化陈述：convexBodyLT_neg_mem (x : mixedSpace K) (hx : x in (convexBodyLT K f)) : -
x in (convexBodyLT K f)
参数：x : mixedSpace K；hx : x in (convexBodyLT K f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
-/
theorem convexBodyLT_neg_mem (x : mixedSpace K) (hx : x ∈ (convexBodyLT K f)) :
    -x ∈ (convexBodyLT K f) := by
  simp only [Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
    mem_ball_zero_iff, norm_neg, Real.norm_eq_abs, forall_true_left, Subtype.forall,
    Prod.snd_neg] at hx ⊢
  exact hx
/-
**NumberField.mixedEmbedding.convexBodyLT_convex** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField.mixedEmbedding`。
形式化陈述：convexBodyLT_convex : Convex Real (convexBodyLT K f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.prod`：Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht :
 Convex 𝕜 t) : Convex 𝕜 (s ×ˢ t)
· 使用定理 `convex_pi`：convex_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommMono
id (E i)] [forall i, SMul 𝕜 (E i)] {s : Set ι} {t : forall i, Set (E i)} (ht : …
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
-/
theorem convexBodyLT_convex : Convex ℝ (convexBodyLT K f) :=
  Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => convex_ball _ _))

open Fintype MeasureTheory MeasureTheory.Measure ENNReal

variable [NumberField K]

/-- The fudge factor that appears in the formula for the volume of `convexBodyLT`. -/
/-
**NumberField.mixedEmbedding.convexBodyLTFactor** 是 Mathlib 中的一个缩写定义，位于命名空间 `Num
berField.mixedEmbedding`。
形式化陈述：convexBodyLTFactor : Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fudge factor that appears in the formula for the volume of `convexBodyLT`.
-/
noncomputable abbrev convexBodyLTFactor : ℝ≥0 :=
  (2 : ℝ≥0) ^ nrRealPlaces K * NNReal.pi ^ nrComplexPlaces K
/-
**NumberField.mixedEmbedding.convexBodyLTFactor_ne_zero** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding`。
形式化陈述：convexBodyLTFactor_ne_zero : convexBodyLTFactor K != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNReal.pi_ne_zero`：pi_ne_zero : pi != 0
-/
theorem convexBodyLTFactor_ne_zero : convexBodyLTFactor K ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)
/-
**NumberField.mixedEmbedding.one_le_convexBodyLTFactor** 是 Mathlib 中的一个定理，位于命名空间
 `NumberField.mixedEmbedding`。
形式化陈述：one_le_convexBodyLTFactor : 1 <= convexBodyLTFactor K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_le_mul`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Preorder α
] [MulLeftMono α] {a b : α}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.two_le_pi`：two_le_pi : (2 : Real) <= π
-/
theorem one_le_convexBodyLTFactor : 1 ≤ convexBodyLTFactor K :=
  one_le_mul (one_le_pow₀ one_le_two) (one_le_pow₀ (one_le_two.trans Real.two_le_pi))

open scoped Classical in
/-- The volume of `(ConvexBodyLt K f)` where `convexBodyLT K f` is the set of points `x`
such that `‖x w‖ < f w` for all infinite places `w`. -/
/-
**NumberField.mixedEmbedding.convexBodyLT_volume** 是 Mathlib 中的一个定理，位于命名空间 `Numb
erField.mixedEmbedding`。
形式化陈述：convexBodyLT_volume : volume (convexBodyLT K f) = (convexBodyLTFactor K) *
 ∏ w, (f w) ^ (mult w)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteForallVolume`：∀ {ι : Type u_1} [ins
t : Fintype ι] {α : ι → Type u_4} [inst_1 : (i : ι) → MeasureTheory.MeasureSpace
 (α i)]   [∀ (i : ι), MeasureTheory.Sig…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.pi_pi`：pi_pi [forall i, SigmaFinite (μ i)] (s : (i
 : ι) -> Set (α i)) : Measure.pi μ (pi univ s) = ∏ i, μ i (s i)
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Real.volume_ball`：volume_ball (a r : Real) : volume (Metric.ball a r) = 
ofReal (2 * r)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.volume_ball`：Complex.volume_ball (a : Complex) (r : Real) : volu
me (Metric.ball a r) = .ofReal r ^ 2 * NNReal.pi
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
The volume of `(ConvexBodyLt K f)` where `convexBodyLT K f` is the set of points
 `x`
such that `‖x w‖ < f w` for all infinite places `w`.
-/
theorem convexBodyLT_volume :
    volume (convexBodyLT K f) = (convexBodyLTFactor K) * ∏ w, (f w) ^ (mult w) := by
  calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ∏ x : {w // InfinitePlace.IsComplex w}, ENNReal.ofReal (f x.val) ^ 2 * NNReal.pi := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball, Complex.volume_ball]
    _ = ((2 : ℝ≥0) ^ nrRealPlaces K
          * (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val)))
          * ((∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2) *
            NNReal.pi ^ nrComplexPlaces K) := by
      simp_rw [ofReal_mul (by simp : 0 ≤ (2 : ℝ)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, ofReal_ofNat, ofReal_coe_nnreal, coe_ofNat]
    _ = (convexBodyLTFactor K) * ((∏ x : {w // InfinitePlace.IsReal w}, .ofReal (f x.val)) *
        (∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2)) := by
      simp_rw [convexBodyLTFactor, coe_mul, ENNReal.coe_pow]
      ring
    _ = (convexBodyLTFactor K) * ∏ w, (f w) ^ (mult w) := by
      simp_rw [prod_eq_prod_mul_prod, coe_mul, ofNNReal_finsetProd, mult_isReal, mult_isComplex,
        pow_one, ENNReal.coe_pow, ofReal_coe_nnreal]

variable {f}

/-- This is a technical result: quite often, we want to impose conditions at all infinite places
but one and choose the value at the remaining place so that we can apply
`exists_ne_zero_mem_ringOfIntegers_lt`. -/
/-
**NumberField.mixedEmbedding.adjust_f** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mix
edEmbedding`。
形式化陈述：adjust_f {w₁ : InfinitePlace K} (B : Real>=0) (hf : forall w, w != w₁ -> f
 w != 0) : exists g : InfinitePlace K -> Real>=0, (forall w, w != w₁ -> g w = f 
w) ∧ ∏ w, (g w) ^ mult w = B
参数：B : Real>=0；hf : forall w, w != w₁ -> f w != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用引理 `NNReal.rpow_natCast`：rpow_natCast (x : Real>=0) (n : Nat) : x ^ (n : Rea
l) = x ^ n
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `NumberField.InfinitePlace.mult.eq_1`：∀ {K : Type u_1} [inst : Field K] (
w : NumberField.InfinitePlace K), w.mult = if w.IsReal then 1 else 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
This is a technical result: quite often, we want to impose conditions at all inf
inite places
but one and choose the value at the remaining place so that we can apply
`exists_ne_zero_mem_ringOfIntegers_lt`.
-/
theorem adjust_f {w₁ : InfinitePlace K} (B : ℝ≥0) (hf : ∀ w, w ≠ w₁ → f w ≠ 0) :
    ∃ g : InfinitePlace K → ℝ≥0, (∀ w, w ≠ w₁ → g w = f w) ∧ ∏ w, (g w) ^ mult w = B := by
  classical
  let S := ∏ w ∈ Finset.univ.erase w₁, (f w) ^ mult w
  refine ⟨Function.update f w₁ ((B * S⁻¹) ^ (mult w₁ : ℝ)⁻¹), ?_, ?_⟩
  · exact fun w hw => Function.update_of_ne hw _ f
  · rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w₁), Function.update_self,
      Finset.prod_congr rfl fun w hw => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)],
      ← NNReal.rpow_natCast, ← NNReal.rpow_mul, inv_mul_cancel₀, NNReal.rpow_one, mul_assoc,
      inv_mul_cancel₀, mul_one]
    · rw [Finset.prod_ne_zero_iff]
      exact fun w hw => pow_ne_zero _ (hf w (Finset.ne_of_mem_erase hw))
    · rw [mult]; split_ifs <;> norm_num

end convexBodyLT

section convexBodyLT'

open Metric ENNReal NNReal

variable (f : InfinitePlace K → ℝ≥0) (w₀ : {w : InfinitePlace K // IsComplex w})

open scoped Classical in
/-- A version of `convexBodyLT` with an additional condition at a fixed complex place. This is
needed to ensure the element constructed is not real, see for example
`exists_primitive_element_lt_of_isComplex`.
-/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**NumberField.mixedEmbedding.convexBodyLT'** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberFi
eld.mixedEmbedding`。
形式化陈述：convexBodyLT' : Set (mixedSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev convexBodyLT' : Set (mixedSpace K) :=
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } ↦ ball 0 (f w))) ×ˢ
  (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } ↦
    if w = w₀ then {x | |x.re| < 1 ∧ |x.im| < (f w : ℝ) ^ 2} else ball 0 (f w)))
/-
**NumberField.mixedEmbedding.convexBodyLT'_mem** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.mixedEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] (f : NumberField.InfinitePlace K → NNRea
l) (w₀ : { w // w.IsComplex }) {x : K},   (NumberField.mixedEmbedding K) x ∈ Num
berField.mixedEmbedding.convexBodyLT' K f w₀ ↔     (∀ (w : NumberField.InfiniteP
lace K), w ≠ ↑w₀ → w x < ↑(f w)) ∧       |((↑w₀).embedding x).re| < 1 ∧ |((↑w₀).
embedding x).im| < ↑(f ↑w₀) ^ 2
参数：K : Type u_1；f : NumberField.InfinitePlace K → NNReal；w₀ : { w // w.IsComplex
 }；NumberField.mixedEmbedding K；∀ (w : NumberField.InfinitePlace K), w ≠ ↑w₀ → w
 x < ↑(f w)；(↑w₀).embedding x；(↑w₀).embedding x；f ↑w₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RingHom.pi_apply`：∀ {I : Type u} {f : I → Type u_1} {γ : Type u_2} [inst
 : (i : I) → NonAssocSemiring (f i)] [inst_1 : NonAssocSemiring γ]   (g : (i : I
) → γ …
· 使用定理 `NumberField.InfinitePlace.embedding_of_isReal_apply`：embedding_of_isReal
_apply {w : InfinitePlace K} (hw : IsReal w) (x : K) : ((embedding_of_isReal hw)
 x : Complex) = (embedding w) x
· 使用定理 `NumberField.InfinitePlace.norm_embedding_eq`：norm_embedding_eq (w : Infi
nitePlace K) (x : K) : ‖(embedding w) x‖ = w x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `mem_ball_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E
} {r : ℝ}, a ∈ Metric.ball 0 r ↔ ‖a‖ < r
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NumberField.InfinitePlace.ne_of_isReal_isComplex`：ne_of_isReal_isComplex
 {w w' : InfinitePlace K} (h : IsReal w) (h' : IsComplex w') : w != w'
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem convexBodyLT'_mem {x : K} :
    mixedEmbedding K x ∈ convexBodyLT' K f w₀ ↔
      (∀ w : InfinitePlace K, w ≠ w₀ → w x < f w) ∧
      |(w₀.val.embedding x).re| < 1 ∧ |(w₀.val.embedding x).im| < (f w₀ : ℝ) ^ 2 := by
  simp_rw [mixedEmbedding, RingHom.prod_apply, Set.mem_prod, Set.mem_pi, Set.mem_univ,
    forall_true_left, RingHom.pi_apply, mem_ball_zero_iff, ← Complex.norm_real,
    embedding_of_isReal_apply, norm_embedding_eq, Subtype.forall]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨fun w h_ne ↦ ?_, ?_⟩, fun ⟨h₁, h₂⟩ ↦ ⟨fun w hw ↦ ?_, fun w hw ↦ ?_⟩⟩
  · by_cases hw : IsReal w
    · exact norm_embedding_eq w _ ▸ h₁ w hw
    · specialize h₂ w (not_isReal_iff_isComplex.mp hw)
      rw [apply_ite (w.embedding x ∈ ·), Set.mem_ofPred_eq,
        mem_ball_zero_iff, norm_embedding_eq] at h₂
      rwa [if_neg (by exact Subtype.coe_ne_coe.1 h_ne)] at h₂
  · simpa [if_true] using h₂ w₀.val w₀.prop
  · exact h₁ w (ne_of_isReal_isComplex hw w₀.prop)
  · by_cases h_ne : w = w₀
    · simpa [h_ne]
    · rw [if_neg (by exact Subtype.coe_ne_coe.1 h_ne)]
      rw [mem_ball_zero_iff, norm_embedding_eq]
      exact h₁ w h_ne
/-
**NumberField.mixedEmbedding.convexBodyLT'_neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] (f : NumberField.InfinitePlace K → NNRea
l) (w₀ : { w // w.IsComplex }),   ∀ x ∈ NumberField.mixedEmbedding.convexBodyLT'
 K f w₀, -x ∈ NumberField.mixedEmbedding.convexBodyLT' K f w₀
参数：K : Type u_1；f : NumberField.InfinitePlace K → NNReal；w₀ : { w // w.IsComplex
 }。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem convexBodyLT'_neg_mem (x : mixedSpace K) (hx : x ∈ convexBodyLT' K f w₀) :
    -x ∈ convexBodyLT' K f w₀ := by
  simp only [Set.mem_prod, Set.mem_pi, Set.mem_univ, mem_ball, dist_zero_right, Real.norm_eq_abs,
    true_implies, Subtype.forall, Prod.fst_neg, Pi.neg_apply, norm_neg, Prod.snd_neg] at hx ⊢
  convert! hx using 3
  split_ifs <;> simp
/-
**NumberField.mixedEmbedding.convexBodyLT'_convex** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.mixedEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] (f : NumberField.InfinitePlace K → NNRea
l) (w₀ : { w // w.IsComplex }),   Convex ℝ (NumberField.mixedEmbedding.convexBod
yLT' K f w₀)
参数：K : Type u_1；f : NumberField.InfinitePlace K → NNReal；w₀ : { w // w.IsComplex
 }；NumberField.mixedEmbedding.convexBodyLT' K f w₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.prod`：Convex.prod {s : Set E} {t : Set F} (hs : Convex 𝕜 s) (ht :
 Convex 𝕜 t) : Convex 𝕜 (s ×ˢ t)
· 使用定理 `convex_pi`：convex_pi {ι : Type*} {E : ι -> Type*} [forall i, AddCommMono
id (E i)] [forall i, SMul 𝕜 (E i)] {s : Set ι} {t : forall i, Set (E i)} (ht : …
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_halfSpace_re_gt`：convex_halfSpace_re_gt : Convex Real { c : Compl
ex | r < c.re }
· 使用定理 `convex_halfSpace_re_lt`：convex_halfSpace_re_lt : Convex Real { c : Compl
ex | c.re < r }
· 使用定理 `convex_halfSpace_im_gt`：convex_halfSpace_im_gt : Convex Real { c : Compl
ex | r < c.im }
· 使用定理 `convex_halfSpace_im_lt`：convex_halfSpace_im_lt : Convex Real { c : Compl
ex | c.im < r }
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem convexBodyLT'_convex : Convex ℝ (convexBodyLT' K f w₀) := by
  refine Convex.prod (convex_pi (fun _ _ => convex_ball _ _)) (convex_pi (fun _ _ => ?_))
  split_ifs
  · simp_rw [abs_lt]
    refine Convex.inter ((convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _))
      ((convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _))
  · exact convex_ball _ _

open MeasureTheory MeasureTheory.Measure

variable [NumberField K]

/-- The fudge factor that appears in the formula for the volume of `convexBodyLT'`. -/
/-
**NumberField.mixedEmbedding.convexBodyLT'Factor** 是 Mathlib 中的一个定义，位于命名空间 `Numb
erField.mixedEmbedding`。
形式化陈述：(K : Type u_1) → [inst : Field K] → [NumberField K] → NNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fudge factor that appears in the formula for the volume of `convexBodyLT'`.
-/
noncomputable abbrev convexBodyLT'Factor : ℝ≥0 :=
  (2 : ℝ≥0) ^ (nrRealPlaces K + 2) * NNReal.pi ^ (nrComplexPlaces K - 1)
/-
**NumberField.mixedEmbedding.convexBodyLT'Factor_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K], NumberField.mi
xedEmbedding.convexBodyLT'Factor K ≠ 0
参数：K : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNReal.pi_ne_zero`：pi_ne_zero : pi != 0
-/
theorem convexBodyLT'Factor_ne_zero : convexBodyLT'Factor K ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ pi_ne_zero)
/-
**NumberField.mixedEmbedding.one_le_convexBodyLT'Factor** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.mixedEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K], 1 ≤ NumberFiel
d.mixedEmbedding.convexBodyLT'Factor K
参数：K : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `one_le_mul`：∀ {α : Type u_1} [inst : MulOneClass α] [inst_1 : Preorder α
] [MulLeftMono α] {a b : α}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b
· 使用引理 `one_le_pow₀`：one_le_pow₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 <= 
a) {n : Nat} : 1 <= a ^ n
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.two_le_pi`：two_le_pi : (2 : Real) <= π
-/
theorem one_le_convexBodyLT'Factor : 1 ≤ convexBodyLT'Factor K :=
  one_le_mul (one_le_pow₀ one_le_two) (one_le_pow₀ (one_le_two.trans Real.two_le_pi))

open scoped Classical in
/-
**NumberField.mixedEmbedding.convexBodyLT'_volume** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.mixedEmbedding`。
形式化陈述：∀ (K : Type u_1) [inst : Field K] (f : NumberField.InfinitePlace K → NNRea
l) (w₀ : { w // w.IsComplex })   [inst_1 : NumberField K],   MeasureTheory.volum
e (NumberField.mixedEmbedding.convexBodyLT' K f w₀) =     ↑(NumberField.mixedEmb
edding.convexBodyLT'Factor K) * ↑(∏ w, f w ^ w.mult)
参数：K : Type u_1；f : NumberField.InfinitePlace K → NNReal；w₀ : { w // w.IsComplex
 }；NumberField.mixedEmbedding.convexBodyLT' K f w₀；NumberField.mixedEmbedding.co
nvexBodyLT'Factor K；∏ w, f w ^ w.mult。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.measure_preimage`：measure_preimage {f : 
α -> β} (hf : MeasurePreserving f μa μb) {s : Set β} (hs : NullMeasurableSet s μ
b) : μa (f ⁻¹' s) = μb s
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Complex.volume_preserving_equiv_real_prod`：volume_preserving_equiv_real_
prod : MeasurePreserving measurableEquivRealProd
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_norm`：measurable_norm : Measurable (norm : α -> Real)
· 使用定理 `Complex.measurable_re`：measurable_re : Measurable re
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `Complex.measurable_im`：measurable_im : Measurable im
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.Measure.prod_prod`：prod_prod (s : Set α) (t : Set β) : μ.p
rod ν (s ×ˢ t) = μ s * ν t
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
（共 100 条，此处仅展示前 30 条）
-/
theorem convexBodyLT'_volume :
    volume (convexBodyLT' K f w₀) = convexBodyLT'Factor K * ∏ w, (f w) ^ (mult w) := by
  have vol_box : ∀ B : ℝ≥0, volume {x : ℂ | |x.re| < 1 ∧ |x.im| < B ^ 2} = 4 * B ^ 2 := by
    intro B
    rw [← (Complex.volume_preserving_equiv_real_prod.symm).measure_preimage]
    · simp_rw [Set.preimage_ofPred_eq, Complex.measurableEquivRealProd_symm_apply]
      rw [show {a : ℝ × ℝ | |a.1| < 1 ∧ |a.2| < B ^ 2} =
        Set.Ioo (-1 : ℝ) (1 : ℝ) ×ˢ Set.Ioo (-(B : ℝ) ^ 2) ((B : ℝ) ^ 2) by
          ext; simp_rw [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Ioo, abs_lt]]
      simp_rw [volume_eq_prod, prod_prod, Real.volume_Ioo, sub_neg_eq_add, one_add_one_eq_two,
        ← two_mul, ofReal_mul zero_le_two, ofReal_pow (coe_nonneg B), ofReal_ofNat,
        ofReal_coe_nnreal, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 by norm_num]
    · refine (MeasurableSet.inter ?_ ?_).nullMeasurableSet
      · exact measurableSet_lt (measurable_norm.comp Complex.measurable_re) measurable_const
      · exact measurableSet_lt (measurable_norm.comp Complex.measurable_im) measurable_const
  calc
    _ = (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (2 * (f x.val))) *
          ((∏ x ∈ Finset.univ.erase w₀, ENNReal.ofReal (f x.val) ^ 2 * pi) *
          (4 * (f w₀) ^ 2)) := by
      simp_rw [volume_eq_prod, prod_prod, volume_pi, pi_pi, Real.volume_ball]
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
      congr 2
      · refine Finset.prod_congr rfl (fun w' hw' ↦ ?_)
        rw [if_neg (Finset.ne_of_mem_erase hw'), Complex.volume_ball]
      · simpa only [ite_true] using vol_box (f w₀)
    _ = ((2 : ℝ≥0) ^ nrRealPlaces K *
          (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val))) *
            ((∏ x ∈ Finset.univ.erase w₀, ENNReal.ofReal (f x.val) ^ 2) *
              ↑pi ^ (nrComplexPlaces K - 1) * (4 * (f w₀) ^ 2)) := by
      simp_rw [ofReal_mul (by simp : 0 ≤ (2 : ℝ)), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ofReal_ofNat,
        ofReal_coe_nnreal, coe_ofNat]
    _ = convexBodyLT'Factor K * (∏ x : {w // InfinitePlace.IsReal w}, ENNReal.ofReal (f x.val))
        * (∏ x : {w // IsComplex w}, ENNReal.ofReal (f x.val) ^ 2) := by
      rw [show (4 : ℝ≥0∞) = (2 : ℝ≥0) ^ 2 by norm_num, convexBodyLT'Factor, pow_add,
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀), ofReal_coe_nnreal]
      simp_rw [coe_mul, ENNReal.coe_pow]
      ring
    _ = convexBodyLT'Factor K * ∏ w, (f w) ^ (mult w) := by
      simp_rw [prod_eq_prod_mul_prod, coe_mul, ofNNReal_finsetProd, mult_isReal, mult_isComplex,
        pow_one, ENNReal.coe_pow, ofReal_coe_nnreal, mul_assoc]

end convexBodyLT'

section convexBodySum

open ENNReal MeasureTheory Fintype

open scoped Real NNReal

variable [NumberField K] (B : ℝ)
variable {K}

/-- The function that sends `x : mixedSpace K` to `∑ w, ‖x.1 w‖ + 2 * ∑ w, ‖x.2 w‖`. It defines a
norm and it used to define `convexBodySum`. -/
/-
**NumberField.mixedEmbedding.convexBodySumFun** 是 Mathlib 中的一个缩写定义，位于命名空间 `Numbe
rField.mixedEmbedding`。
形式化陈述：convexBodySumFun (x : mixedSpace K) : Real
参数：x : mixedSpace K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function that sends `x : mixedSpace K` to `∑ w, ‖x.1 w‖ + 2 * ∑ w, ‖x.2 w‖`.
 It defines a
norm and it used to define `convexBodySum`.
-/
noncomputable abbrev convexBodySumFun (x : mixedSpace K) : ℝ := ∑ w, mult w * normAtPlace w x
/-
**NumberField.mixedEmbedding.convexBodySumFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `N
umberField.mixedEmbedding`。
形式化陈述：convexBodySumFun_apply (x : mixedSpace K) : convexBodySumFun x = ∑ w, mult
 w * normAtPlace w x
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem convexBodySumFun_apply (x : mixedSpace K) :
    convexBodySumFun x = ∑ w, mult w * normAtPlace w x := rfl

open scoped Classical in
/-
**NumberField.mixedEmbedding.convexBodySumFun_apply'** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：convexBodySumFun_apply' (x : mixedSpace K) : convexBodySumFun x = ∑ w, ‖x.
1 w‖ + 2 * ∑ w, ‖x.2 w‖
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.sum_eq_sum_add_sum`：∀ {K : Type u_1} [inst : F
ield K] {α : Type u_2} [inst_1 : AddCommMonoid α] [inst_2 : NumberField K]   (f 
: NumberField.InfinitePlace K → α)…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NumberField.InfinitePlace.mult_isReal`：mult_isReal (w : {w : InfinitePla
ce K // IsReal w}) : mult w.1 = 1
· 使用定理 `NumberField.InfinitePlace.mult_isComplex`：mult_isComplex (w : {w : Infin
itePlace K // IsComplex w}) : mult w.1 = 2
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isReal`：normAtPlace_appl
y_of_isReal {w : InfinitePlace K} (hw : IsReal w) (x : mixedSpace K) : normAtPla
ce w x = ‖x.1 ⟨w, hw⟩‖
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply_of_isComplex`：normAtPlace_a
pply_of_isComplex {w : InfinitePlace K} (hw : IsComplex w) (x : mixedSpace K) : 
normAtPlace w x = ‖x.2 ⟨w, hw⟩‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convexBodySumFun_apply' (x : mixedSpace K) :
    convexBodySumFun x = ∑ w, ‖x.1 w‖ + 2 * ∑ w, ‖x.2 w‖ := by
  simp_rw [convexBodySumFun_apply, sum_eq_sum_add_sum, mult_isReal, mult_isComplex,
    Nat.cast_one, one_mul, Nat.cast_ofNat, normAtPlace_apply_of_isReal (Subtype.prop _),
    normAtPlace_apply_of_isComplex (Subtype.prop _), Finset.mul_sum]
/-
**NumberField.mixedEmbedding.convexBodySumFun_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：convexBodySumFun_nonneg (x : mixedSpace K) : 0 <= convexBodySumFun x
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `NumberField.InfinitePlace.mult_pos`：mult_pos {w : InfinitePlace K} : 0 <
 mult w
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
-/
theorem convexBodySumFun_nonneg (x : mixedSpace K) :
    0 ≤ convexBodySumFun x :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le (normAtPlace_nonneg _ _))
/-
**NumberField.mixedEmbedding.convexBodySumFun_neg** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.mixedEmbedding`。
形式化陈述：convexBodySumFun_neg (x : mixedSpace K) : convexBodySumFun (-x) = convexBo
dySumFun x
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_neg`：normAtPlace_neg (w : Infinit
ePlace K) (x : mixedSpace K) : normAtPlace w (-x) = normAtPlace w x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convexBodySumFun_neg (x : mixedSpace K) :
    convexBodySumFun (-x) = convexBodySumFun x := by
  simp_rw [convexBodySumFun, normAtPlace_neg]
/-
**NumberField.mixedEmbedding.convexBodySumFun_add_le** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：convexBodySumFun_add_le (x y : mixedSpace K) : convexBodySumFun (x + y) <=
 convexBodySumFun x + convexBodySumFun y
参数：x y : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_add_le`：normAtPlace_add_le (w : I
nfinitePlace K) (x y : mixedSpace K) : normAtPlace w (x + y) <= normAtPlace w x 
+ normAtPlace w y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `NumberField.InfinitePlace.mult_pos`：mult_pos {w : InfinitePlace K} : 0 <
 mult w
-/
theorem convexBodySumFun_add_le (x y : mixedSpace K) :
    convexBodySumFun (x + y) ≤ convexBodySumFun x + convexBodySumFun y := by
  simp_rw [convexBodySumFun, ← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum
    fun _ _ ↦ mul_le_mul_of_nonneg_left (normAtPlace_add_le _ x y) (Nat.cast_pos.mpr mult_pos).le
/-
**NumberField.mixedEmbedding.convexBodySumFun_smul** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：convexBodySumFun_smul (c : Real) (x : mixedSpace K) : convexBodySumFun (c 
• x) = |c| * convexBodySumFun x
参数：c : Real；x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_smul`：normAtPlace_smul (w : Infin
itePlace K) (x : mixedSpace K) (c : Real) : normAtPlace w (c • x) = |c| * normAt
Place w x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem convexBodySumFun_smul (c : ℝ) (x : mixedSpace K) :
    convexBodySumFun (c • x) = |c| * convexBodySumFun x := by
  simp_rw [convexBodySumFun, normAtPlace_smul, ← mul_assoc, mul_comm, Finset.mul_sum, mul_assoc]
/-
**NumberField.mixedEmbedding.convexBodySumFun_eq_zero_iff** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.mixedEmbedding`。
形式化陈述：convexBodySumFun_eq_zero_iff (x : mixedSpace K) : convexBodySumFun x = 0 ↔
 x = 0
参数：x : mixedSpace K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.mixedEmbedding.forall_normAtPlace_eq_zero_iff`：forall_normAt
Place_eq_zero_iff {x : mixedSpace K} : (forall w, normAtPlace w x = 0) ↔ x = 0
· 使用定理 `NumberField.mixedEmbedding.convexBodySumFun.eq_1`：∀ {K : Type u_1} [inst
 : Field K] [inst_1 : NumberField K] (x : NumberField.mixedEmbedding.mixedSpace 
K),   NumberField.mixedEmbedding.conve…
· 使用定理 `Finset.sum_eq_zero_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLe
ftMono N], (∀ i ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `NumberField.InfinitePlace.mult_pos`：mult_pos {w : InfinitePlace K} : 0 <
 mult w
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem convexBodySumFun_eq_zero_iff (x : mixedSpace K) :
    convexBodySumFun x = 0 ↔ x = 0 := by
  rw [← forall_normAtPlace_eq_zero_iff, convexBodySumFun, Finset.sum_eq_zero_iff_of_nonneg
    fun _ _ ↦ mul_nonneg (Nat.cast_pos.mpr mult_pos).le (normAtPlace_nonneg _ _)]
  simp

open scoped Classical in
/-
**NumberField.mixedEmbedding.norm_le_convexBodySumFun** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.mixedEmbedding`。
形式化陈述：norm_le_convexBodySumFun (x : mixedSpace K) : ‖x‖ <= convexBodySumFun x
参数：x : mixedSpace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `NumberField.instNonemptyInfinitePlaceOfRingHomComplex`：∀ (K : Type u_1) 
[inst : Field K] [Nonempty (K →+* ℂ)], Nonempty (NumberField.InfinitePlace K)
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.norm_eq_sup'_normAtPlace`：∀ {K : Type u_1} [i
nst : Field K] [inst_1 : NumberField K] (x : NumberField.mixedEmbedding.mixedSpa
ce K),   ‖x‖ = Finset.univ.sup' ⋯ fun w =…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sup'_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   s.sup' H f ≤ a ↔ ∀ 
b ∈ s, f…
· 使用定理 `NumberField.mixedEmbedding.convexBodySumFun_apply`：convexBodySumFun_appl
y (x : mixedSpace K) : convexBodySumFun x = ∑ w, mult w * normAtPlace w x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `le_add_of_le_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : Preorder α] [AddLeftMono α] {a b c : α}, b ≤ c → 0 ≤ a → b ≤ c + a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_nonneg`：normAtPlace_nonneg (w : I
nfinitePlace K) (x : mixedSpace K) : 0 <= normAtPlace w x
· 使用定理 `NumberField.InfinitePlace.one_le_mult`：one_le_mult {w : InfinitePlace K}
 : (1 : Real) <= mult w
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `NumberField.InfinitePlace.mult_pos`：mult_pos {w : InfinitePlace K} : 0 <
 mult w
-/
theorem norm_le_convexBodySumFun (x : mixedSpace K) : ‖x‖ ≤ convexBodySumFun x := by
  rw [norm_eq_sup'_normAtPlace]
  refine (Finset.sup'_le_iff _ _).mpr fun w _ ↦ ?_
  rw [convexBodySumFun_apply, ← Finset.univ.add_sum_erase _ (Finset.mem_univ w)]
  refine le_add_of_le_of_nonneg ?_ ?_
  · exact le_mul_of_one_le_left (normAtPlace_nonneg w x) one_le_mult
  · exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_pos.mpr mult_pos).le
      (normAtPlace_nonneg _ _))

variable (K)
/-
**NumberField.mixedEmbedding.convexBodySumFun_continuous** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：convexBodySumFun_continuous : Continuous (convexBodySumFun : mixedSpace K 
-> Real)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMonoid
 M] [Conti…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `NumberField.mixedEmbedding.continuous_normAtPlace`：continuous_normAtPlac
e (w : InfinitePlace K) : Continuous (normAtPlace w)
-/
theorem convexBodySumFun_continuous :
    Continuous (convexBodySumFun : mixedSpace K → ℝ) := by
  fun_prop

/-- The convex body equal to the set of points `x : mixedSpace K` such that
  `∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B`. -/
/-
**NumberField.mixedEmbedding.convexBodySum** 是 Mathlib 中的一个缩写定义，位于命名空间 `NumberFi
eld.mixedEmbedding`。
形式化陈述：convexBodySum : Set (mixedSpace K)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The convex body equal to the set of points `x : mixedSpace K` such that
  `∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B`.
-/
abbrev convexBodySum : Set (mixedSpace K) := { x | convexBodySumFun x ≤ B }

open scoped Classical in
/-
**NumberField.mixedEmbedding.convexBodySum_volume_eq_zero_of_le_zero** 是 Mathlib
 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：convexBodySum_volume_eq_zero_of_le_zero {B} (hB : B <= 0) : volume (convex
BodySum K B) = 0
参数：hB : B <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
（共 43 条，此处仅展示前 30 条）
-/
theorem convexBodySum_volume_eq_zero_of_le_zero {B} (hB : B ≤ 0) :
    volume (convexBodySum K B) = 0 := by
  obtain hB | hB := lt_or_eq_of_le hB
  · suffices convexBodySum K B = ∅ by rw [this, measure_empty]
    ext x
    refine ⟨fun hx => ?_, fun h => h.elim⟩
    rw [Set.mem_ofPred] at hx
    linarith [convexBodySumFun_nonneg x]
  · suffices convexBodySum K B = { 0 } by rw [this, measure_singleton]
    ext
    rw [convexBodySum, Set.mem_ofPred_eq, Set.mem_singleton_iff, hB, ← convexBodySumFun_eq_zero_iff]
    exact (convexBodySumFun_nonneg _).ge_iff_eq'
/-
**NumberField.mixedEmbedding.convexBodySum_mem** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field.mixedEmbedding`。
形式化陈述：convexBodySum_mem {x : K} : mixedEmbedding K x in (convexBodySum K B) ↔ ∑ 
w : InfinitePlace K, (mult w) * w.val x <= B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NumberField.mixedEmbedding.normAtPlace_apply`：normAtPlace_apply (w : Inf
initePlace K) (x : K) : normAtPlace w (mixedEmbedding K x) = w x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem convexBodySum_mem {x : K} :
    mixedEmbedding K x ∈ (convexBodySum K B) ↔
      ∑ w : InfinitePlace K, (mult w) * w.val x ≤ B := by
  simp_rw [Set.mem_ofPred_eq, convexBodySumFun, normAtPlace_apply]
  rfl
/-
**NumberField.mixedEmbedding.convexBodySum_neg_mem** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：convexBodySum_neg_mem {x : mixedSpace K} (hx : x in (convexBodySum K B)) :
 -x in (convexBodySum K B)
参数：hx : x in (convexBodySum K B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `NumberField.mixedEmbedding.convexBodySumFun_neg`：convexBodySumFun_neg (x
 : mixedSpace K) : convexBodySumFun (-x) = convexBodySumFun x
-/
theorem convexBodySum_neg_mem {x : mixedSpace K} (hx : x ∈ (convexBodySum K B)) :
    -x ∈ (convexBodySum K B) := by
  rw [Set.mem_ofPred, convexBodySumFun_neg]
  exact hx
/-
**NumberField.mixedEmbedding.convexBodySum_convex** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.mixedEmbedding`。
形式化陈述：convexBodySum_convex : Convex Real (convexBodySum K B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex_subadditive_le`：Convex_subadditive_le [SMul 𝕜 E] {f : E -> 𝕜} (hf
1 : forall x y, f (x + y) <= (f x) + (f y)) (hf2 : forall ⦃c⦄ x, 0 <= c -> f (c 
• x) <= c *…
· 使用定理 `NumberField.mixedEmbedding.convexBodySumFun_add_le`：convexBodySumFun_add
_le (x y : mixedSpace K) : convexBodySumFun (x + y) <= convexBodySumFun x + conv
exBodySumFun y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `NumberField.mixedEmbedding.convexBodySumFun_smul`：convexBodySumFun_smul 
(c : Real) (x : mixedSpace K) : convexBodySumFun (c • x) = |c| * convexBodySumFu
n x
-/
theorem convexBodySum_convex : Convex ℝ (convexBodySum K B) := by
  refine Convex_subadditive_le (fun _ _ => convexBodySumFun_add_le _ _) (fun c x h => ?_) B
  convert! le_of_eq (convexBodySumFun_smul c x)
  exact (abs_eq_self.mpr h).symm
/-
**NumberField.mixedEmbedding.convexBodySum_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `
NumberField.mixedEmbedding`。
形式化陈述：convexBodySum_isBounded : Bornology.IsBounded (convexBodySum K B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_sub_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a - b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `NumberField.mixedEmbedding.norm_le_convexBodySumFun`：norm_le_convexBodyS
umFun (x : mixedSpace K) : ‖x‖ <= convexBodySumFun x
-/
theorem convexBodySum_isBounded : Bornology.IsBounded (convexBodySum K B) := by
  classical
  refine Metric.isBounded_iff.mpr ⟨B + B, fun x hx y hy => ?_⟩
  simp_rw [dist_eq_norm]
  refine le_trans (norm_sub_le x y) (add_le_add ?_ ?_)
  · exact le_trans (norm_le_convexBodySumFun x) hx
  · exact le_trans (norm_le_convexBodySumFun y) hy
/-
**NumberField.mixedEmbedding.convexBodySum_compact** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：convexBodySum_compact : IsCompact (convexBodySum K B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.isCompact_iff_isClosed_bounded`：isCompact_iff_isClosed_bounded {α
 : Type*} {s : Set α} [MetricSpace α] [ProperSpace α] : IsCompact s ↔ IsClosed s
 ∧ IsBounded s
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `NumberField.mixedEmbedding.convexBodySumFun_continuous`：convexBodySumFun
_continuous : Continuous (convexBodySumFun : mixedSpace K -> Real)
· 使用定理 `isClosed_Icc`：isClosed_Icc {a b : α} : IsClosed (Icc a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NumberField.mixedEmbedding.convexBodySum_isBounded`：convexBodySum_isBoun
ded : Bornology.IsBounded (convexBodySum K B)
-/
theorem convexBodySum_compact : IsCompact (convexBodySum K B) := by
  classical
  rw [Metric.isCompact_iff_isClosed_bounded]
  refine ⟨?_, convexBodySum_isBounded K B⟩
  convert! IsClosed.preimage (convexBodySumFun_continuous K) (isClosed_Icc : IsClosed (Set.Icc 0 B))
  ext
  simp [convexBodySumFun_nonneg]

/-- The fudge factor that appears in the formula for the volume of `convexBodyLt`. -/
/-
**NumberField.mixedEmbedding.convexBodySumFactor** 是 Mathlib 中的一个缩写定义，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：convexBodySumFactor : Real>=0
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K

--- 原说明 ---
The fudge factor that appears in the formula for the volume of `convexBodyLt`.
-/
noncomputable abbrev convexBodySumFactor : ℝ≥0 :=
  (2 : ℝ≥0) ^ nrRealPlaces K * (NNReal.pi / 2) ^ nrComplexPlaces K / (finrank ℚ K).factorial
/-
**NumberField.mixedEmbedding.convexBodySumFactor_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：convexBodySumFactor_ne_zero : convexBodySumFactor K != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NNReal.instNoZeroDivisors`：NoZeroDivisors NNReal
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NNReal.pi_ne_zero`：pi_ne_zero : pi != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
-/
theorem convexBodySumFactor_ne_zero : convexBodySumFactor K ≠ 0 := by
  refine div_ne_zero ?_ <| Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact mul_ne_zero (pow_ne_zero _ two_ne_zero)
    (pow_ne_zero _ (div_ne_zero NNReal.pi_ne_zero two_ne_zero))

open MeasureTheory MeasureTheory.Measure Real in
open scoped Classical in
/-
**NumberField.mixedEmbedding.convexBodySum_volume** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.mixedEmbedding`。
形式化陈述：convexBodySum_volume : volume (convexBodySum K B) = (convexBodySumFactor K
) * (.ofReal B) ^ (finrank Rat K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.convexBodySum_volume_eq_zero_of_le_zero`：conv
exBodySum_volume_eq_zero_of_le_zero {B} (hB : B <= 0) : volume (convexBodySum K 
B) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_eq_zero`：ofReal_eq_zero {p : Real} : ENNReal.ofReal p = 0
 ↔ p <= 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.measure_le_eq_lt`：MeasureTheory.measure_le_eq_lt [Nontrivi
al E] (r : Real) : μ {x : E | g x <= r} = μ {x : E | g x < r}
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
（共 146 条，此处仅展示前 30 条）
-/
theorem convexBodySum_volume :
    volume (convexBodySum K B) = (convexBodySumFactor K) * (.ofReal B) ^ (finrank ℚ K) := by
  obtain hB | hB := le_or_gt B 0
  · rw [convexBodySum_volume_eq_zero_of_le_zero K hB, ofReal_eq_zero.mpr hB, zero_pow, mul_zero]
    exact finrank_pos.ne'
  · suffices volume (convexBodySum K 1) = (convexBodySumFactor K) by
      rw [mul_comm]
      convert! addHaar_smul volume B (convexBodySum K 1)
      · simp_rw [← Set.preimage_smul_inv₀ (ne_of_gt hB), Set.preimage_ofPred_eq, convexBodySumFun,
        normAtPlace_smul, abs_inv, abs_eq_self.mpr (le_of_lt hB), ← mul_assoc, mul_comm, mul_assoc,
        ← Finset.mul_sum, inv_mul_le_iff₀ hB, mul_one]
      · rw [abs_pow, ofReal_pow (abs_nonneg _), abs_eq_self.mpr (le_of_lt hB),
          mixedEmbedding.finrank]
      · exact this.symm
    rw [MeasureTheory.measure_le_eq_lt _ ((convexBodySumFun_eq_zero_iff 0).mpr rfl)
      convexBodySumFun_neg convexBodySumFun_add_le
      (fun hx => (convexBodySumFun_eq_zero_iff _).mp hx)
      (fun r x => le_of_eq (convexBodySumFun_smul r x))]
    rw [measure_lt_one_eq_integral_div_gamma (g := fun x : (mixedSpace K) => convexBodySumFun x)
      volume ((convexBodySumFun_eq_zero_iff 0).mpr rfl) convexBodySumFun_neg convexBodySumFun_add_le
      (fun hx => (convexBodySumFun_eq_zero_iff _).mp hx)
      (fun r x => le_of_eq (convexBodySumFun_smul r x)) zero_lt_one]
    simp_rw [mixedEmbedding.finrank, div_one, Gamma_nat_eq_factorial, ofReal_div_of_pos
      (Nat.cast_pos.mpr (Nat.factorial_pos _)), Real.rpow_one, ofReal_natCast]
    suffices ∫ x : mixedSpace K, exp (-convexBodySumFun x) =
        (2 : ℝ) ^ nrRealPlaces K * (π / 2) ^ nrComplexPlaces K by
      rw [this, convexBodySumFactor, ofReal_mul (by positivity), ofReal_pow zero_le_two,
        ofReal_pow (by positivity), ofReal_div_of_pos zero_lt_two, ofReal_ofNat,
        ← NNReal.coe_real_pi, ofReal_coe_nnreal, coe_div (Nat.cast_ne_zero.mpr
        (Nat.factorial_ne_zero _)), coe_mul, coe_pow, coe_pow, coe_ofNat, coe_div two_ne_zero,
        coe_ofNat, coe_natCast]
    calc
      _ = (∫ x : {w : InfinitePlace K // IsReal w} → ℝ, ∏ w, exp (-‖x w‖)) *
              (∫ x : {w : InfinitePlace K // IsComplex w} → ℂ, ∏ w, exp (-2 * ‖x w‖)) := by
        simp_rw [convexBodySumFun_apply', neg_add, ← neg_mul, Finset.mul_sum,
          ← Finset.sum_neg_distrib, exp_add, exp_sum, ← integral_prod_mul, volume_eq_prod]
      _ = (∫ x : ℝ, exp (-|x|)) ^ nrRealPlaces K *
              (∫ x : ℂ, Real.exp (-2 * ‖x‖)) ^ nrComplexPlaces K := by
        rw [integral_fintype_prod_volume_eq_pow (fun x => exp (-‖x‖)),
          integral_fintype_prod_volume_eq_pow (fun x => exp (-2 * ‖x‖))]
        simp_rw [norm_eq_abs]
      _ = (2 * Gamma (1 / 1 + 1)) ^ nrRealPlaces K *
              (π * (2 : ℝ) ^ (-(2 : ℝ) / 1) * Gamma (2 / 1 + 1)) ^ nrComplexPlaces K := by
        rw [integral_comp_abs (f := fun x => exp (-x)), ← integral_exp_neg_rpow zero_lt_one,
          ← Complex.integral_exp_neg_mul_rpow le_rfl zero_lt_two]
        simp_rw [Real.rpow_one]
      _ = (2 : ℝ) ^ nrRealPlaces K * (π / 2) ^ nrComplexPlaces K := by
        simp_rw [div_one, one_add_one_eq_two, Gamma_add_one two_ne_zero, Gamma_two, mul_one,
          mul_assoc, ← Real.rpow_add_one two_ne_zero, show (-2 : ℝ) + 1 = -1 by norm_num,
          Real.rpow_neg_one, div_eq_mul_inv]

end convexBodySum

section minkowski

open MeasureTheory MeasureTheory.Measure Module ZSpan Real Submodule

open scoped ENNReal NNReal nonZeroDivisors IntermediateField

variable [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

open scoped Classical in
/-- The bound that appears in **Minkowski Convex Body theorem**, see
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`. See
`NumberField.mixedEmbedding.volume_fundamentalDomain_idealLatticeBasis_eq` and
`NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis` for the computation of
`volume (fundamentalDomain (idealLatticeBasis K))`. -/
/-
**NumberField.mixedEmbedding.minkowskiBound** 是 Mathlib 中的一个定义，位于命名空间 `NumberFie
ld.mixedEmbedding`。
形式化陈述：minkowskiBound : Real>=0∞
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ

--- 原说明 ---
The bound that appears in **Minkowski Convex Body theorem**, see
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`. Se
e
`NumberField.mixedEmbedding.volume_fundamentalDomain_idealLatticeBasis_eq` and
`NumberField.mixedEmbedding.volume_fundamentalDomain_latticeBasis` for the compu
tation of
`volume (fundamentalDomain (idealLatticeBasis K))`.
-/
noncomputable def minkowskiBound : ℝ≥0∞ :=
  volume (fundamentalDomain (fractionalIdealLatticeBasis K I)) *
    (2 : ℝ≥0∞) ^ (finrank ℝ (mixedSpace K))

open scoped Classical in
/-
**NumberField.mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasi
s** 是 Mathlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：volume_fundamentalDomain_fractionalIdealLatticeBasis : volume (fundamental
Domain (fractionalIdealLatticeBasis K I)) = .ofReal (FractionalIdeal.absNorm I.1
) * volume (fundamentalDomain (latticeBasis K))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.instFiniteIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule
`：∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZ
eroDivisors (NumberField.RingOfIntegers K)) K), Module.Finite …
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_card_chooseBasisIndex`：∀ (R : Type u) (M : Type v) [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [inst
_3 : Module.Free R M] [Strong…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.fractionalIdeal_rank`：fractionalIdeal_rank (I : (FractionalI
deal (𝓞 K)⁰ K)ˣ) : finrank Int I = finrank Int (𝓞 K)
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `ZSpan.fundamentalDomain_reindex`：fundamentalDomain_reindex {ι' : Type*} 
(e : ι ≃ ι') : fundamentalDomain (b.reindex e) = fundamentalDomain b
· 使用定理 `ZSpan.measure_fundamentalDomain`：measure_fundamentalDomain [Fintype ι] [
DecidableEq ι] [MeasurableSpace E] (μ : Measure E) [BorelSpace E] [Measure.IsAdd
HaarMeasure μ] (b₀ : …
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
（共 44 条，此处仅展示前 30 条）
-/
theorem volume_fundamentalDomain_fractionalIdealLatticeBasis :
    volume (fundamentalDomain (fractionalIdealLatticeBasis K I)) =
      .ofReal (FractionalIdeal.absNorm I.1) * volume (fundamentalDomain (latticeBasis K)) := by
  let e : (Module.Free.ChooseBasisIndex ℤ I) ≃ (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, ← finrank_eq_card_chooseBasisIndex,
      fractionalIdeal_rank]
  rw [← fundamentalDomain_reindex (fractionalIdealLatticeBasis K I) e,
    measure_fundamentalDomain ((fractionalIdealLatticeBasis K I).reindex e)]
  · rw [show (fractionalIdealLatticeBasis K I).reindex e = (mixedEmbedding K) ∘
        (basisOfFractionalIdeal K I) ∘ e.symm by
      ext1; simp only [Basis.coe_reindex, Function.comp_apply, fractionalIdealLatticeBasis_apply]]
    rw [mixedEmbedding.det_basisOfFractionalIdeal_eq_norm]
/-
**NumberField.mixedEmbedding.minkowskiBound_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.mixedEmbedding`。
形式化陈述：minkowskiBound_lt_top : minkowskiBound K I < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `ENNReal.mul_lt_top`：mul_lt_top : a < ∞ -> b < ∞ -> a * b < ∞
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `Bornology.IsBounded.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} [inst : PseudoMetricSpace α] [ProperSpace α] {μ : MeasureTheory.Measure α}
   [MeasureTheory.IsFini…
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureOnCompactsProdVolume`：∀ {X : Ty
pe u_4} {Y : Type u_5} [inst : TopologicalSpace X] [inst_1 : MeasureTheory.Measu
reSpace X]   [MeasureTheory.IsFiniteMeasureOnCompac…
· 使用定理 `MeasureTheory.Measure.instIsFiniteMeasureOnCompactsForallVolumeOfSigmaFi
nite`：∀ {ι : Type u_1} [inst : Fintype ι] {X : ι → Type u_4} [inst_1 : (i : ι) →
 MeasureTheory.MeasureSpace (X i)]   [inst_2 : (i : ι) → Topologic…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `ZSpan.fundamentalDomain_isBounded`：fundamentalDomain_isBounded [Finite ι
] [HasSolidNorm K] : IsBounded (fundamentalDomain b)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.instFiniteIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule
`：∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZ
eroDivisors (NumberField.RingOfIntegers K)) K), Module.Finite …
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `ENNReal.pow_lt_top`：pow_lt_top (ha : a < ∞) : a ^ n < ∞
· 使用引理 `ENNReal.ofNat_lt_top`：ofNat_lt_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) < ∞
-/
theorem minkowskiBound_lt_top : minkowskiBound K I < ⊤ := by
  classical
  -- FIXME: Make `finiteness` work here
  exact ENNReal.mul_lt_top (fundamentalDomain_isBounded _).measure_lt_top <|
    ENNReal.pow_lt_top ENNReal.ofNat_lt_top
/-
**NumberField.mixedEmbedding.minkowskiBound_pos** 是 Mathlib 中的一个定理，位于命名空间 `Numbe
rField.mixedEmbedding`。
形式化陈述：minkowskiBound_pos : 0 < minkowskiBound K I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `ENNReal.mul_pos`：mul_pos (ha : a != 0) (hb : b != 0) : 0 < a * b
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `ZSpan.measure_fundamentalDomain_ne_zero`：measure_fundamentalDomain_ne_ze
ro [Finite ι] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [Measure.IsAddH
aarMeasure μ] : μ (fundamenta…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.instFiniteIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule
`：∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZ
eroDivisors (NumberField.RingOfIntegers K)) K), Module.Finite …
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `NumberField.mixedEmbedding.instIsAddHaarMeasureMixedSpaceVolume`：∀ (K : 
Type u_1) [inst : Field K] [inst_1 : NumberField K], MeasureTheory.volume.IsAddH
aarMeasure
· 使用定理 `ENNReal.pow_ne_zero`：∀ {a : ENNReal}, a ≠ 0 → ∀ (n : ℕ), a ^ n ≠ 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
-/
theorem minkowskiBound_pos : 0 < minkowskiBound K I :=
  -- TODO: The `NormedAddCommGroup (mixedSpace K)` instance should not need any decidability.
  ENNReal.mul_pos (by classical exact ZSpan.measure_fundamentalDomain_ne_zero _) <|
    ENNReal.pow_ne_zero two_ne_zero _

variable {f : InfinitePlace K → ℝ≥0} (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)

open scoped Classical in
/-- Let `I` be a fractional ideal of `K`. Assume that `f : InfinitePlace K → ℝ≥0` is such that
`minkowskiBound K I < volume (convexBodyLT K f)` where `convexBodyLT K f` is the set of
points `x` such that `‖x w‖ < f w` for all infinite places `w` (see `convexBodyLT_volume` for
the computation of this volume), then there exists a nonzero algebraic number `a` in `I` such
that `w a < f w` for all infinite places `w`. -/
/-
**NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt** 是 Mathlib 中的一个定理，位于命名
空间 `NumberField.mixedEmbedding`。
形式化陈述：exists_ne_zero_mem_ideal_lt (h : minkowskiBound K I < volume (convexBodyLT
 K f)) : exists a in (I : FractionalIdeal (𝓞 K)⁰ K), a != 0 ∧ forall w : Infinit
ePlace K, w a < f w
参数：h : minkowskiBound K I < volume (convexBodyLT K f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `ZSpan.isAddFundamentalDomain'`：∀ {E : Type u_1} {ι : Type u_2} [inst : N
ormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Fini
te ι] [inst_3 : Mea…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.instFiniteIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule
`：∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZ
eroDivisors (NumberField.RingOfIntegers K)) K), Module.Finite …
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfF
inite`：∀ {E : Type u_1} {ι : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : N
ormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finite ι], DiscreteTopo…
· 使用定理 `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measu
re`：exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure [NormedAddCommG
roup E] [NormedSpace Real E] [BorelSpace E] [FiniteDimensional R…
· 使用定理 `NumberField.mixedEmbedding.instIsAddHaarMeasureMixedSpaceVolume`：∀ (K : 
Type u_1) [inst : Field K] [inst_1 : NumberField K], MeasureTheory.volume.IsAddH
aarMeasure
· 使用定理 `NumberField.mixedEmbedding.convexBodyLT_neg_mem`：convexBodyLT_neg_mem (x
 : mixedSpace K) (hx : x in (convexBodyLT K f)) : -x in (convexBodyLT K f)
· 使用定理 `NumberField.mixedEmbedding.convexBodyLT_convex`：convexBodyLT_convex : Co
nvex Real (convexBodyLT K f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Let `I` be a fractional ideal of `K`. Assume that `f : InfinitePlace K → ℝ≥0` is
 such that
`minkowskiBound K I < volume (convexBodyLT K f)` where `convexBodyLT K f` is the
 set of
points `x` such that `‖x w‖ < f w` for all infinite places `w` (see `convexBodyL
T_volume` for
the computation of this volume), then there exists a nonzero algebraic number `a
` in `I` such
that `w a < f w` for all infinite places `w`.
-/
theorem exists_ne_zero_mem_ideal_lt (h : minkowskiBound K I < volume (convexBodyLT K f)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < f w := by
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    h_fund (convexBodyLT_neg_mem K f) (convexBodyLT_convex K f) h
  rw [mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, by simpa using h_nz, (convexBodyLT_mem K f).mp h_mem⟩

open scoped Classical in
/-- A version of `exists_ne_zero_mem_ideal_lt` where the absolute value of the real part of `a` is
smaller than `1` at some fixed complex place. This is useful to ensure that `a` is not real. -/
/-
**NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt'** 是 Mathlib 中的一个定理，位于命
名空间 `NumberField.mixedEmbedding`。
形式化陈述：exists_ne_zero_mem_ideal_lt' (w₀ : {w : InfinitePlace K // IsComplex w}) (
h : minkowskiBound K I < volume (convexBodyLT' K f w₀)) : exists a in (I : Fract
ionalIdeal (𝓞 K)⁰ K), a != 0 ∧ (forall w : InfinitePlace K, w != w₀ -> w a < f w
) ∧ |(w₀.val.embedding a).re| < 1 ∧ |(w₀.val.embedding a).im| < (f w₀ : Real) ^ 
2
参数：w₀ : {w : InfinitePlace K // IsComplex w}；h : minkowskiBound K I < volume (co
nvexBodyLT' K f w₀)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `ZSpan.isAddFundamentalDomain'`：∀ {E : Type u_1} {ι : Type u_2} [inst : N
ormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Fini
te ι] [inst_3 : Mea…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.instFiniteIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule
`：∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZ
eroDivisors (NumberField.RingOfIntegers K)) K), Module.Finite …
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
· 使用定理 `ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfF
inite`：∀ {E : Type u_1} {ι : Type u_2} [inst : NormedAddCommGroup E] [inst_1 : N
ormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Finite ι], DiscreteTopo…
· 使用定理 `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measu
re`：exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure [NormedAddCommG
roup E] [NormedSpace Real E] [BorelSpace E] [FiniteDimensional R…
· 使用定理 `NumberField.mixedEmbedding.instIsAddHaarMeasureMixedSpaceVolume`：∀ (K : 
Type u_1) [inst : Field K] [inst_1 : NumberField K], MeasureTheory.volume.IsAddH
aarMeasure
· 使用定理 `NumberField.mixedEmbedding.convexBodyLT'_neg_mem`：∀ (K : Type u_1) [inst
 : Field K] (f : NumberField.InfinitePlace K → NNReal) (w₀ : { w // w.IsComplex 
}),   ∀ x ∈ NumberField.mixedEmbedding…
· 使用定理 `NumberField.mixedEmbedding.convexBodyLT'_convex`：∀ (K : Type u_1) [inst 
: Field K] (f : NumberField.InfinitePlace K → NNReal) (w₀ : { w // w.IsComplex }
),   Convex ℝ (NumberField.mixedEmbed…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
A version of `exists_ne_zero_mem_ideal_lt` where the absolute value of the real 
part of `a` is
smaller than `1` at some fixed complex place. This is useful to ensure that `a` 
is not real.
-/
theorem exists_ne_zero_mem_ideal_lt' (w₀ : {w : InfinitePlace K // IsComplex w})
    (h : minkowskiBound K I < volume (convexBodyLT' K f w₀)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ (∀ w : InfinitePlace K, w ≠ w₀ → w a < f w) ∧
      |(w₀.val.embedding a).re| < 1 ∧ |(w₀.val.embedding a).im| < (f w₀ : ℝ) ^ 2 := by
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    h_fund (convexBodyLT'_neg_mem K f w₀) (convexBodyLT'_convex K f w₀) h
  rw [mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, ha, by simpa using h_nz, (convexBodyLT'_mem K f w₀).mp h_mem⟩

open scoped Classical in
/-- A version of `exists_ne_zero_mem_ideal_lt` for the ring of integers of `K`. -/
/-
**NumberField.mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt** 是 Mathlib 中的
一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：exists_ne_zero_mem_ringOfIntegers_lt (h : minkowskiBound K ↑1 < volume (co
nvexBodyLT K f)) : exists a : 𝓞 K, a != 0 ∧ forall w : InfinitePlace K, w a < f 
w
参数：h : minkowskiBound K ↑1 < volume (convexBodyLT K f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt`：exists_ne_zero_m
em_ideal_lt (h : minkowskiBound K I < volume (convexBodyLT K f)) : exists a in (
I : FractionalIdeal (𝓞 K)⁰ K), a != 0 ∧ fora…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
· 使用引理 `NumberField.RingOfIntegers.coe_ne_zero_iff`：coe_ne_zero_iff {x : 𝓞 K} : 
algebraMap _ K x != 0 ↔ x != 0

--- 原说明 ---
A version of `exists_ne_zero_mem_ideal_lt` for the ring of integers of `K`.
-/
theorem exists_ne_zero_mem_ringOfIntegers_lt (h : minkowskiBound K ↑1 < volume (convexBodyLT K f)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ ∀ w : InfinitePlace K, w a < f w := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt K ↑1 h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

open scoped Classical in
/-- A version of `exists_ne_zero_mem_ideal_lt'` for the ring of integers of `K`. -/
/-
**NumberField.mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt'** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：exists_ne_zero_mem_ringOfIntegers_lt' (w₀ : {w : InfinitePlace K // IsComp
lex w}) (h : minkowskiBound K ↑1 < volume (convexBodyLT' K f w₀)) : exists a : 𝓞
 K, a != 0 ∧ (forall w : InfinitePlace K, w != w₀ -> w a < f w) ∧ |(w₀.val.embed
ding a).re| < 1 ∧ |(w₀.val.embedding a).im| < (f w₀ : Real) ^ 2
参数：w₀ : {w : InfinitePlace K // IsComplex w}；h : minkowskiBound K ↑1 < volume (c
onvexBodyLT' K f w₀)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_lt'`：exists_ne_zero_
mem_ideal_lt' (w₀ : {w : InfinitePlace K // IsComplex w}) (h : minkowskiBound K 
I < volume (convexBodyLT' K f w₀)) : exists a…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
· 使用引理 `NumberField.RingOfIntegers.coe_ne_zero_iff`：coe_ne_zero_iff {x : 𝓞 K} : 
algebraMap _ K x != 0 ↔ x != 0

--- 原说明 ---
A version of `exists_ne_zero_mem_ideal_lt'` for the ring of integers of `K`.
-/
theorem exists_ne_zero_mem_ringOfIntegers_lt' (w₀ : {w : InfinitePlace K // IsComplex w})
    (h : minkowskiBound K ↑1 < volume (convexBodyLT' K f w₀)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ (∀ w : InfinitePlace K, w ≠ w₀ → w a < f w) ∧
      |(w₀.val.embedding a).re| < 1 ∧ |(w₀.val.embedding a).im| < (f w₀ : ℝ) ^ 2 := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_lt' K ↑1 w₀ h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩
/-
**NumberField.mixedEmbedding.exists_primitive_element_lt_of_isReal** 是 Mathlib 中
的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：exists_primitive_element_lt_of_isReal {w₀ : InfinitePlace K} (hw₀ : IsReal
 w₀) {B : Real>=0} (hB : minkowskiBound K ↑1 < convexBodyLTFactor K * B) : exist
s a : 𝓞 K, Rat⟮(a : K)⟯ = ⊤ ∧ forall w : InfinitePlace K, w a < max B 1
参数：hw₀ : IsReal w₀；hB : minkowskiBound K ↑1 < convexBodyLTFactor K * B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.convexBodyLT_volume`：convexBodyLT_volume : vo
lume (convexBodyLT K f) = (convexBodyLTFactor K) * ∏ w, (f w) ^ (mult w)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_erase_mul`：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `ite_pow`：ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) : (if p then
 a else b) ^ c = if p then a ^ c else b ^ c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.prod_ite_eq'`：prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι)
 (b : ι -> M) : (∏ x in s, ite (x = a) (b x) 1) = ite (a in s) (b a) 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt`：exists_
ne_zero_mem_ringOfIntegers_lt (h : minkowskiBound K ↑1 < volume (convexBodyLT K 
f)) : exists a : 𝓞 K, a != 0 ∧ forall w : InfinitePla…
· 使用定理 `NumberField.is_primitive_element_of_infinitePlace_lt`：∀ {K : Type u_1} [
inst : Field K] [inst_1 : NumberField K] {x : NumberField.RingOfIntegers K}   {w
 : NumberField.InfinitePlace K},   x ≠ 0 →…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NNReal.coe_max`：coe_max (x y : Real>=0) : ((max x y : Real>=0) : Real) =
 max (x : Real) (y : Real)
-/
theorem exists_primitive_element_lt_of_isReal {w₀ : InfinitePlace K} (hw₀ : IsReal w₀) {B : ℝ≥0}
    (hB : minkowskiBound K ↑1 < convexBodyLTFactor K * B) :
    ∃ a : 𝓞 K, ℚ⟮(a : K)⟯ = ⊤ ∧
      ∀ w : InfinitePlace K, w a < max B 1 := by
  classical
  have : minkowskiBound K ↑1 < volume (convexBodyLT K (fun w ↦ if w = w₀ then B else 1)) := by
    rw [convexBodyLT_volume, ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Finset.notMem_erase, ite_false, mult, hw₀, ite_true, one_mul, pow_one]
    exact hB
  obtain ⟨a, h_nz, h_le⟩ := exists_ne_zero_mem_ringOfIntegers_lt K this
  refine ⟨a, ?_, fun w ↦ lt_of_lt_of_le (h_le w) ?_⟩
  · exact is_primitive_element_of_infinitePlace_lt h_nz
      (fun w h_ne ↦ by convert! (if_neg h_ne) ▸ h_le w) (Or.inl hw₀)
  · split_ifs <;> simp
/-
**NumberField.mixedEmbedding.exists_primitive_element_lt_of_isComplex** 是 Mathli
b 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：exists_primitive_element_lt_of_isComplex {w₀ : InfinitePlace K} (hw₀ : IsC
omplex w₀) {B : Real>=0} (hB : minkowskiBound K ↑1 < convexBodyLT'Factor K * B) 
: exists a : 𝓞 K, Rat⟮(a : K)⟯ = ⊤ ∧ forall w : InfinitePlace K, w a < Real.sqrt
 (1 + B ^ 2)
参数：hw₀ : IsComplex w₀；hB : minkowskiBound K ↑1 < convexBodyLT'Factor K * B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.convexBodyLT'_volume`：∀ (K : Type u_1) [inst 
: Field K] (f : NumberField.InfinitePlace K → NNReal) (w₀ : { w // w.IsComplex }
)   [inst_1 : NumberField K],   Measu…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_erase_mul`：prod_erase_mul [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (∏ x in s.erase a, f x) * f a = ∏ x in s, f x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `ite_pow`：ite_pow (p : Prop) [Decidable p] (a b : α) (c : β) : (if p then
 a else b) ^ c = if p then a ^ c else b ^ c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.prod_ite_eq'`：prod_ite_eq' [DecidableEq ι] (s : Finset ι) (a : ι)
 (b : ι -> M) : (∏ x in s, ite (x = a) (b x) 1) = ite (a in s) (b a) 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.InfinitePlace.not_isReal_iff_isComplex`：not_isReal_iff_isCom
plex {w : InfinitePlace K} : ¬IsReal w ↔ IsComplex w
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `NNReal.sq_sqrt`：∀ (x : NNReal), NNReal.sqrt x ^ 2 = x
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt'`：exists
_ne_zero_mem_ringOfIntegers_lt' (w₀ : {w : InfinitePlace K // IsComplex w}) (h :
 minkowskiBound K ↑1 < volume (convexBodyLT' K f w₀)) …
· 使用定理 `NumberField.is_primitive_element_of_infinitePlace_lt`：∀ {K : Type u_1} [
inst : Field K] [inst_1 : NumberField K] {x : NumberField.RingOfIntegers K}   {w
 : NumberField.InfinitePlace K},   x ≠ 0 →…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `NumberField.InfinitePlace.norm_embedding_eq`：norm_embedding_eq (w : Infi
nitePlace K) (x : K) : ‖(embedding w) x‖ = w x
· 使用定理 `Real.lt_sqrt`：lt_sqrt (hx : 0 <= x) : x < √y ↔ x ^ 2 < y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
（共 68 条，此处仅展示前 30 条）
-/
theorem exists_primitive_element_lt_of_isComplex {w₀ : InfinitePlace K} (hw₀ : IsComplex w₀)
    {B : ℝ≥0} (hB : minkowskiBound K ↑1 < convexBodyLT'Factor K * B) :
    ∃ a : 𝓞 K, ℚ⟮(a : K)⟯ = ⊤ ∧
      ∀ w : InfinitePlace K, w a < Real.sqrt (1 + B ^ 2) := by
  classical
  have : minkowskiBound K ↑1 <
      volume (convexBodyLT' K (fun w ↦ if w = w₀ then NNReal.sqrt B else 1) ⟨w₀, hw₀⟩) := by
    rw [convexBodyLT'_volume, ← Finset.prod_erase_mul _ _ (Finset.mem_univ w₀)]
    simp_rw [ite_pow, one_pow]
    rw [Finset.prod_ite_eq']
    simp_rw [Finset.notMem_erase, ite_false, mult, not_isReal_iff_isComplex.mpr hw₀,
      ite_true, ite_false, one_mul, NNReal.sq_sqrt]
    exact hB
  obtain ⟨a, h_nz, h_le, h_le₀⟩ := exists_ne_zero_mem_ringOfIntegers_lt' K ⟨w₀, hw₀⟩ this
  refine ⟨a, ?_, fun w ↦ ?_⟩
  · exact is_primitive_element_of_infinitePlace_lt h_nz
      (fun w h_ne ↦ by convert! if_neg h_ne ▸ h_le w h_ne) (Or.inr h_le₀.1)
  · by_cases h_eq : w = w₀
    · rw [if_pos rfl] at h_le₀
      dsimp only at h_le₀
      rw [h_eq, ← norm_embedding_eq, Real.lt_sqrt (norm_nonneg _), ← Complex.re_add_im
        (embedding w₀ _), Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
      refine add_lt_add ?_ ?_
      · rw [← sq_abs, sq_lt_one_iff₀ (abs_nonneg _)]
        exact h_le₀.1
      · rw [sq_lt_sq, NNReal.abs_eq, ← NNReal.sq_sqrt B]
        exact h_le₀.2
    · refine lt_of_lt_of_le (if_neg h_eq ▸ h_le w h_eq) ?_
      rw [NNReal.coe_one, Real.le_sqrt' zero_lt_one, one_pow]
      norm_num

open scoped Classical in
/-- Let `I` be a fractional ideal of `K`. Assume that `B : ℝ` is such that
`minkowskiBound K I < volume (convexBodySum K B)` where `convexBodySum K B` is the set of points
`x` such that `∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B` (see `convexBodySum_volume` for
the computation of this volume), then there exists a nonzero algebraic number `a` in `I` such
that `|Norm a| < (B / d) ^ d` where `d` is the degree of `K`. -/
/-
**NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_of_norm_le** 是 Mathlib 中的一
个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：exists_ne_zero_mem_ideal_of_norm_le {B : Real} (h : (minkowskiBound K I) <
= volume (convexBodySum K B)) : exists a in (I : FractionalIdeal (𝓞 K)⁰ K), a !=
 0 ∧ |Algebra.norm Rat (a : K)| <= (B / finrank Rat K) ^ finrank Rat K
参数：h : (minkowskiBound K I) <= volume (convexBodySum K B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.mixedEmbedding.convexBodySum_volume_eq_zero_of_le_zero`：conv
exBodySum_volume_eq_zero_of_le_zero {B} (hB : B <= 0) : volume (convexBodySum K 
B) = 0
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NumberField.mixedEmbedding.minkowskiBound_pos`：minkowskiBound_pos : 0 < 
minkowskiBound K I
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `NumberField.instFreeIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule`：
∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZer
oDivisors (NumberField.RingOfIntegers K)) K), Module.Free ℤ …
· 使用定理 `ZSpan.isAddFundamentalDomain'`：∀ {E : Type u_1} {ι : Type u_2} [inst : N
ormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] (b : Module.Basis ι ℝ E)   [Fini
te ι] [inst_3 : Mea…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NumberField.instFiniteIntSubtypeMemSubmoduleRingOfIntegersCoeToSubmodule
`：∀ (K : Type u_1) [inst : Field K] [NumberField K]   (I : FractionalIdeal (nonZ
eroDivisors (NumberField.RingOfIntegers K)) K), Module.Finite …
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
Let `I` be a fractional ideal of `K`. Assume that `B : ℝ` is such that
`minkowskiBound K I < volume (convexBodySum K B)` where `convexBodySum K B` is t
he set of points
`x` such that `∑ w real, ‖x w‖ + 2 * ∑ w complex, ‖x w‖ ≤ B` (see `convexBodySum
_volume` for
the computation of this volume), then there exists a nonzero algebraic number `a
` in `I` such
that `|Norm a| < (B / d) ^ d` where `d` is the degree of `K`.
-/
theorem exists_ne_zero_mem_ideal_of_norm_le {B : ℝ}
    (h : (minkowskiBound K I) ≤ volume (convexBodySum K B)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧
      |Algebra.norm ℚ (a : K)| ≤ (B / finrank ℚ K) ^ finrank ℚ K := by
  have hB : 0 ≤ B := by
    contrapose! h
    rw [convexBodySum_volume_eq_zero_of_le_zero K (le_of_lt h)]
    exact minkowskiBound_pos K I
  -- Some inequalities that will be useful later on
  have h1 : 0 < (finrank ℚ K : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr finrank_pos)
  have h2 : 0 ≤ B / (finrank ℚ K) := div_nonneg hB (Nat.cast_nonneg _)
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (span ℤ (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      h_fund (fun _ ↦ convexBodySum_neg_mem K B) (convexBodySum_convex K B)
      (convexBodySum_compact K B) h
  rw [mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ha, by simpa using h_nz, ?_⟩
  rw [← rpow_natCast, ← rpow_le_rpow_iff (by simp only [Rat.cast_abs, abs_nonneg])
      (rpow_nonneg h2 _) h1, ← rpow_mul h2, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr
      (ne_of_gt finrank_pos)), rpow_one, le_div_iff₀' (Nat.cast_pos.mpr finrank_pos)]
  refine le_trans ?_ ((convexBodySum_mem K B).mp h_mem)
  rw [← le_div_iff₀' (Nat.cast_pos.mpr finrank_pos), ← sum_mult_eq, Nat.cast_sum]
  refine le_trans ?_ (geom_mean_le_arith_mean Finset.univ _ _ (fun _ _ => Nat.cast_nonneg _)
    ?_ (fun _ _ => AbsoluteValue.nonneg _ _))
  · simp_rw [← prod_eq_abs_norm, rpow_natCast]
    exact le_of_eq rfl
  · rw [← Nat.cast_sum, sum_mult_eq, Nat.cast_pos]
    exact finrank_pos

open scoped Classical in
/-
**NumberField.mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_of_norm_le** 是 Ma
thlib 中的一个定理，位于命名空间 `NumberField.mixedEmbedding`。
形式化陈述：exists_ne_zero_mem_ringOfIntegers_of_norm_le {B : Real} (h : (minkowskiBou
nd K ↑1) <= volume (convexBodySum K B)) : exists a : 𝓞 K, a != 0 ∧ |Algebra.norm
 Rat (a : K)| <= (B / finrank Rat K) ^ finrank Rat K
参数：h : (minkowskiBound K ↑1) <= volume (convexBodySum K B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `Complex.instFiniteDimensionalReal`：FiniteDimensional ℝ ℂ
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.mixedEmbedding.exists_ne_zero_mem_ideal_of_norm_le`：exists_n
e_zero_mem_ideal_of_norm_le {B : Real} (h : (minkowskiBound K I) <= volume (conv
exBodySum K B)) : exists a in (I : FractionalIdeal (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
· 使用引理 `NumberField.RingOfIntegers.coe_ne_zero_iff`：coe_ne_zero_iff {x : 𝓞 K} : 
algebraMap _ K x != 0 ↔ x != 0
-/
theorem exists_ne_zero_mem_ringOfIntegers_of_norm_le {B : ℝ}
    (h : (minkowskiBound K ↑1) ≤ volume (convexBodySum K B)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ |Algebra.norm ℚ (a : K)| ≤ (B / finrank ℚ K) ^ finrank ℚ K := by
  obtain ⟨_, h_mem, h_nz, h_bd⟩ := exists_ne_zero_mem_ideal_of_norm_le K ↑1 h
  obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp h_mem
  exact ⟨a, RingOfIntegers.coe_ne_zero_iff.mp h_nz, h_bd⟩

end minkowski

end NumberField.mixedEmbedding

