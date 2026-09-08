/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# L-series of functions on `ZMod N`

We show that if `N` is a positive integer and `Φ : ZMod N → ℂ`, then the L-series of `Φ` has
analytic continuation (away from a pole at `s = 1` if `∑ j, Φ j ≠ 0`) and satisfies a functional
equation. We also define completed L-functions (given by multiplying the naive L-function by a
Gamma-factor), and prove analytic continuation and functional equations for these too, assuming `Φ`
is either even or odd.

The most familiar case is when `Φ` is a Dirichlet character, but the results here are valid
for general functions; for the specific case of Dirichlet characters see
`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`.

## Main definitions

* `ZMod.LFunction Φ s`: the meromorphic continuation of the function `∑ n : ℕ, Φ n * n ^ (-s)`.
* `ZMod.completedLFunction Φ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction Φ s` multiplied by an Archimedean Gamma-factor.

Note that `ZMod.completedLFunction Φ s` is only mathematically well-defined if `Φ` is either even
or odd. Here we extend it to all functions `Φ` by linearity (but the functional equation only holds
if `Φ` is either even or odd).

## Main theorems

Results for non-completed L-functions:

* `ZMod.LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive
  `LSeries`.
* `ZMod.differentiableAt_LFunction`: `ZMod.LFunction Φ` is differentiable at `s ∈ ℂ` if either
  `s ≠ 1` or `∑ j, Φ j = 0`.
* `ZMod.LFunction_one_sub`: the functional equation relating `LFunction Φ (1 - s)` to
  `LFunction (𝓕 Φ) s`, where `𝓕` is the Fourier transform.

Results for completed L-functions:

* `ZMod.LFunction_eq_completed_div_gammaFactor_even` and
  `LFunction_eq_completed_div_gammaFactor_odd`: we have
  `LFunction Φ s = completedLFunction Φ s / Gammaℝ s` for `Φ` even, and
  `LFunction Φ s = completedLFunction Φ s / Gammaℝ (s + 1)` for `Φ` odd. (We formulate it this way
  so that it is still valid at the poles of the Gamma factor.)
* `ZMod.differentiableAt_completedLFunction`: `ZMod.completedLFunction Φ` is differentiable at
  `s ∈ ℂ`, unless `s = 1` and `∑ j, Φ j ≠ 0`, or `s = 0` and `Φ 0 ≠ 0`.
* `ZMod.completedLFunction_one_sub_even` and `ZMod.completedLFunction_one_sub_odd`:
  the functional equation relating `completedLFunction Φ (1 - s)` to `completedLFunction (𝓕 Φ) s`.
-/

@[expose] public section

open HurwitzZeta Complex ZMod Finset Topology Filter Set

open scoped Real

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- If `Φ` is a periodic function, then the L-series of `Φ` converges for `1 < re s`. -/
/-
**ZMod.LSeriesSummable_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：LSeriesSummable_of_one_lt_re (Φ : ZMod N -> Complex) {s : Complex} (hs : 1
 < re s) : LSeriesSummable (Φ ·) s
参数：Φ : ZMod N -> Complex；hs : 1 < re s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LSeriesSummable_of_bounded_of_one_lt_re`：LSeriesSummable_of_bounded_of_o
ne_lt_re {f : Nat -> Complex} {m : Real} (h : forall n != 0, ‖f n‖ <= m) {s : Co
mplex} (hs : 1 < s.re) : LSer…
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
If `Φ` is a periodic function, then the L-series of `Φ` converges for `1 < re s`
.
-/
lemma LSeriesSummable_of_one_lt_re (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LSeriesSummable (Φ ·) s := by
  let c := max' _ <| univ_nonempty.image (norm ∘ Φ)
  refine LSeriesSummable_of_bounded_of_one_lt_re (fun n _ ↦ le_max' _ _ ?_) (m := c) hs
  exact mem_image_of_mem _ (mem_univ _)

/--
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, Φ n / n ^ s` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zeta functions.

Note that this is not the same as `LSeries Φ`: they agree in the convergence range, but
`LSeries Φ s` is defined to be `0` if `re s ≤ 1`.
-/
/-
**ZMod.LFunction** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：LFunction (Φ : ZMod N -> Complex) (s : Complex) : Complex
参数：Φ : ZMod N -> Complex；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique meromorphic function `ℂ → ℂ` which agrees with `∑' n : ℕ, Φ n / n ^ s
` wherever the
latter is convergent. This is constructed as a linear combination of Hurwitz zet
a functions.

Note that this is not the same as `LSeries Φ`: they agree in the convergence ran
ge, but
`LSeries Φ s` is defined to be `0` if `re s ≤ 1`.
-/
noncomputable def LFunction (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s

/-- The L-function of a function on `ZMod 1` is a scalar multiple of the Riemann zeta function. -/
/-
**ZMod.LFunction_modOne_eq** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：LFunction_modOne_eq (Φ : ZMod 1 -> Complex) (s : Complex) : LFunction Φ s 
= Φ 0 * riemannZeta s
参数：Φ : ZMod 1 -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.one_cpow`：one_cpow (x : Complex) : (1 : Complex) ^ x = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.singleton_eq_univ`：singleton_eq_univ [Subsingleton α] (a : α) : (
{a} : Finset α) = univ
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `HurwitzZeta.hurwitzZeta_zero`：HurwitzZeta.hurwitzZeta_zero : hurwitzZeta
 0 = riemannZeta
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The L-function of a function on `ZMod 1` is a scalar multiple of the Riemann zet
a function.
-/
lemma LFunction_modOne_eq (Φ : ZMod 1 → ℂ) (s : ℂ) :
    LFunction Φ s = Φ 0 * riemannZeta s := by
  simp only [LFunction, Nat.cast_one, one_cpow, ← singleton_eq_univ (0 : ZMod 1), sum_singleton,
    map_zero, hurwitzZeta_zero, one_mul]

/-- For `1 < re s` the congruence L-function agrees with the sum of the Dirichlet series. -/
/-
**ZMod.LFunction_eq_LSeries** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：LFunction_eq_LSeries (Φ : ZMod N -> Complex) {s : Complex} (hs : 1 < re s)
 : LFunction Φ s = LSeries (Φ ·) s
参数：Φ : ZMod N -> Complex；hs : 1 < re s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.LFunction.eq_1`：∀ {N : ℕ} [inst : NeZero N] (Φ : ZMod N → ℂ) (s : ℂ
),   ZMod.LFunction Φ s = ↑N ^ (-s) * ∑ j, Φ j * HurwitzZeta.hurwitzZeta (ZMod.t
oAddCircl…
· 使用定理 `LSeries.eq_1`：∀ (f : ℕ → ℂ) (s : ℂ), LSeries f s = ∑' (n : ℕ), LSeries.t
erm f s n
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用引理 `Nat.sumByResidueClasses`：Nat.sumByResidueClasses {R : Type*} [AddCommGro
up R] [UniformSpace R] [IsUniformAddGroup R] [CompleteSpace R] [T0Space R] {f : 
Nat -> R} (hf…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `ZMod.LSeriesSummable_of_one_lt_re`：LSeriesSummable_of_one_lt_re (Φ : ZMo
d N -> Complex) {s : Complex} (hs : 1 < re s) : LSeriesSummable (Φ ·) s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `div_le_one`：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
（共 72 条，此处仅展示前 30 条）

--- 原说明 ---
For `1 < re s` the congruence L-function agrees with the sum of the Dirichlet se
ries.
-/
lemma LFunction_eq_LSeries (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LFunction Φ s = LSeries (Φ ·) s := by
  rw [LFunction, LSeries, mul_sum, Nat.sumByResidueClasses (LSeriesSummable_of_one_lt_re Φ hs) N]
  congr 1 with j
  have : (j.val / N : ℝ) ∈ Set.Icc 0 1 := mem_Icc.mpr ⟨by positivity,
    (div_le_one (Nat.cast_pos.mpr <| NeZero.pos _)).mpr <| Nat.cast_le.mpr (val_lt j).le⟩
  rw [toAddCircle_apply, ← (hasSum_hurwitzZeta_of_one_lt_re this hs).tsum_eq, ← mul_assoc,
    ← tsum_mul_left]
  congr 1 with m
  -- The following manipulation is slightly delicate because `(x * y) ^ s = x ^ s * y ^ s` is
  -- false for general complex `x`, `y`, but it is true if `x` and `y` are non-negative reals, so
  -- we have to carefully juggle coercions `ℕ → ℝ → ℂ`.
  calc N ^ (-s) * Φ j * (1 / (m + (j.val / N : ℝ)) ^ s)
  _ = Φ j * (N ^ (-s) * (1 / (m + (j.val / N : ℝ)) ^ s)) := by
    rw [← mul_assoc, mul_comm _ (Φ _)]
  _ = Φ j * (1 / (N : ℝ) ^ s * (1 / ((j.val + N * m) / N : ℝ) ^ s)) := by
    simp only [cpow_neg, ← one_div, ofReal_div, ofReal_natCast, add_comm, add_div, ofReal_add,
      ofReal_mul, mul_div_cancel_left₀ (m : ℂ) (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  _ = Φ j / ((N : ℝ) * ((j.val + N * m) / N : ℝ)) ^ s := by -- this is the delicate step!
    rw [one_div_mul_one_div, mul_one_div, mul_cpow_ofReal_nonneg] <;> positivity
  _ = Φ j / (N * (j.val + N * m) / N) ^ s := by
    simp only [ofReal_natCast, ofReal_div, ofReal_add, ofReal_mul, mul_div_assoc]
  _ = Φ j / (j.val + N * m) ^ s := by
    rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  _ = Φ ↑(j.val + N * m) / (↑(j.val + N * m)) ^ s := by
    simp only [Nat.cast_add, Nat.cast_mul, natCast_zmod_val, natCast_self, zero_mul, add_zero]
  _ = LSeries.term (Φ ·) s (j.val + N * m) := by
    rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs)]
/-
**ZMod.differentiableAt_LFunction** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：differentiableAt_LFunction (Φ : ZMod N -> Complex) (s : Complex) (hs : s !
= 1 ∨ ∑ j, Φ j = 0) : DifferentiableAt Complex (LFunction Φ) s
参数：Φ : ZMod N -> Complex；s : Complex；hs : s != 1 ∨ ∑ j, Φ j = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.mul`：DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x)
 (hb : DifferentiableAt 𝕜 b x) : DifferentiableAt 𝕜 (a * b) x
· 使用定理 `DifferentiableAt.fun_comp'`：DifferentiableAt.fun_comp' {f : E -> F} {g :
 F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : Diffe
rentiableAt 𝕜 (f…
· 使用引理 `differentiableAt_const_cpow_of_neZero`：differentiableAt_const_cpow_of_ne
Zero (z : Complex) [NeZero z] (t : Complex) : DifferentiableAt Complex (fun s : 
Complex => z ^ s) t
· 使用定理 `DifferentiableAt.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `DifferentiableAt.fun_sum`：DifferentiableAt.fun_sum (h : forall i in u, D
ifferentiableAt 𝕜 (A i) x) : DifferentiableAt 𝕜 (fun y => ∑ i in u, A i y) x
· 使用定理 `DifferentiableAt.const_mul`：DifferentiableAt.const_mul (ha : Differentia
bleAt 𝕜 a x) (b : 𝔸) : DifferentiableAt 𝕜 (fun y => b * a y) x
· 使用引理 `HurwitzZeta.differentiableAt_hurwitzZeta`：differentiableAt_hurwitzZeta (
a : UnitAddCircle) {s : Complex} (hs : s != 1) : DifferentiableAt Complex (hurwi
tzZeta a) s
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用引理 `HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div`：differentiableAt_h
urwitzZeta_sub_one_div (a : UnitAddCircle) : DifferentiableAt Complex (fun s => 
hurwitzZeta a s - 1 / (s - 1) / GammaReal …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Or.neg_resolve_left`：∀ {a b : Prop}, ¬a ∨ b → a → b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma differentiableAt_LFunction (Φ : ZMod N → ℂ) (s : ℂ) (hs : s ≠ 1 ∨ ∑ j, Φ j = 0) :
    DifferentiableAt ℂ (LFunction Φ) s := by
  refine .mul (by fun_prop) ?_
  rcases ne_or_eq s 1 with hs' | rfl
  · exact .fun_sum fun j _ ↦ (differentiableAt_hurwitzZeta _ hs').const_mul _
  · have := DifferentiableAt.fun_sum (u := univ) fun j _ ↦
      (differentiableAt_hurwitzZeta_sub_one_div (toAddCircle j)).const_mul (Φ j)
    simpa only [mul_sub, sum_sub_distrib, ← sum_mul, hs.neg_resolve_left rfl, zero_mul, sub_zero]
/-
**ZMod.differentiable_LFunction_of_sum_zero** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：differentiable_LFunction_of_sum_zero {Φ : ZMod N -> Complex} (hΦ : ∑ j, Φ 
j = 0) : Differentiable Complex (LFunction Φ)
参数：hΦ : ∑ j, Φ j = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ZMod.differentiableAt_LFunction`：differentiableAt_LFunction (Φ : ZMod N 
-> Complex) (s : Complex) (hs : s != 1 ∨ ∑ j, Φ j = 0) : DifferentiableAt Comple
x (LFunction Φ) s
-/
lemma differentiable_LFunction_of_sum_zero {Φ : ZMod N → ℂ} (hΦ : ∑ j, Φ j = 0) :
    Differentiable ℂ (LFunction Φ) :=
  fun s ↦ differentiableAt_LFunction Φ s (Or.inr hΦ)

/-- The L-function of `Φ` has a residue at `s = 1` equal to the average value of `Φ`. -/
/-
**ZMod.LFunction_residue_one** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：LFunction_residue_one (Φ : ZMod N -> Complex) : Tendsto (fun s => (s - 1) 
* LFunction Φ s) (𝓝[!=] 1) (𝓝 (∑ j, Φ j / N))
参数：Φ : ZMod N -> Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `tendsto_finsetSum`：∀ {ι : Type u_1} {α : Type u_2} {M : Type u_3} [inst 
: TopologicalSpace M] [inst_1 : AddCommMonoid M] [ContinuousAdd M]   {f : ι → α 
→ M} {x…
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
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The L-function of `Φ` has a residue at `s = 1` equal to the average value of `Φ`
.
-/
lemma LFunction_residue_one (Φ : ZMod N → ℂ) :
    Tendsto (fun s ↦ (s - 1) * LFunction Φ s) (𝓝[≠] 1) (𝓝 (∑ j, Φ j / N)) := by
  simp only [LFunction, mul_sum]
  refine tendsto_finsetSum _ fun j _ ↦ ?_
  rw [(by ring : Φ j / N = Φ j * (1 / N * 1)), one_div, ← cpow_neg_one]
  simp only [show ∀ a b c d : ℂ, a * (b * (c * d)) = c * (b * (a * d)) by intros; ring]
  refine tendsto_const_nhds.mul (.mul ?_ <| hurwitzZeta_residue_one _)
  exact ((continuous_neg.const_cpow (Or.inl <| NeZero.ne _)).tendsto _).mono_left
    nhdsWithin_le_nhds

local notation "𝕖" => stdAddChar

/--
The `LFunction` of the function `x ↦ e (j * x)`, where `e : ZMod N → ℂ` is the standard additive
character, agrees with `expZeta (j / N)` on `1 < re s`. Private since it is a stepping-stone to
the more general result `LFunction_stdAddChar_eq_expZeta` below.
-/
/-
**ZMod.LFunction_stdAddChar_eq_expZeta_of_one_lt_re** 是 Mathlib 中的一个引理，位于命名空间 `Z
Mod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `LFunction` of the function `x ↦ e (j * x)`, where `e : ZMod N → ℂ` is the s
tandard additive
character, agrees with `expZeta (j / N)` on `1 < re s`. Private since it is a st
epping-stone to
the more general result `LFunction_stdAddChar_eq_expZeta` below.
-/
private lemma LFunction_stdAddChar_eq_expZeta_of_one_lt_re (j : ZMod N) {s : ℂ} (hs : 1 < s.re) :
    LFunction (fun k ↦ 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s := by
  rw [toAddCircle_apply, ← (hasSum_expZeta_of_one_lt_re (j.val / N) hs).tsum_eq,
    LFunction_eq_LSeries _ hs, LSeries]
  congr 1 with n
  rw [LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), ofReal_div, ofReal_natCast,
    ofReal_natCast, mul_assoc, div_mul_eq_mul_div, stdAddChar_apply]
  have := ZMod.toCircle_intCast (N := N) (j.val * n)
  conv_rhs at this => rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, mul_div_assoc]
  rw [← this, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, natCast_zmod_val]

/--
The `LFunction` of the function `x ↦ e (j * x)`, where `e : ZMod N → ℂ` is the standard additive
character, is `expZeta (j / N)`.

Note this is not at all obvious from the definitions, and we prove it by analytic continuation
from the convergence range.
-/
/-
**ZMod.LFunction_stdAddChar_eq_expZeta** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：LFunction_stdAddChar_eq_expZeta (j : ZMod N) (s : Complex) (hjs : j != 0 ∨
 s != 1) : LFunction (fun k => 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s
参数：j : ZMod N；s : Complex；hjs : j != 0 ∨ s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用引理 `ZMod.differentiableAt_LFunction`：differentiableAt_LFunction (Φ : ZMod N 
-> Complex) (s : Complex) (hs : s != 1 ∨ ∑ j, Φ j = 0) : DifferentiableAt Comple
x (LFunction Φ) s
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `AddChar.sum_mulShift`：sum_mulShift {R : Type*} [CommRing R] [Fintype R] 
[DecidableEq R] {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar R R'} (b :
 R) (hψ : …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `ZMod.isPrimitive_stdAddChar`：isPrimitive_stdAddChar (N : Nat) [NeZero N]
 : (stdAddChar (N
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
（共 70 条，此处仅展示前 30 条）

--- 原说明 ---
The `LFunction` of the function `x ↦ e (j * x)`, where `e : ZMod N → ℂ` is the s
tandard additive
character, is `expZeta (j / N)`.

Note this is not at all obvious from the definitions, and we prove it by analyti
c continuation
from the convergence range.
-/
lemma LFunction_stdAddChar_eq_expZeta (j : ZMod N) (s : ℂ) (hjs : j ≠ 0 ∨ s ≠ 1) :
    LFunction (fun k ↦ 𝕖 (j * k)) s = expZeta (ZMod.toAddCircle j) s := by
  let U := if j = 0 then {z : ℂ | z ≠ 1} else univ -- region of analyticity of both functions
  let V := {z : ℂ | 1 < re z} -- convergence region
  have hUo : IsOpen U := by
    by_cases h : j = 0
    · simpa only [h, ↓reduceIte, U] using! isOpen_compl_singleton
    · simp only [h, ↓reduceIte, isOpen_univ, U]
  let f := LFunction (fun k ↦ stdAddChar (j * k))
  let g := expZeta (toAddCircle j)
  have hU {u} : u ∈ U ↔ u ≠ 1 ∨ j ≠ 0 := by simp only [mem_ite_univ_right, U]; tauto
  -- hypotheses for uniqueness of analytic continuation
  have hf : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu ↦ ?_) hUo
    refine (differentiableAt_LFunction _ _ ((hU.mp hu).imp_right fun h ↦ ?_)).differentiableWithinAt
    simp only [mul_comm j, AddChar.sum_mulShift _ (isPrimitive_stdAddChar _), h,
      ↓reduceIte, CharP.cast_eq_zero]
  have hg : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd (fun u hu ↦ ?_) hUo
    refine (differentiableAt_expZeta _ _ ((hU.mp hu).imp_right fun h ↦ ?_)).differentiableWithinAt
    rwa [ne_eq, toAddCircle_eq_zero]
  have hUc : IsPreconnected U := by
    by_cases h : j = 0
    · simpa only [h, ↓reduceIte, U] using!
        (isConnected_compl_singleton_of_one_lt_rank (by simp) _).isPreconnected
    · simpa only [h, ↓reduceIte, U] using isPreconnected_univ
  have hV : V ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hUmem : 2 ∈ U := by simp [U]
  have hUmem' : s ∈ U := hU.mpr hjs.symm
  -- apply uniqueness result
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hUc hUmem ?_ hUmem'
  -- now remains to prove equality on `1 < re s`
  filter_upwards [hV] with z using LFunction_stdAddChar_eq_expZeta_of_one_lt_re _

/-- Explicit formula for the L-function of `𝓕 Φ`, where `𝓕` is the discrete Fourier transform. -/
/-
**ZMod.LFunction_dft** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：LFunction_dft (Φ : ZMod N -> Complex) {s : Complex} (hs : Φ 0 = 0 ∨ s != 1
) : LFunction (𝓕 Φ) s = ∑ j : ZMod N, Φ j * expZeta (toAddCircle (-j)) s
参数：Φ : ZMod N -> Complex；hs : Φ 0 = 0 ∨ s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZMod.LFunction_stdAddChar_eq_expZeta`：LFunction_stdAddChar_eq_expZeta (j
 : ZMod N) (s : Complex) (hjs : j != 0 ∨ s != 1) : LFunction (fun k => 𝕖 (j * k)
) s = expZeta (ZMod.toAddC…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.dft_def`：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCo
mmGroup E] [inst_2 : _root_.Module ℂ E] (Φ : ZMod N → E),   ZMod.dft Φ = fun k =
> …
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)

--- 原说明 ---
Explicit formula for the L-function of `𝓕 Φ`, where `𝓕` is the discrete Fourier 
transform.
-/
lemma LFunction_dft (Φ : ZMod N → ℂ) {s : ℂ} (hs : Φ 0 = 0 ∨ s ≠ 1) :
    LFunction (𝓕 Φ) s = ∑ j : ZMod N, Φ j * expZeta (toAddCircle (-j)) s := by
  have (j : ZMod N) : Φ j * LFunction (fun k ↦ 𝕖 (-j * k)) s =
      Φ j * expZeta (toAddCircle (-j)) s := by
    by_cases h : -j ≠ 0 ∨ s ≠ 1
    · rw [LFunction_stdAddChar_eq_expZeta _ _ h]
    · simp only [neg_ne_zero, not_or, not_not] at h
      rw [h.1, show Φ 0 = 0 by tauto, zero_mul, zero_mul]
  simp only [LFunction, ← this, mul_sum]
  rw [dft_def, sum_comm]
  simp only [sum_mul, mul_sum, smul_eq_mul, stdAddChar_apply, ← mul_assoc]
  congr 1 with j
  congr 1 with k
  rw [mul_assoc (Φ _), mul_comm (Φ _), neg_mul]

/-- Functional equation for `ZMod` L-functions, in terms of discrete Fourier transform. -/
/-
**ZMod.LFunction_one_sub** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：LFunction_one_sub (Φ : ZMod N -> Complex) {s : Complex} (hs : forall (n : 
Nat), s != -n) (hs' : Φ 0 = 0 ∨ s != 1) : LFunction Φ (1 - s) = N ^ (s - 1) * (2
 * π) ^ (-s) * Gamma s * (cexp (π * I * s / 2) * LFunction (𝓕 Φ) s + cexp (-π * 
I * s / 2) * LFunction (𝓕 fun x => Φ (-x)) s)
参数：Φ : ZMod N -> Complex；hs : forall (n : Nat), s != -n；hs' : Φ 0 = 0 ∨ s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.LFunction.eq_1`：∀ {N : ℕ} [inst : NeZero N] (Φ : ZMod N → ℂ) (s : ℂ
),   ZMod.LFunction Φ s = ↑N ^ (-s) * ∑ j, Φ j * HurwitzZeta.hurwitzZeta (ZMod.t
oAddCircl…
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HurwitzZeta.hurwitzZeta_one_sub`：hurwitzZeta_one_sub (a : UnitAddCircle)
 {s : Complex} (hs : forall (n : Nat), s != -n) (hs' : a != 0 ∨ s != 1) : hurwit
zZeta a (1 - s) = (2 …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ZMod.toAddCircle_eq_zero`：∀ {N : ℕ} [inst : NeZero N] {j : ZMod N}, ZMod
.toAddCircle j = 0 ↔ j = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `ZMod.LFunction_dft`：LFunction_dft (Φ : ZMod N -> Complex) {s : Complex} 
(hs : Φ 0 = 0 ∨ s != 1) : LFunction (𝓕 Φ) s = ∑ j : ZMod N, Φ j * expZeta (toAdd
Circle (…
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Equiv.Perm.sum_comp`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] (σ : Equiv.Perm ι) (s : Finset ι) (f : ι → M),   {a | σ a ≠ a} ⊆ ↑s → ∑ x 
∈ s, f (σ…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Functional equation for `ZMod` L-functions, in terms of discrete Fourier transfo
rm.
-/
theorem LFunction_one_sub (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -n) (hs' : Φ 0 = 0 ∨ s ≠ 1) :
    LFunction Φ (1 - s) = N ^ (s - 1) * (2 * π) ^ (-s) * Gamma s *
      (cexp (π * I * s / 2) * LFunction (𝓕 Φ) s
       + cexp (-π * I * s / 2) * LFunction (𝓕 fun x ↦ Φ (-x)) s) := by
  rw [LFunction]
  have (j : ZMod N) : Φ j * hurwitzZeta (toAddCircle j) (1 - s) = Φ j *
      ((2 * π) ^ (-s) * Gamma s * (cexp (-π * I * s / 2) *
      expZeta (toAddCircle j) s + cexp (π * I * s / 2) * expZeta (-toAddCircle j) s)) := by
    rcases eq_or_ne j 0 with rfl | hj
    · rcases hs' with hΦ | hs'
      · simp only [hΦ, zero_mul]
      · rw [hurwitzZeta_one_sub _ hs (Or.inr hs')]
    · rw [hurwitzZeta_one_sub _ hs (Or.inl <| toAddCircle_eq_zero.not.mpr hj)]
  simp only [this, mul_assoc _ _ (Gamma s)]
  -- get rid of Gamma terms and power of N
  generalize (2 * π) ^ (-s) * Gamma s = C
  simp_rw [← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum, ← mul_assoc, mul_comm _ C, mul_assoc,
    neg_sub]
  congr 2
  -- now gather sum terms
  rw [LFunction_dft _ hs', LFunction_dft _ (hs'.imp_left <| by simp only [neg_zero, imp_self])]
  conv_rhs => enter [2, 2]; rw [← (Equiv.neg _).sum_comp _ _ (by simp), Equiv.neg_apply]
  simp_rw [neg_neg, mul_sum, ← sum_add_distrib, ← mul_assoc, mul_comm _ (Φ _), mul_assoc,
    ← mul_add, map_neg, add_comm]

section signed

variable {Φ : ZMod N → ℂ}

/-
**ZMod.LFunction_def_even** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：LFunction_def_even (hΦ : Φ.Even) (s : Complex) : LFunction Φ s = N ^ (-s) 
* ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j) s
参数：hΦ : Φ.Even；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `HurwitzZeta.hurwitzZetaOdd_neg`：hurwitzZetaOdd_neg (a : UnitAddCircle) (
s : Complex) : hurwitzZetaOdd (-a) s = -hurwitzZetaOdd a s
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LFunction_def_even (hΦ : Φ.Even) (s : ℂ) :
    LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j) s := by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_eq_left, ← neg_eq_self, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaOdd_neg, mul_neg]
/-
**ZMod.LFunction_def_odd** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：LFunction_def_odd (hΦ : Φ.Odd) (s : Complex) : LFunction Φ s = N ^ (-s) * 
∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s
参数：hΦ : Φ.Odd；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.neg_apply`：∀ (G : Type u_14) [inst : InvolutiveNeg G], ⇑(Equiv.neg
 G) = Neg.neg
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `HurwitzZeta.hurwitzZetaEven_neg`：hurwitzZetaEven_neg (a : UnitAddCircle)
 (s : Complex) : hurwitzZetaEven (-a) s = hurwitzZetaEven a s
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LFunction_def_odd (hΦ : Φ.Odd) (s : ℂ) :
    LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s := by
  simp only [LFunction, hurwitzZeta, mul_add (Φ _), sum_add_distrib]
  congr 1
  simp only [add_eq_right, ← neg_eq_self, ← sum_neg_distrib]
  refine Fintype.sum_equiv (.neg _) _ _ fun i ↦ ?_
  simp only [Equiv.neg_apply, hΦ i, map_neg, hurwitzZetaEven_neg, neg_mul]

/-- Explicit formula for `LFunction Φ 0` when `Φ` is even. -/
/-
**ZMod.LFunction_apply_zero_of_even** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {Φ : ZMod N → ℂ}, Function.Even Φ → ZMod.LFunc
tion Φ 0 = -Φ 0 / 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用引理 `ZMod.LFunction_def_even`：LFunction_def_even (hΦ : Φ.Even) (s : Complex) 
: LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j)
 s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `HurwitzZeta.hurwitzZetaEven_apply_zero`：hurwitzZetaEven_apply_zero (a : 
UnitAddCircle) : hurwitzZetaEven a 0 = if a = 0 then -1 / 2 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_div`：mul_div (a b c : G) : a * (b / c) = a * b / c
· 使用定理 `mul_neg_one`：mul_neg_one (a : α) : a * -1 = -a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Explicit formula for `LFunction Φ 0` when `Φ` is even.
-/
@[simp] lemma LFunction_apply_zero_of_even (hΦ : Φ.Even) :
    LFunction Φ 0 = -Φ 0 / 2 := by
  simp only [LFunction_def_even hΦ, neg_zero, cpow_zero, hurwitzZetaEven_apply_zero,
    toAddCircle_eq_zero, mul_ite, mul_div, mul_neg_one, mul_zero, sum_ite_eq', Finset.mem_univ,
    ↓reduceIte, one_mul]

/-- The L-function of an even function vanishes at negative even integers. -/
/-
**ZMod.LFunction_neg_two_mul_nat_add_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {Φ : ZMod N → ℂ}, Function.Even Φ → ∀ (n : ℕ),
 ZMod.LFunction Φ (-(2 * (↑n + 1))) = 0
参数：n : ℕ；-(2 * (↑n + 1))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `ZMod.LFunction.congr_simp`：∀ {N : ℕ} [inst : NeZero N] (Φ Φ_1 : ZMod N →
 ℂ),   Φ = Φ_1 → ∀ (s s_1 : ℂ), s = s_1 → ZMod.LFunction Φ s = ZMod.LFunction Φ_
1 s_1
· 使用引理 `ZMod.LFunction_def_even`：LFunction_def_even (hΦ : Φ.Even) (s : Complex) 
: LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j)
 s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `HurwitzZeta.hurwitzZetaEven_neg_two_mul_nat_add_one`：hurwitzZetaEven_neg
_two_mul_nat_add_one (a : UnitAddCircle) (n : Nat) : hurwitzZetaEven a (-2 * (n 
+ 1)) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The L-function of an even function vanishes at negative even integers.
-/
@[simp] lemma LFunction_neg_two_mul_nat_add_one (hΦ : Φ.Even) (n : ℕ) :
    LFunction Φ (-(2 * (n + 1))) = 0 := by
  simp only [LFunction_def_even hΦ, hurwitzZetaEven_neg_two_mul_nat_add_one, mul_zero,
    sum_const_zero, ← neg_mul]

/-- The L-function of an odd function vanishes at negative odd integers. -/
/-
**ZMod.LFunction_neg_two_mul_nat_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {Φ : ZMod N → ℂ}, Function.Odd Φ → ∀ (n : ℕ), 
ZMod.LFunction Φ (-(2 * ↑n) - 1) = 0
参数：n : ℕ；-(2 * ↑n) - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `ZMod.LFunction.congr_simp`：∀ {N : ℕ} [inst : NeZero N] (Φ Φ_1 : ZMod N →
 ℂ),   Φ = Φ_1 → ∀ (s s_1 : ℂ), s = s_1 → ZMod.LFunction Φ s = ZMod.LFunction Φ_
1 s_1
· 使用引理 `ZMod.LFunction_def_odd`：LFunction_def_odd (hΦ : Φ.Odd) (s : Complex) : L
Function Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `HurwitzZeta.hurwitzZetaOdd_neg_two_mul_nat_sub_one`：hurwitzZetaOdd_neg_t
wo_mul_nat_sub_one (a : UnitAddCircle) (n : Nat) : hurwitzZetaOdd a (-2 * n - 1)
 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The L-function of an odd function vanishes at negative odd integers.
-/
@[simp] lemma LFunction_neg_two_mul_nat_sub_one (hΦ : Φ.Odd) (n : ℕ) :
    LFunction Φ (-(2 * n) - 1) = 0 := by
  simp only [LFunction_def_odd hΦ, hurwitzZetaOdd_neg_two_mul_nat_sub_one, mul_zero, ← neg_mul,
    sum_const_zero]

/--
The completed L-function of a function `Φ : ZMod N → ℂ`.

This is only mathematically meaningful if `Φ` is either even, or odd; here we extend this to all `Φ`
by linearity.
-/
/-
**ZMod.completedLFunction** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：completedLFunction (Φ : ZMod N -> Complex) (s : Complex) : Complex
参数：Φ : ZMod N -> Complex；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completed L-function of a function `Φ : ZMod N → ℂ`.

This is only mathematically meaningful if `Φ` is either even, or odd; here we ex
tend this to all `Φ`
by linearity.
-/
noncomputable def completedLFunction (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s
  + N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s
/-
**ZMod.completedLFunction_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] (s : ℂ), ZMod.completedLFunction 0 s = 0
参数：s : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma completedLFunction_zero (s : ℂ) : completedLFunction (0 : ZMod N → ℂ) s = 0 := by
  simp only [completedLFunction, Pi.zero_apply, zero_mul, sum_const_zero, mul_zero, zero_add]
/-
**ZMod.completedLFunction_const_mul** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：completedLFunction_const_mul (a : Complex) (Φ : ZMod N -> Complex) (s : Co
mplex) : completedLFunction (fun j => a * Φ j) s = a * completedLFunction Φ s
参数：a : Complex；Φ : ZMod N -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
lemma completedLFunction_const_mul (a : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    completedLFunction (fun j ↦ a * Φ j) s = a * completedLFunction Φ s := by
  simp only [completedLFunction, mul_add, mul_sum]
  congr with i <;> ring
/-
**ZMod.completedLFunction_def_even** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：completedLFunction_def_even (hΦ : Φ.Even) (s : Complex) : completedLFuncti
on Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s
参数：hΦ : Φ.Even；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Function.Odd.sum_eq_zero`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCom
mGroup β] [IsAddTorsionFree β] [inst_2 : Fintype α]   [inst_3 : InvolutiveNeg α]
 {f : α → β}, …
· 使用定理 `Function.Even.mul_odd`：∀ {α : Type u_1} [inst : Neg α] {R : Type u_3} [i
nst_1 : Mul R] {f g : α → R} [inst_2 : HasDistribNeg R],   Function.Even f → Fun
ction.Odd g…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `HurwitzZeta.completedHurwitzZetaOdd_neg`：completedHurwitzZetaOdd_neg (a 
: UnitAddCircle) (s : Complex) : completedHurwitzZetaOdd (-a) s = -completedHurw
itzZetaOdd a s
· 使用定理 `ZMod.completedLFunction.eq_1`：∀ {N : ℕ} [inst : NeZero N] (Φ : ZMod N → 
ℂ) (s : ℂ),   ZMod.completedLFunction Φ s =     ↑N ^ (-s) * ∑ j, Φ j * HurwitzZe
ta.completedHurwit…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma completedLFunction_def_even (hΦ : Φ.Even) (s : ℂ) :
    completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s := by
  suffices ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s = 0 by
    rw [completedLFunction, this, mul_zero, add_zero]
  refine (hΦ.mul_odd fun j ↦ ?_).sum_eq_zero
  rw [map_neg, completedHurwitzZetaOdd_neg]
/-
**ZMod.completedLFunction_def_odd** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：completedLFunction_def_odd (hΦ : Φ.Odd) (s : Complex) : completedLFunction
 Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s
参数：hΦ : Φ.Odd；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Function.Odd.sum_eq_zero`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCom
mGroup β] [IsAddTorsionFree β] [inst_2 : Fintype α]   [inst_3 : InvolutiveNeg α]
 {f : α → β}, …
· 使用定理 `Function.Odd.mul_even`：∀ {α : Type u_1} [inst : Neg α] {R : Type u_3} [i
nst_1 : Mul R] {f g : α → R} [inst_2 : HasDistribNeg R],   Function.Odd f → Func
tion.Even g…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_neg`：completedHurwitzZetaEven_neg (
a : UnitAddCircle) (s : Complex) : completedHurwitzZetaEven (-a) s = completedHu
rwitzZetaEven a s
· 使用定理 `ZMod.completedLFunction.eq_1`：∀ {N : ℕ} [inst : NeZero N] (Φ : ZMod N → 
ℂ) (s : ℂ),   ZMod.completedLFunction Φ s =     ↑N ^ (-s) * ∑ j, Φ j * HurwitzZe
ta.completedHurwit…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma completedLFunction_def_odd (hΦ : Φ.Odd) (s : ℂ) :
    completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s := by
  suffices ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s = 0 by
    rw [completedLFunction, this, mul_zero, zero_add]
  refine (hΦ.mul_even fun j ↦ ?_).sum_eq_zero
  rw [map_neg, completedHurwitzZetaEven_neg]

/--
The completed L-function of a function `ZMod 1 → ℂ` is a scalar multiple of the completed Riemann
zeta function.
-/
/-
**ZMod.completedLFunction_modOne_eq** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：completedLFunction_modOne_eq (Φ : ZMod 1 -> Complex) (s : Complex) : compl
etedLFunction Φ s = Φ 1 * completedRiemannZeta s
参数：Φ : ZMod 1 -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZMod.completedLFunction_def_even`：completedLFunction_def_even (hΦ : Φ.Ev
en) (s : Complex) : completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurw
itzZetaEven (toAddCirc…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.one_cpow`：one_cpow (x : Complex) : (1 : Complex) ^ x = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.singleton_eq_univ`：singleton_eq_univ [Subsingleton α] (a : α) : (
{a} : Finset α) = univ
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_zero`：HurwitzZeta.completedHurwitzZ
etaEven_zero (s : Complex) : completedHurwitzZetaEven 0 s = completedRiemannZeta
 s

--- 原说明 ---
The completed L-function of a function `ZMod 1 → ℂ` is a scalar multiple of the 
completed Riemann
zeta function.
-/
lemma completedLFunction_modOne_eq (Φ : ZMod 1 → ℂ) (s : ℂ) :
    completedLFunction Φ s = Φ 1 * completedRiemannZeta s := by
  rw [completedLFunction_def_even (show Φ.Even from fun _ ↦ congr_arg Φ (Subsingleton.elim ..)),
    Nat.cast_one, one_cpow, one_mul, ← singleton_eq_univ 0, sum_singleton, map_zero,
    completedHurwitzZetaEven_zero, Subsingleton.elim 0 1]

/--
The completed L-function of a function `ZMod N → ℂ`, modified by adding multiples of `N ^ (-s) / s`
and `N ^ (-s) / (1 - s)` to make it entire.
-/
/-
**ZMod.completedLFunction** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：completedLFunction (Φ : ZMod N -> Complex) (s : Complex) : Complex
参数：Φ : ZMod N -> Complex；s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completed L-function of a function `ZMod N → ℂ`, modified by adding multiple
s of `N ^ (-s) / s`
and `N ^ (-s) / (1 - s)` to make it entire.
-/
noncomputable def completedLFunction₀ (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s
  + N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

/-- The function `completedLFunction₀ Φ` is differentiable. -/
/-
**ZMod.differentiable_completedLFunction** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：differentiable_completedLFunction (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0) : D
ifferentiable Complex (completedLFunction Φ)
参数：hΦ₂ : Φ 0 = 0；hΦ₃ : ∑ j, Φ j = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ZMod.differentiableAt_completedLFunction`：differentiableAt_completedLFun
ction (Φ : ZMod N -> Complex) (s : Complex) (hs₀ : s != 0 ∨ Φ 0 = 0) (hs₁ : s !=
 1 ∨ ∑ j, Φ j = 0) : Different…

--- 原说明 ---
The function `completedLFunction₀ Φ` is differentiable.
-/
lemma differentiable_completedLFunction₀ (Φ : ZMod N → ℂ) :
    Differentiable ℂ (completedLFunction₀ Φ) := by
  refine .add ?_ ?_ <;>
  refine .mul (by fun_prop) (.fun_sum fun i _ ↦ .const_mul ?_ _)
  exacts [differentiable_completedHurwitzZetaEven₀ _, differentiable_completedHurwitzZetaOdd _]
/-
**ZMod.completedLFunction_eq** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：completedLFunction_eq (Φ : ZMod N -> Complex) (s : Complex) : completedLFu
nction Φ s = completedLFunction₀ Φ s - N ^ (-s) * Φ 0 / s - N ^ (-s) * (∑ j, Φ j
) / (1 - s)
参数：Φ : ZMod N -> Complex；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `HurwitzZeta.completedHurwitzZetaEven_eq`：completedHurwitzZetaEven_eq (a 
: UnitAddCircle) (s : Complex) : completedHurwitzZetaEven a s = completedHurwitz
ZetaEven₀ a s - (if a = 0 the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Fintype.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι)   (f : ι → M), (∑ j,
 if j = i…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.ZMod.0.ZMod.completedLFunction_eq.
_abel_1_5`：∀ {N : ℕ} [inst : NeZero N] (Φ : ZMod N → ℂ) (s : ℂ),   ↑N ^ (-s) * ∑
 x, Φ x * HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle x) s …
-/
lemma completedLFunction_eq (Φ : ZMod N → ℂ) (s : ℂ) :
    completedLFunction Φ s =
      completedLFunction₀ Φ s - N ^ (-s) * Φ 0 / s - N ^ (-s) * (∑ j, Φ j) / (1 - s) := by
  simp only [completedLFunction, completedHurwitzZetaEven_eq, toAddCircle_eq_zero, div_eq_mul_inv,
    ite_mul, one_mul, zero_mul, mul_sub, mul_ite, mul_zero, sum_sub_distrib, Fintype.sum_ite_eq',
    ← sum_mul, completedLFunction₀, mul_assoc]
  abel

/--
The completed L-function of a function `ZMod N → ℂ` is differentiable, with the following
exceptions: at `s = 1` if `∑ j, Φ j ≠ 0`; and at `s = 0` if `Φ 0 ≠ 0`.
-/
/-
**ZMod.differentiableAt_completedLFunction** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：differentiableAt_completedLFunction (Φ : ZMod N -> Complex) (s : Complex) 
(hs₀ : s != 0 ∨ Φ 0 = 0) (hs₁ : s != 1 ∨ ∑ j, Φ j = 0) : DifferentiableAt Comple
x (completedLFunction Φ) s
参数：Φ : ZMod N -> Complex；s : Complex；hs₀ : s != 0 ∨ Φ 0 = 0；hs₁ : s != 1 ∨ ∑ j, 
Φ j = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ZMod.completedLFunction_eq`：completedLFunction_eq (Φ : ZMod N -> Complex
) (s : Complex) : completedLFunction Φ s = completedLFunction₀ Φ s - N ^ (-s) * 
Φ 0 / s - N ^ (-…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `DifferentiableAt.sub`：DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x)
 (hg : DifferentiableAt 𝕜 g x) : DifferentiableAt 𝕜 (f - g) x
· 使用引理 `ZMod.differentiable_completedLFunction₀`：differentiable_completedLFuncti
on₀ (Φ : ZMod N -> Complex) : Differentiable Complex (completedLFunction₀ Φ)
· 使用定理 `DifferentiableAt.mul`：DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x)
 (hb : DifferentiableAt 𝕜 b x) : DifferentiableAt 𝕜 (a * b) x
· 使用定理 `DifferentiableAt.fun_comp'`：DifferentiableAt.fun_comp' {f : E -> F} {g :
 F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : Diffe
rentiableAt 𝕜 (f…
· 使用引理 `differentiableAt_const_cpow_of_neZero`：differentiableAt_const_cpow_of_ne
Zero (z : Complex) [NeZero z] (t : Complex) : DifferentiableAt Complex (fun s : 
Complex => z ^ s) t
· 使用定理 `DifferentiableAt.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {F : Type u_…
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `DifferentiableAt.div`：DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x)
 (hd : DifferentiableAt 𝕜 d x) (hx : d x != 0) : DifferentiableAt 𝕜 (c / d) x
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `DifferentiableAt.const_sub`：DifferentiableAt.const_sub (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => c - f y) x
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
The completed L-function of a function `ZMod N → ℂ` is differentiable, with the 
following
exceptions: at `s = 1` if `∑ j, Φ j ≠ 0`; and at `s = 0` if `Φ 0 ≠ 0`.
-/
lemma differentiableAt_completedLFunction (Φ : ZMod N → ℂ) (s : ℂ) (hs₀ : s ≠ 0 ∨ Φ 0 = 0)
    (hs₁ : s ≠ 1 ∨ ∑ j, Φ j = 0) : DifferentiableAt ℂ (completedLFunction Φ) s := by
  simp only [funext (completedLFunction_eq Φ), mul_div_assoc]
  -- We know `completedLFunction₀` is differentiable everywhere, so it suffices to show that the
  -- correction terms from `completedLFunction_eq` are differentiable at `s`.
  refine ((differentiable_completedLFunction₀ _ _).sub ?_).sub ?_
  · -- term with `1 / s`
    refine .mul (by fun_prop) (hs₀.elim ?_ ?_)
    · exact fun h ↦ (differentiableAt_const _).div differentiableAt_id h
    · exact fun h ↦ by simp only [h, funext zero_div, differentiableAt_const]
  · -- term with `1 / (1 - s)`
    refine .mul (by fun_prop) (hs₁.elim ?_ ?_)
    · exact fun h ↦ .div (by fun_prop) (by fun_prop) (by rwa [sub_ne_zero, ne_comm])
    · exact fun h ↦ by simp only [h, zero_div, differentiableAt_const]

/--
Special case of `differentiableAt_completedLFunction` asserting differentiability everywhere
under suitable hypotheses.
-/
/-
**ZMod.differentiable_completedLFunction** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：differentiable_completedLFunction (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0) : D
ifferentiable Complex (completedLFunction Φ)
参数：hΦ₂ : Φ 0 = 0；hΦ₃ : ∑ j, Φ j = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ZMod.differentiableAt_completedLFunction`：differentiableAt_completedLFun
ction (Φ : ZMod N -> Complex) (s : Complex) (hs₀ : s != 0 ∨ Φ 0 = 0) (hs₁ : s !=
 1 ∨ ∑ j, Φ j = 0) : Different…

--- 原说明 ---
Special case of `differentiableAt_completedLFunction` asserting differentiabilit
y everywhere
under suitable hypotheses.
-/
lemma differentiable_completedLFunction (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0) :
    Differentiable ℂ (completedLFunction Φ) :=
  fun s ↦ differentiableAt_completedLFunction Φ s (.inr hΦ₂) (.inr hΦ₃)

/--
Relation between the completed L-function and the usual one (even case).
We state it this way around so it holds at the poles of the gamma factor as well
(except at `s = 0`, where it is genuinely false if `N > 1` and `Φ 0 ≠ 0`).
-/
/-
**ZMod.LFunction_eq_completed_div_gammaFactor_even** 是 Mathlib 中的一个引理，位于命名空间 `ZM
od`。
形式化陈述：LFunction_eq_completed_div_gammaFactor_even (hΦ : Φ.Even) (s : Complex) (h
s : s != 0 ∨ Φ 0 = 0) : LFunction Φ s = completedLFunction Φ s / GammaReal s
参数：hΦ : Φ.Even；s : Complex；hs : s != 0 ∨ Φ 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZMod.LFunction_def_even`：LFunction_def_even (hΦ : Φ.Even) (s : Complex) 
: LFunction Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j)
 s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ZMod.completedLFunction_def_even`：completedLFunction_def_even (hΦ : Φ.Ev
en) (s : Complex) : completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurw
itzZetaEven (toAddCirc…
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用引理 `Finset.sum_div`：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ 
i in s, f i) / a = ∑ i in s, f i / a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用引理 `HurwitzZeta.hurwitzZetaEven_def_of_ne_or_ne`：hurwitzZetaEven_def_of_ne_o
r_ne {a : UnitAddCircle} {s : Complex} (h : a != 0 ∨ s != 0) : hurwitzZetaEven a
 s = completedHurwitzZetaEven a s…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ZMod.toAddCircle_eq_zero`：∀ {N : ℕ} [inst : NeZero N] {j : ZMod N}, ZMod
.toAddCircle j = 0 ↔ j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Relation between the completed L-function and the usual one (even case).
We state it this way around so it holds at the poles of the gamma factor as well
(except at `s = 0`, where it is genuinely false if `N > 1` and `Φ 0 ≠ 0`).
-/
lemma LFunction_eq_completed_div_gammaFactor_even (hΦ : Φ.Even) (s : ℂ) (hs : s ≠ 0 ∨ Φ 0 = 0) :
    LFunction Φ s = completedLFunction Φ s / Gammaℝ s := by
  simp only [completedLFunction_def_even hΦ, LFunction_def_even hΦ, mul_div_assoc, sum_div]
  congr 2 with i
  rcases ne_or_eq i 0 with hi | rfl
  · rw [hurwitzZetaEven_def_of_ne_or_ne (.inl (hi ∘ toAddCircle_eq_zero.mp))]
  · rcases hs with hs | hΦ'
    · rw [hurwitzZetaEven_def_of_ne_or_ne (.inr hs)]
    · simp only [hΦ', map_zero, zero_mul]

/--
Relation between the completed L-function and the usual one (odd case).
We state it this way around so it holds at the poles of the gamma factor as well.
-/
/-
**ZMod.LFunction_eq_completed_div_gammaFactor_odd** 是 Mathlib 中的一个引理，位于命名空间 `ZMo
d`。
形式化陈述：LFunction_eq_completed_div_gammaFactor_odd (hΦ : Φ.Odd) (s : Complex) : LF
unction Φ s = completedLFunction Φ s / GammaReal (s + 1)
参数：hΦ : Φ.Odd；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZMod.LFunction_def_odd`：LFunction_def_odd (hΦ : Φ.Odd) (s : Complex) : L
Function Φ s = N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ZMod.completedLFunction_def_odd`：completedLFunction_def_odd (hΦ : Φ.Odd)
 (s : Complex) : completedLFunction Φ s = N ^ (-s) * ∑ j, Φ j * completedHurwitz
ZetaOdd (toAddCircle …
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用引理 `Finset.sum_div`：Finset.sum_div (s : Finset ι) (f : ι -> K) (a : K) : (∑ 
i in s, f i) / a = ∑ i in s, f i / a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Relation between the completed L-function and the usual one (odd case).
We state it this way around so it holds at the poles of the gamma factor as well
.
-/
lemma LFunction_eq_completed_div_gammaFactor_odd (hΦ : Φ.Odd) (s : ℂ) :
    LFunction Φ s = completedLFunction Φ s / Gammaℝ (s + 1) := by
  simp only [LFunction_def_odd hΦ, completedLFunction_def_odd hΦ, hurwitzZetaOdd, mul_div_assoc,
    sum_div]

/--
First form of functional equation for completed L-functions (even case).

Private because it is superseded by `completedLFunction_one_sub_even` below, which is valid for a
much wider range of `s`.
-/
/-
**ZMod.completedLFunction_one_sub_of_one_lt_even** 是 Mathlib 中的一个引理，位于命名空间 `ZMod
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
First form of functional equation for completed L-functions (even case).

Private because it is superseded by `completedLFunction_one_sub_even` below, whi
ch is valid for a
much wider range of `s`.
-/
private lemma completedLFunction_one_sub_of_one_lt_even (hΦ : Φ.Even) {s : ℂ} (hs : 1 < re s) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * completedLFunction (𝓕 Φ) s := by
  have hs₀ : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hs₁ : s ≠ 1 := (lt_irrefl _ <| one_re ▸ · ▸ hs)
  -- strip down to the key equality:
  suffices ∑ x, Φ x * completedCosZeta (toAddCircle x) s = completedLFunction (𝓕 Φ) s by
    simp only [completedLFunction_def_even hΦ, neg_sub, completedHurwitzZetaEven_one_sub, this]
  -- reduce to equality with un-completed L-functions:
  suffices ∑ x, Φ x * cosZeta (toAddCircle x) s = LFunction (𝓕 Φ) s by
    simpa only [cosZeta, Function.update_of_ne hs₀, ← mul_div_assoc, ← sum_div,
      LFunction_eq_completed_div_gammaFactor_even (dft_even_iff.mpr hΦ) _ (.inl hs₀),
      div_left_inj' (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs))]
  -- expand out `LFunction (𝓕 Φ)` and use parity:
  simp only [cosZeta_eq, ← mul_div_assoc _ _ (2 : ℂ), mul_add, ← sum_div, sum_add_distrib,
    LFunction_dft Φ (.inr hs₁), map_neg, div_eq_iff (two_ne_zero' ℂ), mul_two, add_left_inj]
  exact Fintype.sum_equiv (.neg _) _ _ (by simp [hΦ _])

/--
First form of functional equation for completed L-functions (odd case).

Private because it is superseded by `completedLFunction_one_sub_odd` below, which is valid for a
much wider range of `s`.
-/
/-
**ZMod.completedLFunction_one_sub_of_one_lt_odd** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
First form of functional equation for completed L-functions (odd case).

Private because it is superseded by `completedLFunction_one_sub_odd` below, whic
h is valid for a
much wider range of `s`.
-/
private lemma completedLFunction_one_sub_of_one_lt_odd (hΦ : Φ.Odd) {s : ℂ} (hs : 1 < re s) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s := by
  -- strip down to the key equality:
  suffices ∑ x, Φ x * completedSinZeta (toAddCircle x) s = I * completedLFunction (𝓕 Φ) s by
    simp only [completedLFunction_def_odd hΦ, neg_sub, completedHurwitzZetaOdd_one_sub, this,
      mul_assoc]
  -- reduce to equality with un-completed L-functions:
  suffices ∑ x, Φ x * sinZeta (toAddCircle x) s = I * LFunction (𝓕 Φ) s by
    have hs' : 0 < re (s + 1) := by simp only [add_re, one_re]; linarith
    simpa only [sinZeta, ← mul_div_assoc, ← sum_div, div_left_inj' (Gammaℝ_ne_zero_of_re_pos hs'),
      LFunction_eq_completed_div_gammaFactor_odd (dft_odd_iff.mpr hΦ)]
  -- now calculate:
  calc ∑ x, Φ x * sinZeta (toAddCircle x) s
  _ = (∑ x, Φ x * expZeta (toAddCircle x) s) / (2 * I)
      - (∑ x, Φ x * expZeta (toAddCircle (-x)) s) / (2 * I) := by
    simp only [sinZeta_eq, ← mul_div_assoc, mul_sub, sub_div, sum_sub_distrib, sum_div, map_neg]
  _ = (∑ x, Φ (-x) * expZeta (toAddCircle (-x)) s) / (_) - (_) := by
    congrm ?_ / _ - _
    exact (Fintype.sum_equiv (.neg _) _ _ fun x ↦ by rfl).symm
  _ = -I⁻¹ * LFunction (𝓕 Φ) s := by
    simp only [hΦ _, neg_mul, sum_neg_distrib, LFunction_dft Φ (.inl hΦ.map_zero)]
    ring
  _ = I * LFunction (𝓕 Φ) s := by rw [inv_I, neg_neg]

/--
Functional equation for completed L-functions (even case), valid at all points of differentiability.
-/
/-
**ZMod.completedLFunction_one_sub_even** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：completedLFunction_one_sub_even (hΦ : Φ.Even) (s : Complex) (hs₀ : s != 0 
∨ ∑ j, Φ j = 0) (hs₁ : s != 1 ∨ Φ 0 = 0) : completedLFunction Φ (1 - s) = N ^ (s
 - 1) * completedLFunction (𝓕 Φ) s
参数：hΦ : Φ.Even；s : Complex；hs₀ : s != 0 ∨ ∑ j, Φ j = 0；hs₁ : s != 1 ∨ Φ 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `OfNat.ofNat_ne_one`：∀ {R : Type u_1} [inst : AddMonoidWithOne R] [CharZe
ro R] (n : ℕ) [inst_2 : n.AtLeastTwo], OfNat.ofNat n ≠ 1
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `isOpen_const`：isOpen_const {p : Prop} : IsOpen { _x : X | p }
· 使用定理 `Set.Countable.union`：∀ {α : Type u} {s t : Set α}, s.Countable → t.Count
able → (s ∪ t).Countable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
Functional equation for completed L-functions (even case), valid at all points o
f differentiability.
-/
theorem completedLFunction_one_sub_even (hΦ : Φ.Even) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ ∑ j, Φ j = 0) (hs₁ : s ≠ 1 ∨ Φ 0 = 0) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * completedLFunction (𝓕 Φ) s := by
  -- We prove this using `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, so we need to
  -- gather up the ingredients for this big theorem.
  -- First set up some notations:
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * completedLFunction (𝓕 Φ) t
  -- Set on which F, G are analytic:
  let U := {t : ℂ | (t ≠ 0 ∨ ∑ j, Φ j = 0) ∧ (t ≠ 1 ∨ Φ 0 = 0)}
  -- Properties of U:
  have hsU : s ∈ U := ⟨hs₀, hs₁⟩
  have h2U : 2 ∈ U := ⟨.inl two_ne_zero, .inl (OfNat.ofNat_ne_one _)⟩
  have hUo : IsOpen U := (isOpen_compl_singleton.union isOpen_const).inter
    (isOpen_compl_singleton.union isOpen_const)
  have hUp : IsPreconnected U := by
    -- need to write `U` as the complement of an obviously countable set
    let Uc : Set ℂ := (if ∑ j, Φ j = 0 then ∅ else {0}) ∪ (if Φ 0 = 0 then ∅ else {1})
    have : Uc.Countable := by
      apply Countable.union <;>
      split_ifs <;>
      simp only [countable_singleton, countable_empty]
    convert! (this.isConnected_compl_of_one_lt_rank ?_).isPreconnected using 1
    · ext x
      by_cases h : Φ 0 = 0 <;>
      by_cases h' : ∑ j, Φ j = 0 <;>
      simp [U, Uc, h, h', and_comm]
    · simp only [rank_real_complex, Nat.one_lt_ofNat]
  -- Analyticity on U:
  have hF : AnalyticOnNhd ℂ F U := by
    refine DifferentiableOn.analyticOnNhd
      (fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_) hUo
    refine (differentiableAt_completedLFunction Φ _ ?_ ?_).comp t (differentiableAt_id.const_sub 1)
    exacts [ht.2.imp_left (sub_ne_zero.mpr ∘ Ne.symm), ht.1.imp_left sub_eq_self.not.mpr]
  have hG : AnalyticOnNhd ℂ G U := by
    refine DifferentiableOn.analyticOnNhd
      (fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_) hUo
    apply ((differentiableAt_id.sub_const 1).const_cpow (.inl (NeZero.ne _))).mul
    apply differentiableAt_completedLFunction _ _ (ht.1.imp_right fun h ↦ dft_apply_zero Φ ▸ h)
    exact ht.2.imp_right (fun h ↦ by simp only [← dft_apply_zero, dft_dft, neg_zero, h, smul_zero])
  -- set where we know equality
  have hV : {z | 1 < re z} ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hFG : F =ᶠ[𝓝 2] G := eventually_of_mem hV <| fun t ht ↦ by
    simpa only [F, G, pow_zero, mul_one] using completedLFunction_one_sub_of_one_lt_even hΦ ht
  -- now apply the big hammer to finish
  exact hF.eqOn_of_preconnected_of_eventuallyEq hG hUp h2U hFG hsU

/-- Functional equation for completed L-functions (odd case), valid for all `s`. -/
/-
**ZMod.completedLFunction_one_sub_odd** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：completedLFunction_one_sub_odd (hΦ : Φ.Odd) (s : Complex) : completedLFunc
tion Φ (1 - s) = N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s
参数：hΦ : Φ.Odd；s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Differentiable.comp`：Differentiable.comp {g : F -> G} (hg : Differentiab
le 𝕜 g) (hf : Differentiable 𝕜 f) : Differentiable 𝕜 (g ∘ f)
· 使用引理 `ZMod.differentiable_completedLFunction`：differentiable_completedLFunctio
n (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0) : Differentiable Complex (completedLFunct
ion Φ)
· 使用定理 `Function.Odd.map_zero`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommGr
oup β] [IsAddTorsionFree β] {f : α → β} [inst_2 : NegZeroClass α],   Function.Od
d f → f 0 =…
· 使用定理 `Function.Odd.sum_eq_zero`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCom
mGroup β] [IsAddTorsionFree β] [inst_2 : Fintype α]   [inst_3 : InvolutiveNeg α]
 {f : α → β}, …
· 使用定理 `Differentiable.const_sub`：Differentiable.const_sub (hf : Differentiable 
𝕜 f) (c : F) : Differentiable 𝕜 fun y => c - f y
· 使用定理 `differentiable_id`：differentiable_id : Differentiable 𝕜 (id : E -> E)
· 使用定理 `Differentiable.mul`：Differentiable.mul (ha : Differentiable 𝕜 a) (hb : D
ifferentiable 𝕜 b) : Differentiable 𝕜 (a * b)
· 使用定理 `Differentiable.mul_const`：Differentiable.mul_const (ha : Differentiable 
𝕜 a) (b : 𝔸) : Differentiable 𝕜 fun y => a y * b
· 使用定理 `Differentiable.const_cpow`：Differentiable.const_cpow (hf : Differentiabl
e Complex f) (h0 : c != 0 ∨ forall x, f x != 0) : Differentiable Complex (fun x 
=> c ^ f x)
· 使用定理 `Differentiable.sub_const`：Differentiable.sub_const (hf : Differentiable 
𝕜 f) (c : F) : Differentiable 𝕜 fun y => f y - c
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.dft_odd_iff`：∀ {N : ℕ} [inst : NeZero N] {Φ : ZMod N → ℂ}, Function
.Odd (ZMod.dft Φ) ↔ Function.Odd Φ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.ZMod.0.ZMod.completedLFunction_one
_sub_of_one_lt_odd`：∀ {N : ℕ} [inst : NeZero N] {Φ : ZMod N → ℂ},   Function.Odd
 Φ →     ∀ {s : ℂ},       1 < s.re → ZMod.completedLFunction Φ (1 - s) = ↑N ^ (s
…
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Functional equation for completed L-functions (odd case), valid for all `s`.
-/
theorem completedLFunction_one_sub_odd (hΦ : Φ.Odd) (s : ℂ) :
    completedLFunction Φ (1 - s) = N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s := by
  -- This is much easier than the even case since both functions are entire.
  -- First set up some notations:
  let F (t) := completedLFunction Φ (1 - t)
  let G (t) := ↑N ^ (t - 1) * I * completedLFunction (𝓕 Φ) t
  -- check F, G globally differentiable
  have hF : Differentiable ℂ F := (differentiable_completedLFunction hΦ.map_zero
    hΦ.sum_eq_zero).comp (differentiable_id.const_sub 1)
  have hG : Differentiable ℂ G := by
    apply (((differentiable_id.sub_const 1).const_cpow (.inl (NeZero.ne _))).mul_const _).mul
    rw [← dft_odd_iff] at hΦ
    exact differentiable_completedLFunction hΦ.map_zero hΦ.sum_eq_zero
  -- set where we know equality
  have : {z | 1 < re z} ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hFG : F =ᶠ[𝓝 2] G := by filter_upwards [this] with t ht
    using completedLFunction_one_sub_of_one_lt_odd hΦ ht
  -- now apply the big hammer to finish
  rw [← analyticOnNhd_univ_iff_differentiable] at hF hG
  exact congr_fun (hF.eq_of_eventuallyEq hG hFG) s

end signed

end ZMod

