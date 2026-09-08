/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Bounds
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# smoothingSeminorm

In this file, we prove [BGR, Proposition 1.3.2/1][bosch-guntzer-remmert]: if `μ` is a
nonarchimedean seminorm on a commutative ring `R`, then
`iInf (fun (n : PNat), (μ(x ^ (n : ℕ))) ^ (1 / (n : ℝ)))` is a power-multiplicative nonarchimedean
seminorm on `R`.

## Main Definitions
* `smoothingSeminormSeq` : the `ℝ`-valued sequence sending `n` to `((f( (x ^ n)) ^ (1 / n : ℝ)`.
* `smoothingFun` : the iInf of the sequence `n ↦ f(x ^ (n : ℕ))) ^ (1 / (n : ℝ)`.
* `smoothingSeminorm` : if `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun`
  is a ring seminorm.

## Main Results

* `tendsto_smoothingFun_of_map_one_le_one` : if `μ 1 ≤ 1`, then `smoothingFun μ x` is the limit
  of `smoothingSeminormSeq μ x` as `n` tends to infinity.
* `isNonarchimedean_smoothingFun` : if `μ 1 ≤ 1` and `μ` is nonarchimedean, then
  `smoothingFun` is nonarchimedean.
* `isPowMul_smoothingFun` : if `μ 1 ≤ 1` and `μ` is nonarchimedean, then
  `smoothingFun μ` is power-multiplicative.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

smoothingSeminorm, seminorm, nonarchimedean
-/

@[expose] public section

noncomputable section

open Filter Nat Real

open scoped Topology NNReal

variable {R : Type*} [CommRing R] (μ : RingSeminorm R)

section smoothingSeminorm

/-- The `ℝ`-valued sequence sending `n` to `(μ (x ^ n))^(1/n : ℝ)`. -/
/-
**smoothingSeminormSeq** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：smoothingSeminormSeq (x : R) : Nat -> Real
参数：x : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ℝ`-valued sequence sending `n` to `(μ (x ^ n))^(1/n : ℝ)`.
-/
abbrev smoothingSeminormSeq (x : R) : ℕ → ℝ := fun n => μ (x ^ n) ^ (1 / n : ℝ)

/-- For any positive `ε`, there exists a positive natural number `m` such that
  `μ (x ^ (m : ℕ)) ^ (1 / m : ℝ) < iInf (fun (n : PNat), (μ(x ^(n : ℕ)))^(1/(n : ℝ))) + ε/2`. -/
/-
**smoothingSeminormSeq_exists_pnat** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any positive `ε`, there exists a positive natural number `m` such that
  `μ (x ^ (m : ℕ)) ^ (1 / m : ℝ) < iInf (fun (n : PNat), (μ(x ^(n : ℕ)))^(1/(n :
 ℝ))) + ε/2`.
-/
private theorem smoothingSeminormSeq_exists_pnat (x : R) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : PNat, μ (x ^ (m : ℕ)) ^ (1 / m : ℝ) <
        (iInf fun n : PNat => μ (x ^ (n : ℕ)) ^ (1 / (n : ℝ))) + ε / 2 :=
  exists_lt_of_ciInf_lt (lt_add_of_le_of_pos (le_refl _) (half_pos hε))
/-
**smoothingSeminormSeq_tendsto_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem smoothingSeminormSeq_tendsto_aux {L : ℝ} (hL : 0 ≤ L) {ε : ℝ} (hε : 0 < ε)
    {m1 : ℕ} (hm1 : 0 < m1) {x : R} (hx : μ x ≠ 0) :
    Tendsto
      (fun n : ℕ => (L + ε) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) * (μ x ^ (n % m1)) ^ (1 / (n : ℝ)))
      atTop (𝓝 1) := by
  rw [← mul_one (1 : ℝ)]
  have h_exp : Tendsto (fun n : ℕ => ((n % m1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_mod_div_atTop_nhds_zero_nat hm1
  apply Tendsto.mul
  · have h0 : Tendsto (fun t : ℕ => -(((t % m1 : ℕ) : ℝ) / (t : ℝ))) atTop (𝓝 0) := by
      rw [← neg_zero]
      exact Tendsto.neg h_exp
    rw [← rpow_zero (L + ε)]
    apply Tendsto.rpow tendsto_const_nhds h0
    rw [ne_eq, add_eq_zero_iff_of_nonneg hL (le_of_lt hε)]
    exact Or.inl (not_and_of_not_right _ (ne_of_gt hε))
  · simp_rw [mul_one, ← rpow_natCast, ← rpow_mul (apply_nonneg μ x), ← mul_div_assoc, mul_one,
      ← rpow_zero (μ x)]
    exact Tendsto.rpow tendsto_const_nhds h_exp (Or.inl hx)

/-- `0` is a lower bound of `smoothingSeminormSeq`. -/
/-
**zero_mem_lowerBounds_smoothingSeminormSeq_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_mem_lowerBounds_smoothingSeminormSeq_range (x : R) : 0 in lowerBounds
 (Set.range fun n : Nat+ => μ (x ^ (n : Nat)) ^ (1 / (n : Real)))
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…

--- 原说明 ---
`0` is a lower bound of `smoothingSeminormSeq`.
-/
theorem zero_mem_lowerBounds_smoothingSeminormSeq_range (x : R) :
    0 ∈ lowerBounds (Set.range fun n : ℕ+ => μ (x ^ (n : ℕ)) ^ (1 / (n : ℝ))) := by
  rintro y ⟨n, rfl⟩
  positivity

/-- `smoothingSeminormSeq` is bounded below (by zero). -/
/-
**smoothingSeminormSeq_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingSeminormSeq_bddBelow (x : R) : BddBelow (Set.range fun n : Nat+ =
> μ (x ^ (n : Nat)) ^ (1 / (n : Real)))
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_mem_lowerBounds_smoothingSeminormSeq_range`：zero_mem_lowerBounds_sm
oothingSeminormSeq_range (x : R) : 0 in lowerBounds (Set.range fun n : Nat+ => μ
 (x ^ (n : Nat)) ^ (1 / (n : Real)))

--- 原说明 ---
`smoothingSeminormSeq` is bounded below (by zero).
-/
theorem smoothingSeminormSeq_bddBelow (x : R) :
    BddBelow (Set.range fun n : ℕ+ => μ (x ^ (n : ℕ)) ^ (1 / (n : ℝ))) :=
  ⟨0, zero_mem_lowerBounds_smoothingSeminormSeq_range μ x⟩

/-- The iInf of the sequence `n ↦ μ(x ^ (n : ℕ)))^(1 / (n : ℝ)`. -/
/-
**smoothingFun** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：smoothingFun (x : R) : Real
参数：x : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The iInf of the sequence `n ↦ μ(x ^ (n : ℕ)))^(1 / (n : ℝ)`.
-/
abbrev smoothingFun (x : R) : ℝ :=
  iInf fun n : PNat => μ (x ^ (n : ℕ)) ^ (1 / (n : ℝ))

/-- If `μ x = 0`, then `smoothingFun μ x` is the limit of `smoothingSeminormSeq μ x`. -/
/-
**tendsto_smoothingFun_of_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_smoothingFun_of_eq_zero {x : R} (hx : μ x = 0) : Tendsto (smoothin
gSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x))
参数：hx : μ x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `map_pow_le_pow`：∀ {F : Type u_2} {α : Type u_3} [inst : Ring α] [inst_1 
: FunLike F α ℝ] [RingSeminormClass F α ℝ] (f : F) (a : α)   {n : ℕ}, n ≠ 0 → f 
(a ^…
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `Nat.one_div_cast_ne_zero`：one_div_cast_ne_zero {n : Nat} (hn : n != 0) :
 1 / (n : α) != 0
· 使用定理 `ciInf_le_of_le`：ciInf_le_of_le {f : ι -> α} (H : BddBelow (range f)) (c 
: ι) (h : f c <= a) : iInf f <= a
· 使用定理 `smoothingSeminormSeq_bddBelow`：smoothingSeminormSeq_bddBelow (x : R) : B
ddBelow (Set.range fun n : Nat+ => μ (x ^ (n : Nat)) ^ (1 / (n : Real)))
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)

--- 原说明 ---
If `μ x = 0`, then `smoothingFun μ x` is the limit of `smoothingSeminormSeq μ x`
.
-/
theorem tendsto_smoothingFun_of_eq_zero {x : R} (hx : μ x = 0) :
    Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)) := by
  have h0 (n : ℕ) (hn : 1 ≤ n) : μ (x ^ n) ^ (1 / (n : ℝ)) = 0 := by
    have hμn : μ (x ^ n) = 0 := by
      apply le_antisymm _ (apply_nonneg μ _)
      rw [← zero_pow (pos_iff_ne_zero.mp hn), ← hx]
      exact map_pow_le_pow _ x (one_le_iff_ne_zero.mp hn)
    rw [hμn, zero_rpow (one_div_cast_ne_zero (one_le_iff_ne_zero.mp hn))]
  have hL0 : (iInf fun n : PNat => μ (x ^ (n : ℕ)) ^ (1 / (n : ℝ))) = 0 :=
    le_antisymm
      (ciInf_le_of_le (smoothingSeminormSeq_bddBelow μ x) (1 : PNat) (le_of_eq (h0 1 (le_refl _))))
      (le_ciInf fun n ↦ by positivity)
  simpa only [hL0] using tendsto_atTop_of_eventually_const h0

/-- If `μ 1 ≤ 1` and `μ x ≠ 0`, then `smoothingFun μ x` is the limit of
`smoothingSeminormSeq μ x`. -/
/-
**tendsto_smoothingFun_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_smoothingFun_of_ne_zero (hμ1 : μ 1 <= 1) {x : R} (hx : μ x != 0) :
 Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x))
参数：hμ1 : μ 1 <= 1；hx : μ x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.tendsto_atTop`：tendsto_atTop [Nonempty β] [SemilatticeSup β] {u :
 β -> α} {a : α} : Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N
, dist (u …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm.0.smoothing
SeminormSeq_exists_pnat`：∀ {R : Type u_1} [inst : CommRing R] (μ : RingSeminorm 
R) (x : R) {ε : ℝ},   0 < ε → ∃ m, μ (x ^ ↑m) ^ (1 / ↑↑m) < (⨅ n, μ (x ^ ↑n) ^ (
1 / ↑…
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `_private.Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm.0.smoothing
SeminormSeq_tendsto_aux`：∀ {R : Type u_1} [inst : CommRing R] (μ : RingSeminorm 
R) {L : ℝ},   0 ≤ L →     ∀ {ε : ℝ},       0 < ε →         ∀ {m1 : ℕ},          
 0 < …
· 使用定理 `PNat.pos`：pos (n : Nat+) : 0 < (n : Nat)
· 使用定理 `div_mul_eq_div_mul_one_div`：div_mul_eq_div_mul_one_div : a / (b * c) = a
 / b * (1 / c)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftStrictMono α] {a b : α},   0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 114 条，此处仅展示前 30 条）

--- 原说明 ---
If `μ 1 ≤ 1` and `μ x ≠ 0`, then `smoothingFun μ x` is the limit of
`smoothingSeminormSeq μ x`.
-/
theorem tendsto_smoothingFun_of_ne_zero (hμ1 : μ 1 ≤ 1) {x : R} (hx : μ x ≠ 0) :
    Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)) := by
  let L := iInf fun n : PNat => μ (x ^ (n : ℕ)) ^ (1 / (n : ℝ))
  have hL0 : 0 ≤ L := le_ciInf fun x ↦ by positivity
  rw [Metric.tendsto_atTop]
  intro ε hε
  /- For each `ε > 0`, we can find a positive natural number `m1` such that
  `μ x ^ (1 / m1) < L + ε/2`. -/
  obtain ⟨m1, hm1⟩ := smoothingSeminormSeq_exists_pnat μ x hε
  /- For `n` large enough, we have that
    `(L + ε / 2) ^ (-(n % m1) / n)) * (μ x ^ (n % m1)) ^ (1 / n) - 1 ≤ ε / (2 * (L + ε / 2))`. -/
  obtain ⟨m2, hm2⟩ : ∃ m : ℕ, ∀ n ≥ m,
      (L + ε / 2) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) * (μ x ^ (n % m1)) ^ (1 / (n : ℝ)) - 1 ≤
      ε / (2 * (L + ε / 2)) := by
    have hε2 : 0 < ε / 2 := half_pos hε
    have hL2 := smoothingSeminormSeq_tendsto_aux μ hL0 hε2 (PNat.pos m1) hx
    rw [Metric.tendsto_atTop] at hL2
    set δ : ℝ := ε / (2 * (L + ε / 2)) with hδ_def
    have hδ : 0 < δ := by
      rw [hδ_def, div_mul_eq_div_mul_one_div]
      exact mul_pos hε2
        ((one_div (L + ε / 2)).symm ▸ inv_pos_of_pos (add_pos_of_nonneg_of_pos hL0 hε2))
    obtain ⟨N, hN⟩ := hL2 δ hδ
    use N
    intro n hn
    specialize hN n hn
    rw [Real.dist_eq, abs_lt] at hN
    exact le_of_lt hN.right
  /- We now show that for all `n ≥ max m1 m2`, we have
    `dist (smoothingSeminormSeq μ x n) (smoothingFun μ x) < ε`. -/
  use max (m1 : ℕ) m2
  intro n hn
  have hn0 : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le (PNat.pos m1) (le_max_left (m1 : ℕ) m2)) hn
  rw [Real.dist_eq, abs_lt]
  have hL_le : L ≤ smoothingSeminormSeq μ x n := by
    rw [← PNat.mk_coe n hn0]
    apply ciInf_le (smoothingSeminormSeq_bddBelow μ x)
  refine ⟨lt_of_lt_of_le (neg_lt_zero.mpr hε) (sub_nonneg.mpr hL_le), ?_⟩
  -- It is enough to show that `smoothingSeminormSeq μ x n < L + ε`, that is,
  -- `μ (x ^ n) ^ (1 / ↑n) < L + ε`.
  suffices h : smoothingSeminormSeq μ x n < L + ε by rwa [tsub_lt_iff_left hL_le]
  by_cases hxn : μ (x ^ (n % m1)) = 0
  · /- If `μ (x ^ (n % m1)) = 0`, this reduces to showing that
     `μ (x ^ (↑m1 * (n / ↑m1)) * x ^ (n % ↑m1)) ^ (1 / ↑n) ≤
     (μ (x ^ (↑m1 * (n / ↑m1))) * μ (x ^ (n % ↑m1))) ^ (1 / ↑n)`, which follows from the
     submultiplicativity of `μ`. -/
    simp only [smoothingSeminormSeq]
    nth_rw 1 [← div_add_mod n m1]
    have hLε : 0 < L + ε := add_pos_of_nonneg_of_pos hL0 hε
    apply lt_of_le_of_lt _ hLε
    rw [pow_add, ← MulZeroClass.mul_zero (μ (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) ^ (1 / (n : ℝ))),
      ← zero_rpow (one_div_cast_ne_zero (pos_iff_ne_zero.mp hn0)), ← hxn,
      ← mul_rpow (apply_nonneg μ _) (apply_nonneg μ _)]
    gcongr
    exact map_mul_le_mul μ _ _
  · --Otherwise, we have `0 < μ (x ^ (n % ↑m1))`.
    have hxn' : 0 < μ (x ^ (n % ↑m1)) := lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hxn)
    simp only [smoothingSeminormSeq]
    nth_rw 1 [← div_add_mod n m1]
    /- We use the submultiplicativity of `μ` to deduce
    `μ (x ^ (m1 * (n / m1)) ^ (1 / n) ≤ (μ (x ^ m1) ^ (n / m1)) ^ (1 / n)`. -/
    have h : μ (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) ^ (1 / (n : ℝ)) ≤
        (μ (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ)) := by
      gcongr
      rw [pow_mul]
      exact map_pow_le_pow μ (x ^ (m1 : ℕ))
        (pos_iff_ne_zero.mp (Nat.div_pos (le_trans (le_max_left (m1 : ℕ) m2) hn) (PNat.pos m1)))
    have hL0' : 0 < L + ε / 2 := add_pos_of_nonneg_of_pos hL0 (half_pos hε)
    /- We show that `(μ (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ)) <
        (L + ε / 2) ^ (1 - (((n % m1 : ℕ) : ℝ) / (n : ℝ)))`. -/
    have h1 : (μ (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ)) <
        (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) := by
      have hm10 : (m1 : ℝ) ≠ 0 := cast_ne_zero.mpr (_root_.ne_of_gt (PNat.pos m1))
      rw [← rpow_lt_rpow_iff (rpow_nonneg (apply_nonneg μ _) _) (le_of_lt hL0')
        (cast_pos.mpr (PNat.pos m1)), ← rpow_mul (apply_nonneg μ _), one_div_mul_cancel hm10,
        rpow_one] at hm1
      nth_rw 1 [← rpow_one (L + ε / 2)]
      have : (n : ℝ) / n = (1 : ℝ) := div_self (cast_ne_zero.mpr (_root_.ne_of_gt hn0))
      nth_rw 2 [← this]; clear this
      nth_rw 3 [← div_add_mod n m1]
      have h_lt : 0 < ((n / m1 : ℕ) : ℝ) / (n : ℝ) :=
        div_pos (cast_pos.mpr (Nat.div_pos (le_trans (le_max_left _ _) hn) (PNat.pos m1)))
          (cast_pos.mpr hn0)
      rw [← rpow_natCast, ← rpow_add hL0', ← neg_div, ← add_div, Nat.cast_add,
        add_neg_cancel_right, Nat.cast_mul, ← rpow_mul (apply_nonneg μ _), mul_one_div,
        mul_div_assoc, rpow_mul (le_of_lt hL0')]
      exact rpow_lt_rpow (apply_nonneg μ _) hm1 h_lt
    /- We again use the submultiplicativity of `μ` to deduce
    `μ (x ^ (n % m1)) ^ (1 / n) ≤ (μ x ^ (n % m1)) ^ (1 / n)`. -/
    have h2 : μ (x ^ (n % m1)) ^ (1 / (n : ℝ)) ≤ (μ x ^ (n % m1)) ^ (1 / (n : ℝ)) := by
      by_cases hnm1 : n % m1 = 0
      · simpa [hnm1, pow_zero] using rpow_le_rpow (apply_nonneg μ _) hμ1 (one_div_cast_nonneg _)
      · exact rpow_le_rpow (apply_nonneg μ _) (map_pow_le_pow μ _ hnm1) (one_div_cast_nonneg _)
    /- We bound `(L + ε / 2) ^ (1 -n % m1) / n) * (μ x ^ (n % m1)) ^ (1 / n)` by `L + ε`. -/
    have h3 : (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) *
          (μ x ^ (n % m1)) ^ (1 / (n : ℝ)) ≤ L + ε := by
      have heq : L + ε = L + ε / 2 + ε / 2 := by rw [add_assoc, add_halves]
      rw [heq, ← tsub_le_iff_left]
      nth_rw 3 [← mul_one (L + ε / 2)]
      rw [mul_assoc, ← mul_sub, mul_comm, ← le_div_iff₀ hL0', div_div]
      exact hm2 n (le_trans (le_max_right (m1 : ℕ) m2) hn)
    have h4 : 0 < μ (x ^ (n % ↑m1)) ^ (1 / (n : ℝ)) := rpow_pos_of_pos hxn' _
    have h5 : 0 < (L + ε / 2) * (L + ε / 2) ^ (-(↑(n % ↑m1) / (n : ℝ))) :=
      mul_pos hL0' (rpow_pos_of_pos hL0' _)
    /- We combine the previous steps to deduce that
     `μ (x ^ (↑m1 * (n / ↑m1) + n % ↑m1)) ^ (1 / ↑n) < L + ε`. -/
    calc μ (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)) + n % m1)) ^ (1 / (n : ℝ)) =
          μ (x ^ ((m1 : ℕ) * (n / (m1 : ℕ))) * x ^ (n % m1)) ^ (1 / (n : ℝ)) := by rw [pow_add]
      _ ≤ (μ (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) * μ (x ^ (n % m1))) ^ (1 / (n : ℝ)) :=
        (rpow_le_rpow (apply_nonneg μ _) (map_mul_le_mul μ _ _) (one_div_cast_nonneg _))
      _ = μ (x ^ ((m1 : ℕ) * (n / (m1 : ℕ)))) ^ (1 / (n : ℝ)) *
          μ (x ^ (n % m1)) ^ (1 / (n : ℝ)) :=
        (mul_rpow (apply_nonneg μ _) (apply_nonneg μ _))
      _ ≤ (μ (x ^ (m1 : ℕ)) ^ (n / (m1 : ℕ))) ^ (1 / (n : ℝ)) *
            μ (x ^ (n % m1)) ^ (1 / (n : ℝ)) := by gcongr
      _ < (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) *
            μ (x ^ (n % m1)) ^ (1 / (n : ℝ)) := by gcongr
      _ ≤ (L + ε / 2) * (L + ε / 2) ^ (-(((n % m1 : ℕ) : ℝ) / (n : ℝ))) *
            (μ x ^ (n % m1)) ^ (1 / (n : ℝ)) := by gcongr
      _ ≤ L + ε := h3

/-- If `μ 1 ≤ 1`, then `smoothingFun μ x` is the limit of `smoothingSeminormSeq μ x`
  as `n` tends to infinity. -/
/-
**tendsto_smoothingFun_of_map_one_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_smoothingFun_of_map_one_le_one (hμ1 : μ 1 <= 1) (x : R) : Tendsto 
(smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x))
参数：hμ1 : μ 1 <= 1；x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_smoothingFun_of_eq_zero`：tendsto_smoothingFun_of_eq_zero {x : R}
 (hx : μ x = 0) : Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)
)
· 使用定理 `tendsto_smoothingFun_of_ne_zero`：tendsto_smoothingFun_of_ne_zero (hμ1 : 
μ 1 <= 1) {x : R} (hx : μ x != 0) : Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 
(smoothingFun μ x))

--- 原说明 ---
If `μ 1 ≤ 1`, then `smoothingFun μ x` is the limit of `smoothingSeminormSeq μ x`
  as `n` tends to infinity.
-/
theorem tendsto_smoothingFun_of_map_one_le_one (hμ1 : μ 1 ≤ 1) (x : R) :
    Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (smoothingFun μ x)) := by
  by_cases hx : μ x = 0
  · exact tendsto_smoothingFun_of_eq_zero μ hx
  · exact tendsto_smoothingFun_of_ne_zero μ hμ1 hx

/-- If `μ 1 ≤ 1`, then `smoothingFun μ x` is nonnegative. -/
/-
**smoothingFun_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingFun_nonneg (hμ1 : μ 1 <= 1) (x : R) : 0 <= smoothingFun μ x
参数：hμ1 : μ 1 <= 1；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_smoothingFun_of_map_one_le_one`：tendsto_smoothingFun_of_map_one_
le_one (hμ1 : μ 1 <= 1) (x : R) : Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (s
moothingFun μ x))
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…

--- 原说明 ---
If `μ 1 ≤ 1`, then `smoothingFun μ x` is nonnegative.
-/
theorem smoothingFun_nonneg (hμ1 : μ 1 ≤ 1) (x : R) : 0 ≤ smoothingFun μ x := by
  apply ge_of_tendsto (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
  simpa [eventually_atTop, ge_iff_le] using ⟨1, fun _ _ ↦ by positivity⟩

/-- If `μ 1 ≤ 1`, then `smoothingFun μ 1 ≤ 1`. -/
/-
**smoothingFun_one_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingFun_one_le (hμ1 : μ 1 <= 1) : smoothingFun μ 1 <= 1
参数：hμ1 : μ 1 <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_smoothingFun_of_map_one_le_one`：tendsto_smoothingFun_of_map_one_
le_one (hμ1 : μ 1 <= 1) (x : R) : Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (s
moothingFun μ x))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.rpow_le_rpow_iff`：rpow_le_rpow_iff (hx : 0 <= x) (hy : 0 <= y) (hz 
: 0 < z) : x ^ z <= y ^ z ↔ x <= y
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
If `μ 1 ≤ 1`, then `smoothingFun μ 1 ≤ 1`.
-/
theorem smoothingFun_one_le (hμ1 : μ 1 ≤ 1) : smoothingFun μ 1 ≤ 1 := by
  apply le_of_tendsto (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (1 : R))
  simp only [eventually_atTop]
  use 1
  rintro n hn
  simp only [smoothingSeminormSeq]
  rw [one_pow]
  conv_rhs => rw [← one_rpow (1 / n : ℝ)]
  have hn1 : 0 < (1 / n : ℝ) := by
    apply _root_.div_pos zero_lt_one
    rw [← cast_zero, cast_lt]
    exact succ_le_iff.mp hn
  exact (rpow_le_rpow_iff (apply_nonneg μ _) zero_le_one hn1).mpr hμ1

/-- For any `x` and any positive `n`, `smoothingFun μ x ≤ μ (x ^ (n : ℕ))^(1 / n : ℝ)`. -/
/-
**smoothingFun_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingFun_le (x : R) (n : PNat) : smoothingFun μ x <= μ (x ^ (n : Nat))
 ^ (1 / n : Real)
参数：x : R；n : PNat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `smoothingSeminormSeq_bddBelow`：smoothingSeminormSeq_bddBelow (x : R) : B
ddBelow (Set.range fun n : Nat+ => μ (x ^ (n : Nat)) ^ (1 / (n : Real)))

--- 原说明 ---
For any `x` and any positive `n`, `smoothingFun μ x ≤ μ (x ^ (n : ℕ))^(1 / n : ℝ
)`.
-/
theorem smoothingFun_le (x : R) (n : PNat) :
    smoothingFun μ x ≤ μ (x ^ (n : ℕ)) ^ (1 / n : ℝ) :=
  ciInf_le (smoothingSeminormSeq_bddBelow μ x) _

/-- For all `x : R`, `smoothingFun μ x ≤ μ x`. -/
/-
**smoothingFun_le_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingFun_le_self (x : R) : smoothingFun μ x <= μ x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `smoothingFun_le`：smoothingFun_le (x : R) (n : PNat) : smoothingFun μ x <
= μ (x ^ (n : Nat)) ^ (1 / n : Real)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PNat.one_coe`：one_coe : ((1 : Nat+) : Nat) = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
For all `x : R`, `smoothingFun μ x ≤ μ x`.
-/
theorem smoothingFun_le_self (x : R) : smoothingFun μ x ≤ μ x := by
  apply (smoothingFun_le μ x 1).trans
  rw [PNat.one_coe, pow_one, cast_one, div_one, rpow_one]

/- In this section, we prove that if `μ` is nonarchimedean, then `smoothingFun μ` is
  nonarchimedean. -/
section IsNonarchimedean

variable {x y : R} (hn : ∀ n : ℕ, ∃ m < n + 1, μ ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤
  (μ (x ^ m) * μ (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)))

/-- Auxiliary sequence for the proof that `smoothingFun` is nonarchimedean. -/
/-
**mu** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary sequence for the proof that `smoothingFun` is nonarchimedean.
-/
private def mu : ℕ → ℕ := fun n => Classical.choose (hn n)
/-
**mu_property** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mu_property (n : ℕ) : μ ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤
    (μ (x ^ mu μ hn n) * μ (y ^ (n - mu μ hn n : ℕ))) ^ (1 / (n : ℝ)) :=
  (Classical.choose_spec (hn n)).2
/-
**mu_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mu_le (n : ℕ) : mu μ hn n ≤ n := by
  simpa [mu] using (Classical.choose_spec (hn n)).1
/-
**mu_bdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mu_bdd (n : ℕ) : (mu μ hn n : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
  refine Set.mem_Icc.mpr ⟨div_nonneg (cast_nonneg (mu μ hn n)) (cast_nonneg n), ?_⟩
  by_cases hn0 : n = 0
  · rw [hn0, cast_zero, div_zero]; exact zero_le_one
  · rw [div_le_one (cast_pos.mpr (Nat.pos_of_ne_zero hn0)), cast_le]
    exact mu_le _ _ _
/-
**** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem μ_bddBelow (s : ℕ → ℕ) {x : R} (ψ : ℕ → ℕ) :
    BddBelow {a : ℝ |
      ∀ᶠ n : ℝ in map (fun n : ℕ => μ x ^ (↑(s (ψ n)) * (1 / (ψ n : ℝ)))) atTop, n ≤ a} := by
  use 0
  simp only [mem_lowerBounds, eventually_map, eventually_atTop, Set.mem_ofPred_eq,
    forall_exists_index]
  intro r m hm
  exact le_trans (rpow_nonneg (apply_nonneg μ _) _) (hm m (le_refl _))
/-
**** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem μ_bddAbove (hμ1 : μ 1 ≤ 1) {s : ℕ → ℕ} (hs : ∀ n : ℕ, s n ≤ n) (x : R)
    (ψ : ℕ → ℕ) : BddAbove (Set.range fun n : ℕ => μ (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))) := by
  have hψ : ∀ n, 0 ≤ 1 / (ψ n : ℝ) := fun _ ↦ by simp only [one_div, inv_nonneg, cast_nonneg]
  by_cases! hx : μ x ≤ 1
  · use 1
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index]
    rintro _ n rfl
    apply le_trans (rpow_le_rpow (apply_nonneg _ _) (map_pow_le_pow' hμ1 _ _) (hψ n))
    rw [← rpow_natCast, ← rpow_mul (apply_nonneg _ _), mul_one_div]
    exact rpow_le_one (apply_nonneg _ _) hx (div_nonneg (cast_nonneg _) (cast_nonneg _))
  · use μ x
    simp only [mem_upperBounds, Set.mem_range, forall_exists_index]
    rintro _ n rfl
    apply le_trans (rpow_le_rpow (apply_nonneg _ _) (map_pow_le_pow' hμ1 _ _) (hψ n))
    rw [← rpow_natCast, ← rpow_mul (apply_nonneg _ _), mul_one_div]
    conv_rhs => rw [← rpow_one (μ x)]
    rw [rpow_le_rpow_left_iff hx]
    exact div_le_one_of_le₀ (cast_le.mpr (hs (ψ n))) (cast_nonneg _)
/-
**** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem μ_bddAbove' (hμ1 : μ 1 ≤ 1) {s : ℕ → ℕ} (hs : ∀ n : ℕ, s n ≤ n) (x : R)
    (ψ : ℕ → ℕ) : BddAbove ((fun n : ℕ => μ (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))) '' Set.univ) := by
  rw [Set.image_eq_range]
  convert! μ_bddAbove μ hμ1 hs x ψ
  ext
  simp [one_div, Set.mem_range, Subtype.exists, Set.mem_univ, exists_const]
/-
**** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem μ_nonempty {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x : R} (ψ : ℕ → ℕ) :
    {a : ℝ | ∀ᶠ n : ℝ in map (fun n : ℕ => μ x ^ (↑(s (ψ n)) * (1 / (ψ n : ℝ)))) atTop,
      n ≤ a}.Nonempty := by
  by_cases hμx : μ x < 1
  · use 1
    simp only [eventually_map, eventually_atTop, Set.mem_ofPred_eq]
    exact ⟨0, fun _ _ ↦ rpow_le_one (apply_nonneg _ _) (le_of_lt hμx)
      (mul_nonneg (cast_nonneg _) (one_div_nonneg.mpr (cast_nonneg _)))⟩
  · use μ x
    simp only [eventually_map, eventually_atTop, Set.mem_ofPred_eq]
    use 0
    intro b _
    nth_rw 2 [← rpow_one (μ x)]
    apply rpow_le_rpow_of_exponent_le (not_lt.mp hμx)
    rw [mul_one_div]
    exact div_le_one_of_le₀ (cast_le.mpr (hs_le (ψ b))) (cast_nonneg _)
/-
**** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem μ_limsup_le_one {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x : R} {ψ : ℕ → ℕ}
    (hψ_lim : Tendsto ((fun n : ℕ => ↑(s n) / (n : ℝ)) ∘ ψ) atTop (𝓝 0)) :
    limsup (fun n : ℕ => μ x ^ ((s (ψ n) : ℝ) * (1 / (ψ n : ℝ)))) atTop ≤ 1 := by
  simp only [limsup, limsSup]
  rw [csInf_le_iff (μ_bddBelow μ s ψ) (μ_nonempty μ hs_le ψ)]
  · intro c hc_bd
    simp only [mem_lowerBounds, eventually_map, eventually_atTop, Set.mem_ofPred_eq,
      forall_exists_index] at hc_bd
    by_cases hμx : μ x < 1
    · apply hc_bd (1 : ℝ) 0
      intro b _
      exact rpow_le_one (apply_nonneg _ _) (le_of_lt hμx)
          (mul_nonneg (cast_nonneg _) (one_div_nonneg.mpr (cast_nonneg _)))
    · have hμ_lim : Tendsto (fun n : ℕ => μ x ^ (↑(s (ψ n)) * (1 / (ψ n : ℝ)))) atTop (𝓝 1) := by
        nth_rw 1 [← rpow_zero (μ x)]
        convert!
          Tendsto.rpow tendsto_const_nhds hψ_lim
            (Or.inl (ne_of_gt (lt_of_lt_of_le zero_lt_one (not_lt.mp hμx))))
        · simp only [rpow_zero, mul_one_div, Function.comp_apply]
        · rw [rpow_zero]
      rw [tendsto_atTop_nhds] at hμ_lim
      apply le_of_forall_pos_le_add
      intro ε hε
      have h1 : (1 : ℝ) ∈ Set.Ioo 0 (1 + ε) := by
        simp only [Set.mem_Ioo, zero_lt_one, lt_add_iff_pos_right, hε, and_self]
      obtain ⟨k, hk⟩ := hμ_lim (Set.Ioo (0 : ℝ) (1 + ε)) h1 isOpen_Ioo
      exact hc_bd (1 + ε) k fun b hb => le_of_lt (Set.mem_Ioo.mp (hk b hb)).2
/-
**limsup_mu_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem limsup_mu_le (hμ1 : μ 1 ≤ 1) {s : ℕ → ℕ} (hs_le : ∀ n : ℕ, s n ≤ n) {x : R}
    {a : ℝ} (a_in : a ∈ Set.Icc (0 : ℝ) 1) {ψ : ℕ → ℕ} (hψ_mono : StrictMono ψ)
    (hψ_lim : Tendsto ((fun n : ℕ => (s n : ℝ) / ↑n) ∘ ψ) atTop (𝓝 a)) :
    limsup (fun n : ℕ => μ (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))) atTop ≤ smoothingFun μ x ^ a := by
  by_cases ha : a = 0
  · rw [ha] at hψ_lim
    calc limsup (fun n : ℕ => μ (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ))) atTop ≤
          limsup (fun n : ℕ => μ x ^ ((s (ψ n) : ℝ) * (1 / (ψ n : ℝ)))) atTop := by
          apply csInf_le_csInf _ (μ_nonempty μ hs_le ψ)
          · intro b hb
            simp only [eventually_map, eventually_atTop, Set.mem_ofPred_eq] at hb ⊢
            obtain ⟨m, hm⟩ := hb
            use m
            intro k hkm
            apply le_trans _ (hm k hkm)
            rw [rpow_mul (apply_nonneg μ x), rpow_natCast]
            gcongr
            exact map_pow_le_pow' hμ1 x _
          · use 0
            simp only [mem_lowerBounds, eventually_map, eventually_atTop,
              Set.mem_ofPred_eq, forall_exists_index]
            exact fun _ m hm ↦ le_trans (by positivity) (hm m (le_refl _))
      _ ≤ 1 := (μ_limsup_le_one μ hs_le hψ_lim)
      _ = smoothingFun μ x ^ a := by rw [ha, rpow_zero]
  · have ha_pos : 0 < a := lt_of_le_of_ne a_in.1 (Ne.symm ha)
    have h_eq : (fun n : ℕ =>
        (μ (x ^ s (ψ n)) ^ (1 / (s (ψ n) : ℝ))) ^ ((s (ψ n) : ℝ) / (ψ n : ℝ))) =ᶠ[atTop]
        fun n : ℕ => μ (x ^ s (ψ n)) ^ (1 / (ψ n : ℝ)) := by
      have h : (fun n : ℕ => (1 : ℝ) / (s (ψ n) : ℝ) * (s (ψ n) : ℝ)) =ᶠ[atTop] 1 := by
        apply Filter.EventuallyEq.div_mul_cancel_atTop
        exact (tendsto_natCast_atTop_atTop.comp hψ_mono.tendsto_atTop).num ha_pos hψ_lim
      simp_rw [← rpow_mul (apply_nonneg μ _), mul_div]
      exact EventuallyEq.comp₂ EventuallyEq.rfl HPow.hPow (h.div EventuallyEq.rfl)
    exact ((tendsto_smoothingFun_of_map_one_le_one μ hμ1 x |>.comp <|
      tendsto_natCast_atTop_iff.mp <| (tendsto_natCast_atTop_atTop.comp
        hψ_mono.tendsto_atTop).num ha_pos hψ_lim).rpow
          hψ_lim <| .inr ha_pos).congr' h_eq |>.limsup_eq.le
/-
**tendsto_smoothingFun_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_smoothingFun_comp (hμ1 : μ 1 <= 1) (x : R) {ψ : Nat -> Nat} (hψ_mo
no : StrictMono ψ) : Tendsto (fun n : Nat => μ (x ^ ψ n) ^ (1 / ψ n : Real)) atT
op (𝓝 (smoothingFun μ x))
参数：hμ1 : μ 1 <= 1；x : R；hψ_mono : StrictMono ψ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_smoothingFun_of_map_one_le_one`：tendsto_smoothingFun_of_map_one_
le_one (hμ1 : μ 1 <= 1) (x : R) : Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (s
moothingFun μ x))
-/
theorem tendsto_smoothingFun_comp (hμ1 : μ 1 ≤ 1) (x : R) {ψ : ℕ → ℕ}
    (hψ_mono : StrictMono ψ) :
    Tendsto (fun n : ℕ => μ (x ^ ψ n) ^ (1 / ψ n : ℝ)) atTop (𝓝 (smoothingFun μ x)) :=
  have hψ_lim' : Tendsto ψ atTop atTop := StrictMono.tendsto_atTop hψ_mono
  (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x).comp hψ_lim'

/-- If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun μ` is nonarchimedean. -/
/-
**isNonarchimedean_smoothingFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNonarchimedean_smoothingFun (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) 
: IsNonarchimedean (smoothingFun μ)
参数：hμ1 : μ 1 <= 1；hna : IsNonarchimedean μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingSeminorm.exists_index_pow_le`：exists_index_pow_le (hna : IsNonarchim
edean p) (x y : R) (n : Nat) : exists (m : Nat), m < n + 1 ∧ p ((x + y) ^ (n : N
at)) ^ (1 / (n : Real)…
· 使用定理 `_private.Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm.0.mu_le`：∀ 
{R : Type u_1} [inst : CommRing R] (μ : RingSeminorm R) {x y : R}   (hn : ∀ (n :
 ℕ), ∃ m < n + 1, μ ((x + y) ^ n) ^ (1 / ↑n) ≤ (μ (x ^ m) …
· 使用定理 `_private.Mathlib.Analysis.Normed.Unbundled.SmoothingSeminorm.0.mu_bdd`：∀
 {R : Type u_1} [inst : CommRing R] (μ : RingSeminorm R) {x y : R}   (hn : ∀ (n 
: ℕ), ∃ m < n + 1, μ ((x + y) ^ n) ^ (1 / ↑n) ≤ (μ (x ^ m) …
· 使用定理 `Metric.isBounded_Icc`：isBounded_Icc (a b : α) : IsBounded (Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_subseq_of_bounded`：tendsto_subseq_of_bounded (hs : IsBounded s) 
{x : Nat -> X} (hx : forall n, x n in s) : exists a in closure s, exists φ : Nat
 -> Nat, Strict…
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.ne_zero`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Filter.Tendsto.const_sub`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] (b : G) {c : G} {f : α → G}   {l : 
Filter α}, Fil…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Set.Icc.mem_iff_one_sub_mem`：mem_iff_one_sub_mem {t : β} : t in Icc (0 :
 β) 1 ↔ 1 - t in Icc (0 : β) 1
（共 96 条，此处仅展示前 30 条）

--- 原说明 ---
If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun μ` is nonarchimedean.
-/
theorem isNonarchimedean_smoothingFun (hμ1 : μ 1 ≤ 1) (hna : IsNonarchimedean μ) :
    IsNonarchimedean (smoothingFun μ) := by
  -- Fix `x, y : R`.
  intro x y
  have hn : ∀ n : ℕ, ∃ m < n + 1,
      μ ((x + y) ^ (n : ℕ)) ^ (1 / (n : ℝ)) ≤ (μ (x ^ m) * μ (y ^ (n - m : ℕ))) ^ (1 / (n : ℝ)) :=
    fun n => RingSeminorm.exists_index_pow_le μ hna x y n
  /- For each `n : ℕ`, we find `mu n` and `nu n` such that `mu n + nu n = n` and
    `μ ((x + y) ^ n) ^ (1 / n) ≤ (μ (x ^ (mu n)) * μ (y ^ (nu n))) ^ (1 / n)`. -/
  let mu : ℕ → ℕ := fun n => mu μ hn n
  set nu : ℕ → ℕ := fun n => n - mu n with hnu
  have hmu_le : ∀ n : ℕ, mu n ≤ n := fun n => mu_le μ hn n
  have hmu_bdd : ∀ n : ℕ, (mu n : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := fun n => mu_bdd μ hn n
  have hs : Bornology.IsBounded (Set.Icc (0 : ℝ) 1) := Metric.isBounded_Icc 0 1
  /- Since `0 ≤ (mu n) / n ≤ 1` for all `n`, we can find a subsequence `(ψ n) ⊆ ℕ` such that the
    limit of `mu (ψ n) / ψ n` as `n` tends to infinity exists. We denote this limit by `a`. -/
  obtain ⟨a, a_in, ψ, hψ_mono, hψ_lim⟩ := tendsto_subseq_of_bounded hs hmu_bdd
  rw [closure_Icc] at a_in
  /- The limit of `nu (ψ n) / ψ n` as `n` tends to infinity also exists, and it is equal to
    `b := 1 - a` -/
  set b := 1 - a with hb
  have hb_lim : Tendsto ((fun n : ℕ => (nu n : ℝ) / ↑n) ∘ ψ) atTop (𝓝 b) := by
    apply Tendsto.congr' _ (Tendsto.const_sub 1 hψ_lim)
    simp only [EventuallyEq, Function.comp_apply, eventually_atTop]
    use 1
    intro m hm
    have h0 : (ψ m : ℝ) ≠ 0 := cast_ne_zero.mpr
      (hψ_mono (Nat.pos_of_ne_zero (one_le_iff_ne_zero.mp hm))).ne_zero
    rw [← div_self h0, ← sub_div, cast_sub (hmu_le _)]
  have b_in : b ∈ Set.Icc (0 : ℝ) 1 := Set.Icc.mem_iff_one_sub_mem.mp a_in
  have hnu_le : ∀ n : ℕ, nu n ≤ n := fun n => by simp only [hnu, tsub_le_self]
  have hx : limsup (fun n : ℕ => μ (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ))) atTop ≤
      smoothingFun μ x ^ a := limsup_mu_le μ hμ1 hmu_le a_in hψ_mono hψ_lim
  have hy : limsup (fun n : ℕ => μ (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ))) atTop ≤
      smoothingFun μ y ^ b :=
    limsup_mu_le μ hμ1 hnu_le b_in hψ_mono hb_lim
  have hxy : limsup
      (fun n => μ (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ)) * μ (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ))) atTop ≤
        smoothingFun μ x ^ a * smoothingFun μ y ^ b := by
    have hxy' :
      limsup (fun n : ℕ => μ (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ)) * μ (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ)))
        atTop ≤ limsup (fun n : ℕ => μ (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ))) atTop *
          limsup (fun n : ℕ => μ (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ))) atTop :=
      limsup_mul_le (Frequently.of_forall (fun n ↦ by positivity))
        (μ_bddAbove μ hμ1 hmu_le x ψ).isBoundedUnder_of_range
        (Eventually.of_forall (fun n ↦ by positivity))
        (μ_bddAbove μ hμ1 hnu_le y ψ).isBoundedUnder_of_range
    have h_bdd : IsBoundedUnder LE.le atTop fun n : ℕ => μ (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ)) :=
      RingSeminorm.isBoundedUnder μ hμ1 hnu_le ψ
    apply le_trans hxy' (mul_le_mul hx hy (le_limsup_of_frequently_le (Frequently.of_forall
      (fun n ↦ by positivity)) h_bdd) (rpow_nonneg (smoothingFun_nonneg μ hμ1 x) _))
  apply le_of_forall_sub_le
  /- Fix `ε > 0`. We first show that `smoothingFun μ x ^ a * smoothingFun μ y ^ b + ε ≤
    max (smoothingFun μ x) (smoothingFun μ y) + ε`. -/
  intro ε hε
  rw [sub_le_iff_le_add]
  have h_mul : smoothingFun μ x ^ a * smoothingFun μ y ^ b + ε ≤
      max (smoothingFun μ x) (smoothingFun μ y) + ε := by
    rw [max_def]
    split_ifs with h
    · rw [add_le_add_iff_right]
      apply le_trans (mul_le_mul_of_nonneg_right
        (rpow_le_rpow (smoothingFun_nonneg μ hμ1 _) h a_in.1)
        (rpow_nonneg (smoothingFun_nonneg μ hμ1 _) _))
      rw [hb, ← rpow_add_of_nonneg (smoothingFun_nonneg μ hμ1 _) a_in.1
        (sub_nonneg.mpr a_in.2), add_sub, add_sub_cancel_left, rpow_one]
    · rw [add_le_add_iff_right]
      apply le_trans (mul_le_mul_of_nonneg_left
        (rpow_le_rpow (smoothingFun_nonneg μ hμ1 _) (le_of_lt (not_le.mp h)) b_in.1)
        (rpow_nonneg (smoothingFun_nonneg μ hμ1 _) _))
      rw [hb, ← rpow_add_of_nonneg (smoothingFun_nonneg μ hμ1 _) a_in.1
        (sub_nonneg.mpr a_in.2), add_sub, add_sub_cancel_left, rpow_one]
  apply le_trans _ h_mul
  /- We then show that there exists some natural number `N` such that
    `μ (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ)) * μ (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ)) <
      smoothingFun μ x ^ a * smoothingFun μ y ^ b + ε`. -/
  have hex : ∃ n : PNat, μ (x ^ mu (ψ n)) ^ (1 / (ψ n : ℝ)) * μ (y ^ nu (ψ n)) ^ (1 / (ψ n : ℝ)) <
      smoothingFun μ x ^ a * smoothingFun μ y ^ b + ε :=
    Filter.exists_lt_of_limsup_le (bddAbove_range_mul (μ_bddAbove μ hμ1 hmu_le _ _)
      (fun n ↦ by positivity) (μ_bddAbove μ hμ1 hnu_le _ _)
      (fun n ↦ by positivity)).isBoundedUnder_of_range hxy hε
  obtain ⟨N, hN⟩ := hex
  /- By definition of `smoothingFun`, and applying the inequality `hN`, it suffices to show that
    `μ ((x + y) ^ ψ N) ^ (1 / ψ N) ≤ μ (x ^ mu (ψ N)) ^ (1 / ψ N) * μ (y ^ nu ψ N) ^ (1 / ψ N)`. -/
  apply (ciInf_le (smoothingSeminormSeq_bddBelow μ _)
    ⟨ψ N, (hψ_mono.lt_iff_lt.mpr N.pos).pos⟩).trans (hN.le.trans' _)
  simpa [PNat.mk_coe, hnu, ← mul_rpow (apply_nonneg μ _) (apply_nonneg μ _)] using
    mu_property μ hn (ψ N)

end IsNonarchimedean

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun` is a ring seminorm. -/
/-
**smoothingSeminorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothingSeminorm (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) : RingSemino
rm R where toFun
参数：hμ1 : μ 1 <= 1；hna : IsNonarchimedean μ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun` is a ring seminorm.
-/
def smoothingSeminorm (hμ1 : μ 1 ≤ 1) (hna : IsNonarchimedean μ) : RingSeminorm R where
  toFun     := smoothingFun μ
  map_zero' := by
    apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 0)
      tendsto_const_nhds
    simp only [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    simp only [smoothingSeminormSeq]
    rw [zero_pow (pos_iff_ne_zero.mp hn), map_zero, zero_rpow]
    exact one_div_ne_zero (cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn))
  add_le' _ _ := (isNonarchimedean_smoothingFun μ hμ1 hna).add_le (smoothingFun_nonneg μ hμ1)
  neg' n := by
    simp only [smoothingFun]
    congr
    ext n
    rw [neg_pow]
    rcases neg_one_pow_eq_or R n with hpos | hneg
    · rw [hpos, one_mul]
    · rw [hneg, neg_one_mul, map_neg_eq_map μ]
  mul_le' x y := by
    apply le_of_tendsto_of_tendsto' (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x * y))
      (Tendsto.mul (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
        (tendsto_smoothingFun_of_map_one_le_one μ hμ1 y))
    intro n
    have hn : 0 ≤ 1 / (n : ℝ) := by simp only [one_div, inv_nonneg, cast_nonneg]
    simp only [smoothingSeminormSeq]
    rw [← mul_rpow (apply_nonneg μ _) (apply_nonneg μ _), mul_pow]
    gcongr
    exact map_mul_le_mul μ _ _

/-- If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingSeminorm μ 1 ≤ 1`. -/
/-
**smoothingSeminorm_map_one_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingSeminorm_map_one_le_one (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean 
μ) : smoothingSeminorm μ hμ1 hna 1 <= 1
参数：hμ1 : μ 1 <= 1；hna : IsNonarchimedean μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smoothingFun_one_le`：smoothingFun_one_le (hμ1 : μ 1 <= 1) : smoothingFun
 μ 1 <= 1

--- 原说明 ---
If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingSeminorm μ 1 ≤ 1`.
-/
theorem smoothingSeminorm_map_one_le_one (hμ1 : μ 1 ≤ 1)
    (hna : IsNonarchimedean μ) : smoothingSeminorm μ hμ1 hna 1 ≤ 1 :=
  smoothingFun_one_le μ hμ1

/-- If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun μ` is
  power-multiplicative. -/
/-
**isPowMul_smoothingFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPowMul_smoothingFun (hμ1 : μ 1 <= 1) : IsPowMul (smoothingFun μ)
参数：hμ1 : μ 1 <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_smoothingFun_of_map_one_le_one`：tendsto_smoothingFun_of_map_one_
le_one (hμ1 : μ 1 <= 1) (x : R) : Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (s
moothingFun μ x))
· 使用定理 `Filter.tendsto_atTop_atTop_of_monotone`：tendsto_atTop_atTop_of_monotone 
[Preorder α] [Preorder β] {f : α -> β} (hf : Monotone f) (h : forall b, exists a
, b <= f a) : Tendsto f atTo…
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `le_mul_of_one_le_left'`：le_mul_of_one_le_left' [MulRightMono α] {a b : α
} (h : 1 <= b) : a <= b * a
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `one_div_mul_one_div`：one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `μ 1 ≤ 1` and `μ` is nonarchimedean, then `smoothingFun μ` is
  power-multiplicative.
-/
theorem isPowMul_smoothingFun (hμ1 : μ 1 ≤ 1) : IsPowMul (smoothingFun μ) := by
  intro x m hm
  have hlim : Tendsto (fun n => smoothingSeminormSeq μ x (m * n)) atTop
      (𝓝 (smoothingFun μ x)) :=
    Tendsto.comp (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x) (tendsto_atTop_atTop_of_monotone
      (fun n k hnk ↦ mul_le_mul_right hnk m) (fun n ↦ ⟨n, le_mul_of_one_le_left' hm⟩))
  apply tendsto_nhds_unique _ (Tendsto.pow hlim m)
  have h_eq (n : ℕ) : smoothingSeminormSeq μ x (m * n) ^ m = smoothingSeminormSeq μ (x ^ m) n := by
    have hm' : (m : ℝ) ≠ 0 := cast_ne_zero.mpr (_root_.ne_of_gt (lt_of_lt_of_le zero_lt_one hm))
    simp only [smoothingSeminormSeq]
    rw [pow_mul, ← rpow_natCast, ← rpow_mul (apply_nonneg μ _), cast_mul, ← one_div_mul_one_div,
      mul_comm (1 / (m : ℝ)), mul_assoc, one_div_mul_cancel hm', mul_one]
  simpa [h_eq] using tendsto_smoothingFun_of_map_one_le_one μ hμ1 _

/-- If `μ 1 ≤ 1` and `∀ (1 ≤ n), μ (x ^ n) = μ x ^ n`, then `smoothingFun μ x = μ x`. -/
/-
**smoothingFun_of_powMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingFun_of_powMul (hμ1 : μ 1 <= 1) {x : R} (hx : forall (n : Nat) (_h
n : 1 <= n), μ (x ^ n) = μ x ^ n) : smoothingFun μ x = μ x
参数：hμ1 : μ 1 <= 1；hx : forall (n : Nat) (_hn : 1 <= n), μ (x ^ n) = μ x ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique_of_eventuallyEq`：tendsto_nhds_unique_of_eventuallyEq
 [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l
 (𝓝 a)) (hb : Tendsto g l…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_smoothingFun_of_map_one_le_one`：tendsto_smoothingFun_of_map_one_
le_one (hμ1 : μ 1 <= 1) (x : R) : Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (s
moothingFun μ x))
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用引理 `mul_one_div_cancel`：mul_one_div_cancel (h : a != 0) : a * (1 / a) = 1
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x

--- 原说明 ---
If `μ 1 ≤ 1` and `∀ (1 ≤ n), μ (x ^ n) = μ x ^ n`, then `smoothingFun μ x = μ x`
.
-/
theorem smoothingFun_of_powMul (hμ1 : μ 1 ≤ 1) {x : R}
    (hx : ∀ (n : ℕ) (_hn : 1 ≤ n), μ (x ^ n) = μ x ^ n) : smoothingFun μ x = μ x := by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  have hn0 : (n : ℝ) ≠ 0 := cast_ne_zero.mpr (one_le_iff_ne_zero.mp hn)
  rw [hx n hn, ← rpow_natCast, ← rpow_mul (apply_nonneg μ _), mul_one_div_cancel hn0, rpow_one]

/-- If `μ 1 ≤ 1` and `∀ y : R, μ (x * y) = μ x * μ y`, then `smoothingFun μ x = μ x`. -/
/-
**smoothingFun_apply_of_map_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingFun_apply_of_map_mul_eq_mul (hμ1 : μ 1 <= 1) {x : R} (hx : forall
 y : R, μ (x * y) = μ x * μ y) : smoothingFun μ x = μ x
参数：hμ1 : μ 1 <= 1；hx : forall y : R, μ (x * y) = μ x * μ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique_of_eventuallyEq`：tendsto_nhds_unique_of_eventuallyEq
 [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l
 (𝓝 a)) (hb : Tendsto g l…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_smoothingFun_of_map_one_le_one`：tendsto_smoothingFun_of_map_one_
le_one (hμ1 : μ 1 <= 1) (x : R) : Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (s
moothingFun μ x))
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `map_pow_le_pow`：∀ {F : Type u_2} {α : Type u_3} [inst : Ring α] [inst_1 
: FunLike F α ℝ] [RingSeminormClass F α ℝ] (f : F) (a : α)   {n : ℕ}, n ≠ 0 → f 
(a ^…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `Real.zero_rpow`：zero_rpow {x : Real} (h : x != 0) : (0 : Real) ^ x = 0
· 使用定理 `Nat.one_div_cast_ne_zero`：one_div_cast_ne_zero {n : Nat} (hn : n != 0) :
 1 / (n : α) != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If `μ 1 ≤ 1` and `∀ y : R, μ (x * y) = μ x * μ y`, then `smoothingFun μ x = μ x`
.
-/
theorem smoothingFun_apply_of_map_mul_eq_mul (hμ1 : μ 1 ≤ 1) {x : R}
    (hx : ∀ y : R, μ (x * y) = μ x * μ y) : smoothingFun μ x = μ x := by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 x)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  use 1
  intro n hn
  simp only [smoothingSeminormSeq]
  by_cases hx0 : μ x = 0
  · have hxn : μ (x ^ n) = 0 := by
      apply le_antisymm _ (apply_nonneg μ _)
      apply le_trans (map_pow_le_pow μ x (one_le_iff_ne_zero.mp hn))
      rw [hx0, zero_pow (pos_iff_ne_zero.mp hn)]
    rw [hx0, hxn, zero_rpow (one_div_cast_ne_zero (one_le_iff_ne_zero.mp hn))]
  · have h1 : μ 1 = 1 := by rw [← mul_right_inj' hx0, ← hx 1, mul_one, mul_one]
    have hn0 : (n : ℝ) ≠ 0 := cast_ne_zero.mpr (_root_.ne_of_gt (lt_of_lt_of_le zero_lt_one hn))
    rw [← mul_one (x ^ n), pow_mul_apply_eq_pow_mul μ hx, ← rpow_natCast, h1, mul_one,
      ← rpow_mul (apply_nonneg μ _), mul_one_div_cancel hn0, rpow_one]

/-- If `μ 1 ≤ 1`, `μ` is nonarchimedean, and `∀ y : R, μ (x * y) = μ x * μ y`, then
  `smoothingSeminorm μ x = μ x`. -/
/-
**smoothingSeminorm_apply_of_map_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingSeminorm_apply_of_map_mul_eq_mul (hμ1 : μ 1 <= 1) (hna : IsNonarc
himedean μ) {x : R} (hx : forall y : R, μ (x * y) = μ x * μ y) : smoothingSemino
rm μ hμ1 hna x = μ x
参数：hμ1 : μ 1 <= 1；hna : IsNonarchimedean μ；hx : forall y : R, μ (x * y) = μ x * 
μ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smoothingFun_apply_of_map_mul_eq_mul`：smoothingFun_apply_of_map_mul_eq_m
ul (hμ1 : μ 1 <= 1) {x : R} (hx : forall y : R, μ (x * y) = μ x * μ y) : smoothi
ngFun μ x = μ x

--- 原说明 ---
If `μ 1 ≤ 1`, `μ` is nonarchimedean, and `∀ y : R, μ (x * y) = μ x * μ y`, then
  `smoothingSeminorm μ x = μ x`.
-/
theorem smoothingSeminorm_apply_of_map_mul_eq_mul (hμ1 : μ 1 ≤ 1) (hna : IsNonarchimedean μ) {x : R}
    (hx : ∀ y : R, μ (x * y) = μ x * μ y) : smoothingSeminorm μ hμ1 hna x = μ x :=
  smoothingFun_apply_of_map_mul_eq_mul μ hμ1 hx

/-- If `μ 1 ≤ 1`, and `x` is multiplicative for `μ`, then it is multiplicative for
  `smoothingFun`. -/
/-
**smoothingFun_of_map_mul_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingFun_of_map_mul_eq_mul (hμ1 : μ 1 <= 1) {x : R} (hx : forall y : R
, μ (x * y) = μ x * μ y) (y : R) : smoothingFun μ (x * y) = smoothingFun μ x * s
moothingFun μ y
参数：hμ1 : μ 1 <= 1；hx : forall y : R, μ (x * y) = μ x * μ y；y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smoothingFun_apply_of_map_mul_eq_mul`：smoothingFun_apply_of_map_mul_eq_m
ul (hμ1 : μ 1 <= 1) {x : R} (hx : forall y : R, μ (x * y) = μ x * μ y) : smoothi
ngFun μ x = μ x
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `tendsto_smoothingFun_of_map_one_le_one`：tendsto_smoothingFun_of_map_one_
le_one (hμ1 : μ 1 <= 1) (x : R) : Tendsto (smoothingSeminormSeq μ x) atTop (𝓝 (s
moothingFun μ x))
· 使用定理 `tendsto_nhds_unique_of_eventuallyEq`：tendsto_nhds_unique_of_eventuallyEq
 [T2Space X] {f g : Y -> X} {l : Filter Y} {a b : X} [NeBot l] (ha : Tendsto f l
 (𝓝 a)) (hb : Tendsto g l…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `pow_mul_apply_eq_pow_mul`：pow_mul_apply_eq_pow_mul {M : Type*} [Monoid M
] (f : M₀ -> M) {x : M₀} (hx : forall y : M₀, f (x * y) = f x * f y) (n : Nat) :
 forall (y : M…
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NonnegHomClass.apply_nonneg`：∀ {F : Type u_7} {α : outParam (Type u_8)} 
{β : outParam (Type u_9)} {inst : Zero β} {inst_1 : LE β}   {inst_2 : FunLike F 
α β} [self : Nonn…
· 使用定理 `RingSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} {β :
 Type u_4} [inst : FunLike F α β] [inst_1 : NonUnitalNonAssocRing α]   [inst_2 :
 Semiring β] [inst_3 : L…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `μ 1 ≤ 1`, and `x` is multiplicative for `μ`, then it is multiplicative for
  `smoothingFun`.
-/
theorem smoothingFun_of_map_mul_eq_mul (hμ1 : μ 1 ≤ 1) {x : R} (hx : ∀ y : R, μ (x * y) = μ x * μ y)
    (y : R) : smoothingFun μ (x * y) = smoothingFun μ x * smoothingFun μ y := by
  have hlim : Tendsto (fun n => μ x * smoothingSeminormSeq μ y n) atTop
      (𝓝 (smoothingFun μ x * smoothingFun μ y)) := by
    rw [smoothingFun_apply_of_map_mul_eq_mul μ hμ1 hx]
    exact Tendsto.const_mul _ (tendsto_smoothingFun_of_map_one_le_one μ hμ1 y)
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_smoothingFun_of_map_one_le_one μ hμ1 (x * y))
    hlim
  simp only [EventuallyEq, eventually_atTop]
  use 1
  intro n hn1
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (_root_.ne_of_gt (lt_of_lt_of_le zero_lt_one hn1))
  simp only [smoothingSeminormSeq]
  rw [mul_pow, pow_mul_apply_eq_pow_mul μ hx, mul_rpow (pow_nonneg (apply_nonneg μ _) _)
    (apply_nonneg μ _), ← rpow_natCast, ← rpow_mul (apply_nonneg μ _), mul_one_div_cancel hn0,
    rpow_one]

/-- If `μ 1 ≤ 1`, `μ` is nonarchimedean, and `x` is multiplicative for `μ`, then `x` is
  multiplicative for `smoothingSeminorm`. -/
/-
**smoothingSeminorm_of_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smoothingSeminorm_of_mul (hμ1 : μ 1 <= 1) (hna : IsNonarchimedean μ) {x : 
R} (hx : forall y : R, μ (x * y) = μ x * μ y) (y : R) : smoothingSeminorm μ hμ1 
hna (x * y) = smoothingSeminorm μ hμ1 hna x * smoothingSeminorm μ hμ1 hna y
参数：hμ1 : μ 1 <= 1；hna : IsNonarchimedean μ；hx : forall y : R, μ (x * y) = μ x * 
μ y；y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smoothingFun_of_map_mul_eq_mul`：smoothingFun_of_map_mul_eq_mul (hμ1 : μ 
1 <= 1) {x : R} (hx : forall y : R, μ (x * y) = μ x * μ y) (y : R) : smoothingFu
n μ (x * y) = smooth…

--- 原说明 ---
If `μ 1 ≤ 1`, `μ` is nonarchimedean, and `x` is multiplicative for `μ`, then `x`
 is
  multiplicative for `smoothingSeminorm`.
-/
theorem smoothingSeminorm_of_mul (hμ1 : μ 1 ≤ 1) (hna : IsNonarchimedean μ) {x : R}
    (hx : ∀ y : R, μ (x * y) = μ x * μ y) (y : R) :
    smoothingSeminorm μ hμ1 hna (x * y) =
      smoothingSeminorm μ hμ1 hna x * smoothingSeminorm μ hμ1 hna y :=
  smoothingFun_of_map_mul_eq_mul μ hμ1 hx y

end smoothingSeminorm

