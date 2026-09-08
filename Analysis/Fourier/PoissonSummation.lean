/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Topology.ContinuousMap.Periodic

/-!
# Poisson's summation formula

We prove Poisson's summation formula `∑ (n : ℤ), f n = ∑ (n : ℤ), 𝓕 f n`, where `𝓕 f` is the
Fourier transform of `f`, under the following hypotheses:
* `f` is a continuous function `ℝ → ℂ`.
* The sum `∑ (n : ℤ), 𝓕 f n` is convergent.
* For all compacts `K ⊂ ℝ`, the sum `∑ (n : ℤ), ‖f(x + n)‖` is uniformly convergent on `K`.
  See `Real.tsum_eq_tsum_fourier` for this formulation.

These hypotheses are potentially a little awkward to apply, so we also provide the less general but
easier-to-use result `Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay`, in which we assume `f` and
`𝓕 f` both decay as `|x| ^ (-b)` for some `b > 1`, and the even more specific result
`SchwartzMap.tsum_eq_tsum_fourierIntegral`, where we assume that `f` is a Schwartz function. -/

public section


noncomputable section

open Function hiding comp_apply

open Set hiding restrict_apply

open Complex

open Real

open TopologicalSpace Filter MeasureTheory Asymptotics

open scoped Real Filter FourierTransform

open ContinuousMap

set_option backward.isDefEq.respectTransparency.types false in
/-- The key lemma for Poisson summation: the `m`-th Fourier coefficient of the periodic function
`∑' n : ℤ, f (x + n)` is the value at `m` of the Fourier transform of `f`. -/
/-
**Real.fourierCoeff_tsum_comp_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.fourierCoeff_tsum_comp_add {f : C(Real, Complex)} (hf : forall K : Co
mpacts Real, Summable fun n : Int => ‖(f.comp (ContinuousMap.addRight n)).restri
ct K‖) (m : Int) : fourierCoeff (Periodic.lift <| f.periodic_tsum_comp_add_zsmul
 1) m = 𝓕 (f : Real -> Complex) m
参数：Real, Complex；hf : forall K : Compacts Real, Summable fun n : Int => ‖(f.comp
 (ContinuousMap.addRight n)).restrict K‖；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.instCompactSpaceElemCoeCompacts`：∀ {X : Type u_4} [inst : 
TopologicalSpace X] (K : TopologicalSpace.Compacts X), CompactSpace ↑↑K
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用引理 `Circle.norm_coe`：norm_coe (z : Circle) : ‖(z : Complex)‖ = 1
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.norm_eq_iSup_norm`：norm_eq_iSup_norm : ‖f‖ = ⨆ x : α, ‖f x
‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMap.mul_apply`：mul_apply [Mul β] [ContinuousMul β] (f g : C(α,
 β)) (x : α) : (f * g) x = f x * g x
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `Function.Periodic.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
f : α → β} {c : α} [inst : Add α],   Function.Periodic f c → ∀ (g : β → γ), Func
tion.Periodi…
· 使用定理 `AddCircle.coe_add_period`：coe_add_period (x : 𝕜) : ((x + p : 𝕜) : AddCir
cle p) = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 104 条，此处仅展示前 30 条）

--- 原说明 ---
The key lemma for Poisson summation: the `m`-th Fourier coefficient of the perio
dic function
`∑' n : ℤ, f (x + n)` is the value at `m` of the Fourier transform of `f`.
-/
theorem Real.fourierCoeff_tsum_comp_add {f : C(ℝ, ℂ)}
    (hf : ∀ K : Compacts ℝ, Summable fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖)
    (m : ℤ) : fourierCoeff (Periodic.lift <| f.periodic_tsum_comp_add_zsmul 1) m =
      𝓕 (f : ℝ → ℂ) m := by
  -- NB: This proof can be shortened somewhat by telescoping together some of the steps in the calc
  -- block, but I think it's more legible this way. We start with preliminaries about the integrand.
  let e : C(ℝ, ℂ) := (fourier (-m)).comp ⟨((↑) : ℝ → UnitAddCircle), continuous_quotient_mk'⟩
  have neK : ∀ (K : Compacts ℝ) (g : C(ℝ, ℂ)), ‖(e * g).restrict K‖ = ‖g.restrict K‖ := by
    have (x : ℝ) : ‖e x‖ = 1 := (AddCircle.toCircle (-m • x)).norm_coe
    intro K g
    simp_rw [norm_eq_iSup_norm, restrict_apply, mul_apply, norm_mul, this, one_mul]
  have eadd : ∀ (n : ℤ), e.comp (ContinuousMap.addRight n) = e := by
    intro n; ext1 x
    have : Periodic e 1 := Periodic.comp (fun x => AddCircle.coe_add_period 1 x) (fourier (-m))
    simpa only [mul_one] using! this.int_mul n x
  -- Now the main argument. First unwind some definitions.
  calc
    fourierCoeff (Periodic.lift <| f.periodic_tsum_comp_add_zsmul 1) m =
        ∫ x in (0 : ℝ)..1, e x * (∑' n : ℤ, f.comp (ContinuousMap.addRight n)) x := by
      simp_rw [fourierCoeff_eq_intervalIntegral _ m 0, div_one, one_smul, zero_add, e, comp_apply,
        coe_mk, Periodic.lift_coe, zsmul_one, smul_eq_mul]
    -- Transform sum in C(ℝ, ℂ) evaluated at x into pointwise sum of values.
    _ = ∫ x in (0 : ℝ)..1, ∑' n : ℤ, (e * f.comp (ContinuousMap.addRight n)) x := by
      simp_rw [coe_mul, Pi.mul_apply,
        ← ContinuousMap.tsum_apply (summable_of_locally_summable_norm hf), tsum_mul_left]
    -- Swap sum and integral.
    _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, (e * f.comp (ContinuousMap.addRight n)) x := by
      refine (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm ?_).symm
      convert! hf ⟨uIcc 0 1, isCompact_uIcc⟩ using 1
      exact funext fun n => neK _ _
    _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, (e * f).comp (ContinuousMap.addRight n) x := by
      simp only [mul_comp] at eadd ⊢
      simp_rw [eadd]
    -- Rearrange sum of interval integrals into an integral over `ℝ`.
    _ = ∫ x, e x * f x := by
      suffices Integrable (e * f) from this.hasSum_intervalIntegral_comp_add_int.tsum_eq
      apply integrable_of_summable_norm_Icc
      convert! hf ⟨Icc 0 1, isCompact_Icc⟩ using 1
      simp_rw [mul_comp] at eadd ⊢
      simp_rw [eadd]
      exact funext fun n => neK ⟨Icc 0 1, isCompact_Icc⟩ _
    -- Minor tidying to finish
    _ = 𝓕 (f : ℝ → ℂ) m := by
      rw [fourier_real_eq_integral_exp_smul]
      congr 1 with x : 1
      rw [smul_eq_mul, comp_apply, coe_mk, coe_mk, ContinuousMap.toFun_eq_coe, fourier_coe_apply]
      congr 2
      push_cast
      ring

/-- **Poisson's summation formula**, most general form. -/
/-
**Real.tsum_eq_tsum_fourier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.tsum_eq_tsum_fourier {f : C(Real, Complex)} (h_norm : forall K : Comp
acts Real, Summable fun n : Int => ‖(f.comp <| ContinuousMap.addRight n).restric
t K‖) (h_sum : Summable fun n : Int => 𝓕 (f : Real -> Complex) n) (x : Real) : ∑
' n : Int, f (x + n) = ∑' n : Int, 𝓕 (f : Real -> Complex) n * fourier n (x : Un
itAddCircle)
参数：Real, Complex；h_norm : forall K : Compacts Real, Summable fun n : Int => ‖(f.
comp <| ContinuousMap.addRight n).restrict K‖；h_sum : Summable fun n : Int => 𝓕 
(f : Real -> Complex) n；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.instCompactSpaceElemCoeCompacts`：∀ {X : Type u_4} [inst : 
TopologicalSpace X] (K : TopologicalSpace.Compacts X), CompactSpace ↑↑K
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousMap.periodic_tsum_comp_add_zsmul`：periodic_tsum_comp_add_zsmul
 [AddCommGroup X] [ContinuousAdd X] [AddCommMonoid Y] [ContinuousAdd Y] [T2Space
 Y] (f : C(X, Y)) (p : X) : Func…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_coinduced_dom`：continuous_coinduced_dom {g : β -> γ} {t₁ : To
pologicalSpace α} {t₂ : TopologicalSpace γ} : Continuous[coinduced f t₁, t₂] g ↔
 Continuous[t₁…
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.fourierCoeff_tsum_comp_add`：Real.fourierCoeff_tsum_comp_add {f : C(
Real, Complex)} (hf : forall K : Compacts Real, Summable fun n : Int => ‖(f.comp
 (ContinuousMap.addRi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Periodic.lift.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {f f_
1 : α → β} (e_f : f = f_1) {c : α} [inst : AddGroup α] (h : Function.Periodic f 
c)   (x x_1 : α ⧸ AddSu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousMap.addRight.congr_simp`：∀ {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : Add X] [inst_2 : SeparatelyContinuousAdd X] (x x_1 : X),   x =
 x_1 → ContinuousMap.ad…
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ContinuousMap.hasSum_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : Topo
logicalSpace α] [inst_1 : TopologicalSpace β] {γ : Type u_3}   [inst_2 : AddComm
Monoid β] [inst_…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
**Poisson's summation formula**, most general form.
-/
theorem Real.tsum_eq_tsum_fourier {f : C(ℝ, ℂ)}
    (h_norm :
      ∀ K : Compacts ℝ, Summable fun n : ℤ => ‖(f.comp <| ContinuousMap.addRight n).restrict K‖)
    (h_sum : Summable fun n : ℤ => 𝓕 (f : ℝ → ℂ) n) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 (f : ℝ → ℂ) n * fourier n (x : UnitAddCircle) := by
  let F : C(UnitAddCircle, ℂ) :=
    ⟨(f.periodic_tsum_comp_add_zsmul 1).lift, continuous_coinduced_dom.mpr (map_continuous _)⟩
  have : Summable (fourierCoeff F) := by
    convert! h_sum
    exact Real.fourierCoeff_tsum_comp_add h_norm _
  convert! (has_pointwise_sum_fourier_series_of_summable this x).tsum_eq.symm using 1
  · simpa only [F, coe_mk, ← QuotientAddGroup.mk_zero, Periodic.lift_coe, zsmul_one, comp_apply,
      coe_addRight, zero_add]
       using (hasSum_apply (summable_of_locally_summable_norm h_norm).hasSum x).tsum_eq
  · simp_rw [← Real.fourierCoeff_tsum_comp_add h_norm, smul_eq_mul, F, coe_mk]

section RpowDecay

variable {E : Type*} [NormedAddCommGroup E]

/-- If `f` is `O(x ^ (-b))` at infinity, then so is the function
`fun x ↦ ‖f.restrict (Icc (x + R) (x + S))‖` for any fixed `R` and `S`. -/
/-
**isBigO_norm_Icc_restrict_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBigO_norm_Icc_restrict_atTop {f : C(Real, E)} {b : Real} (hb : 0 < b) (h
f : f =O[atTop] fun x : Real => |x| ^ (-b)) (R S : Real) : (fun x : Real => ‖f.r
estrict (Icc (x + R) (x + S))‖) =O[atTop] fun x : Real => |x| ^ (-b)
参数：Real, E；hb : 0 < b；hf : f =O[atTop] fun x : Real => |x| ^ (-b)；R S : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
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
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `Real.rpow_le_rpow_of_nonpos`：rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : 
x <= y) (hz : z <= 0) : y ^ z <= x ^ z
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
（共 110 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is `O(x ^ (-b))` at infinity, then so is the function
`fun x ↦ ‖f.restrict (Icc (x + R) (x + S))‖` for any fixed `R` and `S`.
-/
theorem isBigO_norm_Icc_restrict_atTop {f : C(ℝ, E)} {b : ℝ} (hb : 0 < b)
    (hf : f =O[atTop] fun x : ℝ => |x| ^ (-b)) (R S : ℝ) :
    (fun x : ℝ => ‖f.restrict (Icc (x + R) (x + S))‖) =O[atTop] fun x : ℝ => |x| ^ (-b) := by
  -- First establish an explicit estimate on decay of inverse powers.
  -- This is logically independent of the rest of the proof, but of no mathematical interest in
  -- itself, so it is proved in-line rather than being formulated as a separate lemma.
  have claim : ∀ x : ℝ, max 0 (-2 * R) < x → ∀ y : ℝ, x + R ≤ y →
      y ^ (-b) ≤ (1 / 2) ^ (-b) * x ^ (-b) := fun x hx y hy ↦ by
    rw [max_lt_iff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [← mul_rpow] <;> try positivity
    apply rpow_le_rpow_of_nonpos <;> linarith
  -- Now the main proof.
  obtain ⟨c, hc, hc'⟩ := hf.exists_pos
  simp only [IsBigO, IsBigOWith, eventually_atTop] at hc' ⊢
  obtain ⟨d, hd⟩ := hc'
  refine ⟨c * (1 / 2) ^ (-b), ⟨max (1 + max 0 (-2 * R)) (d - R), fun x hx => ?_⟩⟩
  rw [max_le_iff] at hx
  have hx' : max 0 (-2 * R) < x := by linarith
  rw [max_lt_iff] at hx'
  rw [norm_norm, ContinuousMap.norm_le _ (by positivity)]
  refine fun y => (hd y.1 (by linarith [hx.1, y.2.1])).trans ?_
  have A : ∀ x : ℝ, 0 ≤ |x| ^ (-b) := fun x => by positivity
  rw [mul_assoc, mul_le_mul_iff_right₀ hc, norm_of_nonneg (A _), norm_of_nonneg (A _)]
  convert! claim x (by linarith only [hx.1]) y.1 y.2.1
  · apply abs_of_nonneg; linarith [y.2.1]
  · exact abs_of_pos hx'.1
/-
**isBigO_norm_Icc_restrict_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBigO_norm_Icc_restrict_atBot {f : C(Real, E)} {b : Real} (hb : 0 < b) (h
f : f =O[atBot] fun x : Real => |x| ^ (-b)) (R S : Real) : (fun x : Real => ‖f.r
estrict (Icc (x + R) (x + S))‖) =O[atBot] fun x : Real => |x| ^ (-b)
参数：Real, E；hb : 0 < b；hf : f =O[atBot] fun x : Real => |x| ^ (-b)；R S : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousNeg.continuous_neg`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Neg G} [self : ContinuousNeg G], Continuous fun a => -a
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `isBigO_norm_Icc_restrict_atTop`：isBigO_norm_Icc_restrict_atTop {f : C(Re
al, E)} {b : Real} (hb : 0 < b) (hf : f =O[atTop] fun x : Real => |x| ^ (-b)) (R
 S : Real) : (fun x …
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.isBigO_of_le`：isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) 
: f =O[l] g
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `ContinuousMap.norm_le`：norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <
= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ContinuousMap.restrict_apply_mk`：restrict_apply_mk (f : C(α, β)) (s : Se
t α) (x : α) (hx : x in s) : f.restrict s ⟨x, hx⟩ = f x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
（共 64 条，此处仅展示前 30 条）
-/
theorem isBigO_norm_Icc_restrict_atBot {f : C(ℝ, E)} {b : ℝ} (hb : 0 < b)
    (hf : f =O[atBot] fun x : ℝ => |x| ^ (-b)) (R S : ℝ) :
    (fun x : ℝ => ‖f.restrict (Icc (x + R) (x + S))‖) =O[atBot] fun x : ℝ => |x| ^ (-b) := by
  have h1 : (f.comp (ContinuousMap.mk _ continuous_neg)) =O[atTop] fun x : ℝ => |x| ^ (-b) := by
    convert! hf.comp_tendsto tendsto_neg_atTop_atBot using 1
    ext1 x; simp only [Function.comp_apply, abs_neg]
  have h2 := (isBigO_norm_Icc_restrict_atTop hb h1 (-S) (-R)).comp_tendsto tendsto_neg_atBot_atTop
  have : (fun x : ℝ => |x| ^ (-b)) ∘ Neg.neg = fun x : ℝ => |x| ^ (-b) := by
    ext1 x; simp only [Function.comp_apply, abs_neg]
  rw [this] at h2
  refine (isBigO_of_le _ fun x => ?_).trans h2
  -- equality holds, but less work to prove `≤` alone
  rw [norm_norm, Function.comp_apply, norm_norm, ContinuousMap.norm_le _ (norm_nonneg _)]
  rintro ⟨x, hx⟩
  rw [ContinuousMap.restrict_apply_mk]
  refine (le_of_eq ?_).trans (ContinuousMap.norm_coe_le_norm _ ⟨-x, ?_⟩)
  · rw [ContinuousMap.restrict_apply_mk, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      ContinuousMap.coe_mk, neg_neg]
  · exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
/-
**isBigO_norm_restrict_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBigO_norm_restrict_cocompact (f : C(Real, E)) {b : Real} (hb : 0 < b) (h
f : f =O[cocompact Real] fun x : Real => |x| ^ (-b)) (K : Compacts Real) : (fun 
x => ‖(f.comp (ContinuousMap.addRight x)).restrict K‖) =O[cocompact Real] (|·| ^
 (-b))
参数：f : C(Real, E)；hb : 0 < b；hf : f =O[cocompact Real] fun x : Real => |x| ^ (-b
)；K : Compacts Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.instCompactSpaceElemCoeCompacts`：∀ {X : Type u_4} [inst : 
TopologicalSpace X] (K : TopologicalSpace.Compacts X), CompactSpace ↑↑K
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `Bornology.IsBounded.subset_closedBall`：∀ {α : Type u} {s : Set α} [inst 
: PseudoMetricSpace α],   Bornology.IsBounded s → ∀ (c : α), ∃ r, s ⊆ Metric.clo
sedBall c r
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.norm_le`：norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <
= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
（共 69 条，此处仅展示前 30 条）
-/
theorem isBigO_norm_restrict_cocompact (f : C(ℝ, E)) {b : ℝ} (hb : 0 < b)
    (hf : f =O[cocompact ℝ] fun x : ℝ => |x| ^ (-b)) (K : Compacts ℝ) :
    (fun x => ‖(f.comp (ContinuousMap.addRight x)).restrict K‖) =O[cocompact ℝ] (|·| ^ (-b)) := by
  obtain ⟨r, hr⟩ := K.isCompact.isBounded.subset_closedBall 0
  rw [closedBall_eq_Icc, zero_add, zero_sub] at hr
  have : ∀ x : ℝ,
      ‖(f.comp (ContinuousMap.addRight x)).restrict K‖ ≤ ‖f.restrict (Icc (x - r) (x + r))‖ := by
    intro x
    rw [ContinuousMap.norm_le _ (norm_nonneg _)]
    rintro ⟨y, hy⟩
    refine (le_of_eq ?_).trans (ContinuousMap.norm_coe_le_norm _ ⟨y + x, ?_⟩)
    · simp_rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight]
    · exact ⟨by linarith [(hr hy).1], by linarith [(hr hy).2]⟩
  simp_rw [cocompact_eq_atBot_atTop, isBigO_sup] at hf ⊢
  constructor
  · refine (isBigO_of_le atBot ?_).trans (isBigO_norm_Icc_restrict_atBot hb hf.1 (-r) r)
    simp_rw [norm_norm]; exact this
  · refine (isBigO_of_le atTop ?_).trans (isBigO_norm_Icc_restrict_atTop hb hf.2 (-r) r)
    simp_rw [norm_norm]; exact this

/-- **Poisson's summation formula**, assuming that `f` decays as
`|x| ^ (-b)` for some `1 < b` and its Fourier transform is summable. -/
/-
**Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable {f : Real -> Complex} 
(hc : Continuous f) {b : Real} (hb : 1 < b) (hf : IsBigO (cocompact Real) f fun 
x : Real => |x| ^ (-b)) (hFf : Summable fun n : Int => 𝓕 f n) (x : Real) : ∑' n 
: Int, f (x + n) = ∑' n : Int, 𝓕 f n * fourier n (x : UnitAddCircle)
参数：hc : Continuous f；hb : 1 < b；hf : IsBigO (cocompact Real) f fun x : Real => |
x| ^ (-b)；hFf : Summable fun n : Int => 𝓕 f n；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.tsum_eq_tsum_fourier`：Real.tsum_eq_tsum_fourier {f : C(Real, Comple
x)} (h_norm : forall K : Compacts Real, Summable fun n : Int => ‖(f.comp <| Cont
inuousMap.addRi…
· 使用定理 `summable_of_isBigO`：summable_of_isBigO {ι E} [SeminormedAddCommGroup E] 
[CompleteSpace E] {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : f =O[cofin
ite] g) …
· 使用定理 `ContinuousMap.instCompactSpaceElemCoeCompacts`：∀ {X : Type u_4} [inst : 
TopologicalSpace X] (K : TopologicalSpace.Compacts X), CompactSpace ↑↑K
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
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
· 使用定理 `Real.summable_abs_int_rpow`：summable_abs_int_rpow {b : Real} (hb : 1 < b
) : Summable fun n : Int => |(n : Real)| ^ (-b)
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `isBigO_norm_restrict_cocompact`：isBigO_norm_restrict_cocompact (f : C(Re
al, E)) {b : Real} (hb : 0 < b) (hf : f =O[cocompact Real] fun x : Real => |x| ^
 (-b)) (K : Compacts…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.tendsto_coe_cofinite`：tendsto_coe_cofinite : Tendsto ((↑) : Int -> R
eal) cofinite (cocompact Real)

--- 原说明 ---
**Poisson's summation formula**, assuming that `f` decays as
`|x| ^ (-b)` for some `1 < b` and its Fourier transform is summable.
-/
theorem Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable {f : ℝ → ℂ} (hc : Continuous f)
    {b : ℝ} (hb : 1 < b) (hf : IsBigO (cocompact ℝ) f fun x : ℝ => |x| ^ (-b))
    (hFf : Summable fun n : ℤ => 𝓕 f n) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) :=
  Real.tsum_eq_tsum_fourier (fun K => summable_of_isBigO (Real.summable_abs_int_rpow hb)
    ((isBigO_norm_restrict_cocompact ⟨_, hc⟩ (zero_lt_one.trans hb) hf K).comp_tendsto
    Int.tendsto_coe_cofinite)) hFf x

/-- **Poisson's summation formula**, assuming that both `f` and its Fourier transform decay as
`|x| ^ (-b)` for some `1 < b`. (This is the one-dimensional case of Corollary VII.2.6 of Stein and
Weiss, *Introduction to Fourier analysis on Euclidean spaces*.) -/
/-
**Real.tsum_eq_tsum_fourier_of_rpow_decay** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.tsum_eq_tsum_fourier_of_rpow_decay {f : Real -> Complex} (hc : Contin
uous f) {b : Real} (hb : 1 < b) (hf : f =O[cocompact Real] (|·| ^ (-b))) (hFf : 
(𝓕 f) =O[cocompact Real] (|·| ^ (-b))) (x : Real) : ∑' n : Int, f (x + n) = ∑' n
 : Int, 𝓕 f n * fourier n (x : UnitAddCircle)
参数：hc : Continuous f；hb : 1 < b；hf : f =O[cocompact Real] (|·| ^ (-b))；hFf : (𝓕 
f) =O[cocompact Real] (|·| ^ (-b))；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`：Real.tsum_eq_tsum_f
ourier_of_rpow_decay_of_summable {f : Real -> Complex} (hc : Continuous f) {b : 
Real} (hb : 1 < b) (hf : IsBigO (cocompac…
· 使用定理 `summable_of_isBigO`：summable_of_isBigO {ι E} [SeminormedAddCommGroup E] 
[CompleteSpace E] {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : f =O[cofin
ite] g) …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Real.summable_abs_int_rpow`：summable_abs_int_rpow {b : Real} (hb : 1 < b
) : Summable fun n : Int => |(n : Real)| ^ (-b)
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Int.tendsto_coe_cofinite`：tendsto_coe_cofinite : Tendsto ((↑) : Int -> R
eal) cofinite (cocompact Real)

--- 原说明 ---
**Poisson's summation formula**, assuming that both `f` and its Fourier transfor
m decay as
`|x| ^ (-b)` for some `1 < b`. (This is the one-dimensional case of Corollary VI
I.2.6 of Stein and
Weiss, *Introduction to Fourier analysis on Euclidean spaces*.)
-/
theorem Real.tsum_eq_tsum_fourier_of_rpow_decay {f : ℝ → ℂ} (hc : Continuous f) {b : ℝ}
    (hb : 1 < b) (hf : f =O[cocompact ℝ] (|·| ^ (-b)))
    (hFf : (𝓕 f) =O[cocompact ℝ] (|·| ^ (-b))) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) :=
  Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc hb hf (summable_of_isBigO
    (Real.summable_abs_int_rpow hb) (hFf.comp_tendsto Int.tendsto_coe_cofinite)) x

end RpowDecay

section Schwartz

open scoped SchwartzMap

/-- **Poisson's summation formula** for Schwartz functions. -/
/-
**SchwartzMap.tsum_eq_tsum_fourier** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SchwartzMap.tsum_eq_tsum_fourier (f : 𝓢(Real, Complex)) (x : Real) : ∑' n 
: Int, f (x + n) = ∑' n : Int, 𝓕 f n * fourier n (x : UnitAddCircle)
参数：f : 𝓢(Real, Complex)；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.tsum_eq_tsum_fourier_of_rpow_decay`：Real.tsum_eq_tsum_fourier_of_rp
ow_decay {f : Real -> Complex} (hc : Continuous f) {b : Real} (hb : 1 < b) (hf :
 f =O[cocompact Real] (|·| ^ …
· 使用定理 `SchwartzMap.continuous`：∀ {E : Type u_5} {F : Type u_6} [inst : NormedAd
dCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : NormedAddCommGroup F]   [inst
_3 : NormedS…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `SchwartzMap.isBigO_cocompact_rpow`：isBigO_cocompact_rpow [ProperSpace E]
 (s : Real) : f =O[cocompact E] (‖·‖ ^ s)
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ

--- 原说明 ---
**Poisson's summation formula** for Schwartz functions.
-/
theorem SchwartzMap.tsum_eq_tsum_fourier (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) := by
  -- We know that Schwartz functions are `O(‖x ^ (-b)‖)` for *every* `b`; for this argument we take
  -- `b = 2` and work with that.
  apply Real.tsum_eq_tsum_fourier_of_rpow_decay f.continuous one_lt_two
    (f.isBigO_cocompact_rpow (-2)) ((𝓕 f).isBigO_cocompact_rpow (-2))

end Schwartz

