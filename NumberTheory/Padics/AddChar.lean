/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis
public import Mathlib.Topology.Algebra.Monoid.AddChar
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Additive characters of `ℤ_[p]`

We show that for any complete, ultrametric normed `ℤ_[p]`-algebra `R`, there is a bijection between
continuous additive characters `ℤ_[p] → R` and topologically nilpotent elements of `R`, given by
sending `κ` to the element `κ 1 - 1`. This is used to define the Mahler transform for `p`-adic
measures.

Note that if the norm on `R` is not strictly multiplicative, then the condition that `κ 1 - 1` be
topologically nilpotent is strictly weaker than assuming `‖κ 1 - 1‖ < 1`, although they are
equivalent if `NormMulClass R` holds.

## Main definitions and theorems:

* `addChar_of_value_at_one`: given a topologically nilpotent `r : R`, construct a continuous
  additive character of `ℤ_[p]` mapping `1` to `1 + r`.
* `continuousAddCharEquiv`: for any complete, ultrametric normed `ℤ_[p]`-algebra `R`, the map
  `addChar_of_value_at_one` defines a bijection between continuous additive characters `ℤ_[p] → R`
  and topologically nilpotent elements of `R`.
* `continuousAddCharEquiv_of_norm_mul`: if the norm on `R` is strictly multiplicative (not just
  sub-multiplicative), then `addChar_of_value_at_one` is a bijection between continuous additive
  characters `ℤ_[p] → R` and elements of `R` with `‖r‖ < 1`.

## TODO:

* Show that the above equivalences are homeomorphisms, for appropriate choices of the topology.
-/

@[expose] public section

open scoped fwdDiff
open Filter Topology

variable {p : ℕ} [Fact p.Prime]

variable {R : Type*} [NormedRing R] [Algebra ℤ_[p] R] [IsBoundedSMul ℤ_[p] R]
  [IsUltrametricDist R]

/-
**AddChar.tendsto_eval_one_sub_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddChar.tendsto_eval_one_sub_pow {κ : AddChar Int_[p] R} (hκ : Continuous 
κ) : Tendsto (fun n => (κ 1 - 1) ^ n) atTop (𝓝 0)
参数：hκ : Continuous κ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `fwdDiff_addChar_eq`：fwdDiff_addChar_eq {M R : Type*} [AddCommMonoid M] [
Ring R] (φ : AddChar M R) (x h : M) (n : Nat) : Δ_[h]^[n] φ x = (φ h - 1) ^ n * 
φ x
· 使用引理 `PadicInt.fwdDiff_tendsto_zero`：fwdDiff_tendsto_zero (f : C(Int_[p], E)) 
: Tendsto (Δ_[1]^[·] f 0) atTop (𝓝 0)
-/
lemma AddChar.tendsto_eval_one_sub_pow {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) :
    Tendsto (fun n ↦ (κ 1 - 1) ^ n) atTop (𝓝 0) := by
  refine (PadicInt.fwdDiff_tendsto_zero ⟨κ, hκ⟩).congr fun n ↦ ?_
  simpa only [AddChar.map_zero_eq_one, mul_one] using! fwdDiff_addChar_eq κ 0 1 n

namespace PadicInt
variable [CompleteSpace R]

/-- The unique continuous additive character of `ℤ_[p]` mapping `1` to `1 + r`. -/
/-
**PadicInt.addChar_of_value_at_one** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：addChar_of_value_at_one (r : R) (hr : Tendsto (r ^ ·) atTop (𝓝 0)) : AddCh
ar Int_[p] R where toFun
参数：r : R；hr : Tendsto (r ^ ·) atTop (𝓝 0)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique continuous additive character of `ℤ_[p]` mapping `1` to `1 + r`.
-/
noncomputable def addChar_of_value_at_one (r : R) (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    AddChar ℤ_[p] R where
  toFun := mahlerSeries (r ^ ·)
  map_zero_eq_one' := by
    rw [← Nat.cast_zero, mahlerSeries_apply_nat hr le_rfl, zero_add, Finset.sum_range_one,
      Nat.choose_self, pow_zero, one_smul]
  map_add_eq_mul' a b := by
    let F : C(ℤ_[p], R) := mahlerSeries (r ^ ·)
    change F (a + b) = F a * F b
    -- It is fiddly to show directly that `F (a + b) = F a * F b` for general `a, b`,
    -- so we prove it for `a, b ∈ ℕ` directly, and then deduce it for all `a, b` by continuity.
    have hF (n : ℕ) : F n = (r + 1) ^ n := by
      rw [mahlerSeries_apply_nat hr le_rfl, (Commute.one_right _).add_pow]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [one_pow, mul_one, nsmul_eq_mul, Nat.cast_comm]
    refine congr_fun ((denseRange_natCast.prodMap denseRange_natCast).equalizer
      ((map_continuous F).comp continuous_add)
      (continuous_mul.comp (map_continuous <| F.prodMap F)) (funext fun ⟨m, n⟩ ↦ ?_)) (a, b)
    simp [← Nat.cast_add, hF, ContinuousMap.prodMap_apply, pow_add]

@[fun_prop]
/-
**PadicInt.continuous_addChar_of_value_at_one** 是 Mathlib 中的一个引理，位于命名空间 `PadicIn
t`。
形式化陈述：continuous_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 
0)) : Continuous (addChar_of_value_at_one r hr : Int_[p] -> R)
参数：hr : Tendsto (r ^ ·) atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
-/
lemma continuous_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    Continuous (addChar_of_value_at_one r hr : ℤ_[p] → R) :=
  map_continuous (mahlerSeries (r ^ ·))
/-
**PadicInt.coe_addChar_of_value_at_one** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：coe_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) : (
addChar_of_value_at_one r hr : Int_[p] -> R) = mahlerSeries (r ^ ·)
参数：hr : Tendsto (r ^ ·) atTop (𝓝 0)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    (addChar_of_value_at_one r hr : ℤ_[p] → R) = mahlerSeries (r ^ ·) :=
  rfl

@[simp]
/-
**PadicInt.addChar_of_value_at_one_def** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：addChar_of_value_at_one_def {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) : a
ddChar_of_value_at_one r hr (1 : Int_[p]) = 1 + r
参数：hr : Tendsto (r ^ ·) atTop (𝓝 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PadicInt.mahlerSeries_apply_nat`：mahlerSeries_apply_nat (ha : Tendsto a 
atTop (𝓝 0)) {m n : Nat} (hmn : m <= n) : mahlerSeries a (m : Int_[p]) = ∑ i in 
range (n + 1), m.choo…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Finset.sum_range_one`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M), ∑ k ∈ Finset.range 1, f k = f 0
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma addChar_of_value_at_one_def {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    addChar_of_value_at_one r hr (1 : ℤ_[p]) = 1 + r := by
  change mahlerSeries (r ^ ·) ↑(1 : ℕ) = _
  rw [mahlerSeries_apply_nat hr le_rfl, Finset.sum_range_succ, Finset.sum_range_one,
    Nat.choose_zero_right, Nat.choose_self, one_smul, one_smul, pow_zero, pow_one]
/-
**PadicInt.eq_addChar_of_value_at_one** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：eq_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) {κ :
 AddChar Int_[p] R} (hκ : Continuous κ) (hκ' : κ 1 = 1 + r) : κ = addChar_of_val
ue_at_one r hr
参数：hr : Tendsto (r ^ ·) atTop (𝓝 0)；hκ : Continuous κ；hκ' : κ 1 = 1 + r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DenseRange.addChar_eq_of_eval_one_eq`：DenseRange.addChar_eq_of_eval_one_
eq {A M : Type*} [TopologicalSpace A] [AddMonoidWithOne A] [Monoid M] [Topologic
alSpace M] [T2Space M] (hd…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `PadicInt.denseRange_natCast`：denseRange_natCast : DenseRange (Nat.cast :
 Nat -> Int_[p])
· 使用引理 `PadicInt.continuous_addChar_of_value_at_one`：continuous_addChar_of_value
_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) : Continuous (addChar_of_valu
e_at_one r hr : Int_[p] -> R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PadicInt.addChar_of_value_at_one_def`：addChar_of_value_at_one_def {r : R
} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) : addChar_of_value_at_one r hr (1 : Int_[p]
) = 1 + r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eq_addChar_of_value_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0))
    {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) (hκ' : κ 1 = 1 + r) :
    κ = addChar_of_value_at_one r hr :=
  denseRange_natCast.addChar_eq_of_eval_one_eq hκ (by fun_prop) (by simp [hκ'])

variable (p R) in
/-- Equivalence between continuous additive characters `ℤ_[p] → R`, and `r ∈ R` with `r ^ n → 0`. -/
/-
**PadicInt.continuousAddCharEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：continuousAddCharEquiv : {κ : AddChar Int_[p] R // Continuous κ} ≃ {r : R 
// Tendsto (r ^ ·) atTop (𝓝 0)} where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AddChar.tendsto_eval_one_sub_pow`：AddChar.tendsto_eval_one_sub_pow {κ : 
AddChar Int_[p] R} (hκ : Continuous κ) : Tendsto (fun n => (κ 1 - 1) ^ n) atTop 
(𝓝 0)
· 使用引理 `PadicInt.continuous_addChar_of_value_at_one`：continuous_addChar_of_value
_at_one {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) : Continuous (addChar_of_valu
e_at_one r hr : Int_[p] -> R)

--- 原说明 ---
Equivalence between continuous additive characters `ℤ_[p] → R`, and `r ∈ R` with
 `r ^ n → 0`.
-/
noncomputable def continuousAddCharEquiv :
    {κ : AddChar ℤ_[p] R // Continuous κ} ≃ {r : R // Tendsto (r ^ ·) atTop (𝓝 0)} where
  toFun := fun ⟨κ, hκ⟩ ↦ ⟨κ 1 - 1, κ.tendsto_eval_one_sub_pow hκ⟩
  invFun := fun ⟨r, hr⟩ ↦ ⟨_, continuous_addChar_of_value_at_one hr⟩
  left_inv := fun ⟨κ, hκ⟩ ↦ by simpa using (eq_addChar_of_value_at_one _ hκ (by abel)).symm
  right_inv := fun ⟨r, hr⟩ ↦ by simp [addChar_of_value_at_one_def hr]
/-
**PadicInt.continuousAddCharEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : NormedRing 
R] [inst_2 : Algebra ℤ_[p] R]   [inst_3 : IsBoundedSMul ℤ_[p] R] [inst_4 : IsUlt
rametricDist R] [inst_5 : CompleteSpace R] {κ : AddChar ℤ_[p] R}   (hκ : Continu
ous ⇑κ), ↑((PadicInt.continuousAddCharEquiv p R) ⟨κ, hκ⟩) = κ 1 - 1
参数：Nat.Prime p；hκ : Continuous ⇑κ；(PadicInt.continuousAddCharEquiv p R) ⟨κ, hκ⟩。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma continuousAddCharEquiv_apply {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) :
    continuousAddCharEquiv p R ⟨κ, hκ⟩ = κ 1 - 1 :=
  rfl
/-
**PadicInt.continuousAddCharEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt
`。
形式化陈述：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : NormedRing 
R] [inst_2 : Algebra ℤ_[p] R]   [inst_3 : IsBoundedSMul ℤ_[p] R] [inst_4 : IsUlt
rametricDist R] [inst_5 : CompleteSpace R] {r : R}   (hr : Filter.Tendsto (fun x
 => r ^ x) Filter.atTop (nhds 0)),   ↑((PadicInt.continuousAddCharEquiv p R).sym
m ⟨r, hr⟩) = PadicInt.addChar_of_value_at_one r hr
参数：Nat.Prime p；hr : Filter.Tendsto (fun x => r ^ x) Filter.atTop (nhds 0)；(Padic
Int.continuousAddCharEquiv p R).symm ⟨r, hr⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma continuousAddCharEquiv_symm_apply {r : R} (hr : Tendsto (r ^ ·) atTop (𝓝 0)) :
    (continuousAddCharEquiv p R).symm ⟨r, hr⟩ =
    (addChar_of_value_at_one r hr : AddChar ℤ_[p] R) :=
  rfl

section NormMulClass
variable [NormMulClass R]

variable (p R) in
/-- Equivalence between continuous additive characters `ℤ_[p] → R`, and `r ∈ R` with `‖r‖ < 1`,
for rings with strictly multiplicative norm. -/
/-
**PadicInt.continuousAddCharEquiv_of_norm_mul** 是 Mathlib 中的一个定义，位于命名空间 `PadicIn
t`。
形式化陈述：continuousAddCharEquiv_of_norm_mul : {κ : AddChar Int_[p] R // Continuous 
κ} ≃ {r : R // ‖r‖ < 1}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Equivalence between continuous additive characters `ℤ_[p] → R`, and `r ∈ R` with
 `‖r‖ < 1`,
for rings with strictly multiplicative norm.
-/
noncomputable def continuousAddCharEquiv_of_norm_mul :
    {κ : AddChar ℤ_[p] R // Continuous κ} ≃ {r : R // ‖r‖ < 1} :=
  (continuousAddCharEquiv p R).trans <|
    .subtypeEquivProp (by simp only [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one])
/-
**PadicInt.continuousAddCharEquiv_of_norm_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `P
adicInt`。
形式化陈述：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : NormedRing 
R] [inst_2 : Algebra ℤ_[p] R]   [inst_3 : IsBoundedSMul ℤ_[p] R] [inst_4 : IsUlt
rametricDist R] [inst_5 : CompleteSpace R] [inst_6 : NormMulClass R]   {κ : AddC
har ℤ_[p] R} (hκ : Continuous ⇑κ), ↑((PadicInt.continuousAddCharEquiv_of_norm_mu
l p R) ⟨κ, hκ⟩) = κ 1 - 1
参数：Nat.Prime p；hκ : Continuous ⇑κ；(PadicInt.continuousAddCharEquiv_of_norm_mul p
 R) ⟨κ, hκ⟩。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma continuousAddCharEquiv_of_norm_mul_apply {κ : AddChar ℤ_[p] R} (hκ : Continuous κ) :
    continuousAddCharEquiv_of_norm_mul p R ⟨κ, hκ⟩ = κ 1 - 1 :=
  rfl
/-
**PadicInt.continuousAddCharEquiv_of_norm_mul_symm_apply** 是 Mathlib 中的一个定理，位于命名
空间 `PadicInt`。
形式化陈述：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : NormedRing 
R] [inst_2 : Algebra ℤ_[p] R]   [inst_3 : IsBoundedSMul ℤ_[p] R] [inst_4 : IsUlt
rametricDist R] [inst_5 : CompleteSpace R] [inst_6 : NormMulClass R]   {r : R} (
hr : ‖r‖ < 1),   ↑((PadicInt.continuousAddCharEquiv_of_norm_mul p R).symm ⟨r, hr
⟩) = PadicInt.addChar_of_value_at_one r ⋯
参数：Nat.Prime p；hr : ‖r‖ < 1；(PadicInt.continuousAddCharEquiv_of_norm_mul p R).sy
mm ⟨r, hr⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma continuousAddCharEquiv_of_norm_mul_symm_apply {r : R} (hr : ‖r‖ < 1) :
    (continuousAddCharEquiv_of_norm_mul p R).symm ⟨r, hr⟩ = (addChar_of_value_at_one r
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hr) : AddChar ℤ_[p] R) :=
  rfl

end NormMulClass

end PadicInt

