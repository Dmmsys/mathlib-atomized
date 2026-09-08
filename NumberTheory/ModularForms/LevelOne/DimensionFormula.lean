/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.CuspFormSubmodule
public import Mathlib.NumberTheory.ModularForms.Discriminant

import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Dimension formula and Sturm bound for level 1 modular forms

This file proves the dimension formula and the Sturm bound for the space of modular forms
for `𝒮ℒ` (= `SL(2, ℤ)`) of even weight.

## Main results

* `CuspForm.discriminantEquiv`: `CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12)`.
* `ModularForm.rank_eq_one_add_rank_cuspForm`: `rank M_k = 1 + rank S_k` for even `k ≥ 3`.
* `ModularForm.dimension_level_one`: the full dimension formula for all even `k : ℕ`.
* `ModularForm.levelOne_odd_weight_rank_zero`: modular forms of odd weight are zero.
* A `FiniteDimensional ℂ (ModularForm 𝒮ℒ k)` instance for every `k : ℤ`.
* `ModularForm.sturm_bound_levelOne`: a modular form `f : ModularForm 𝒮ℒ k` whose q-expansion
  has order strictly greater than `k / 12` is identically zero.
* `ModularForm.sturm_bound_levelOne_nat`: convenience version for `k : ℕ`.
-/

@[expose] public noncomputable section

open UpperHalfPlane ModularForm SlashInvariantForm SlashInvariantFormClass ModularFormClass
  CuspFormClass MatrixGroups OnePoint Filter EisensteinSeries Asymptotics

open scoped Topology

section DeltaIsomorphism

variable {k : ℤ}

local notation "Δ" => ModularForm.discriminant

namespace CuspForm

/-- Multiply a modular form of weight `k - 12` by the discriminant to get a cusp form of
weight `k`. Built directly as a `CuspForm` via `CuspForm.mulModularForm`. -/
/-
**CuspForm.ofMulDiscriminant** 是 Mathlib 中的一个定义，位于命名空间 `CuspForm`。
形式化陈述：ofMulDiscriminant (f : ModularForm 𝒮ℒ (k - 12)) : CuspForm 𝒮ℒ k
参数：f : ModularForm 𝒮ℒ (k - 12)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiply a modular form of weight `k - 12` by the discriminant to get a cusp for
m of
weight `k`. Built directly as a `CuspForm` via `CuspForm.mulModularForm`.
-/
def ofMulDiscriminant (f : ModularForm 𝒮ℒ (k - 12)) : CuspForm 𝒮ℒ k :=
  CuspForm.mcast (by ring) (CuspForm.discriminant.mulModularForm f)

@[simp]
/-
**CuspForm.ofMulDiscriminant_apply** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
形式化陈述：ofMulDiscriminant_apply (f : ModularForm 𝒮ℒ (k - 12)) (z : ℍ) : (ofMulDisc
riminant f) z = Δ z * f z
参数：f : ModularForm 𝒮ℒ (k - 12)；z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofMulDiscriminant_apply (f : ModularForm 𝒮ℒ (k - 12)) (z : ℍ) :
    (ofMulDiscriminant f) z = Δ z * f z := rfl
/-
**CuspForm.divByDiscriminant_slash_eq** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
形式化陈述：divByDiscriminant_slash_eq (f : CuspForm 𝒮ℒ k) (γ : SL(2, Int)) : (fun z =
> f z / Δ z) ∣[k - 12] γ = fun z => f z / Δ z
参数：f : CuspForm 𝒮ℒ k；γ : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModularForm.div_slash_SL2`：div_slash_SL2 (k1 k2 : Int) (A : SL(2, Int)) 
(f g : ℍ -> Complex) : (f / g) ∣[k1 - k2] A = f ∣[k1] A / g ∣[k2] A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SlashInvariantForm.slash_action_eqn`：slash_action_eqn [SlashInvariantFor
mClass F Γ k] (f : F) (γ) (hγ : γ in Γ) : ↑f ∣[k] γ = ⇑f
· 使用定理 `CuspFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outParam 
(Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane ℂ} 
  [self : CuspFormClass F Γ k…
· 使用定理 `CuspFormClass.cuspForm`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ), CuspFor
mClass (CuspForm Γ k) Γ k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma divByDiscriminant_slash_eq (f : CuspForm 𝒮ℒ k) (γ : SL(2, ℤ)) :
    (fun z ↦ f z / Δ z) ∣[k - 12] γ = fun z ↦ f z / Δ z := by
  have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
  change (⇑f / ⇑CuspForm.discriminant) ∣[k - 12] γ = ⇑f / ⇑CuspForm.discriminant
  simp_rw [div_slash_SL2, SL_slash, slash_action_eqn _ _ hγ]

/-- The linear equivalence between cusp forms of weight `k` and modular forms of weight `k - 12`,
given by division by the discriminant. -/
/-
**CuspForm.discriminantEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CuspForm`。
形式化陈述：discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[Complex] ModularForm 𝒮ℒ (k - 12) wher
e toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between cusp forms of weight `k` and modular forms of wei
ght `k - 12`,
given by division by the discriminant.
-/
def discriminantEquiv : CuspForm 𝒮ℒ k ≃ₗ[ℂ] ModularForm 𝒮ℒ (k - 12) where
  toFun f :=
    { toFun z := f z / Δ z
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ divByDiscriminant_slash_eq f γ
      holo' := f.holo'.div CuspForm.discriminant.holo' discriminant_ne_zero
      bdd_at_cusps' {c} hc := by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [divByDiscriminant_slash_eq f γ, IsBoundedAtImInfty, BoundedAtFilter]
        exact (div_isBoundedUnder_of_isBigO (exp_decay_isBigO_discriminant f)).isBigO_one ℝ }
  map_add' a b := by
    ext z
    change (a z + b z) / Δ z = a z / Δ z + b z / Δ z
    rw [add_div]
  map_smul' c a := by
    ext z
    change (c * a z) / Δ z = c * (a z / Δ z)
    rw [mul_div_assoc]
  invFun := ofMulDiscriminant
  left_inv f := by
    ext z
    exact mul_div_cancel₀ (f z) (discriminant_ne_zero z)
  right_inv f := by
    ext z
    exact mul_div_cancel_left₀ (f z) (discriminant_ne_zero z)
/-
**CuspForm.discriminantEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
形式化陈述：discriminantEquiv_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) : (discriminantEquiv f
) z = f z / Δ z
参数：f : CuspForm 𝒮ℒ k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
-/
lemma discriminantEquiv_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    (discriminantEquiv f) z = f z / Δ z := rfl

/-- Divide a cusp form by the discriminant to get a modular form of weight `k - 12`. -/
@[deprecated discriminantEquiv (since := "2026-05-18")]
/-
**CuspForm.divDiscriminant** 是 Mathlib 中的一个定义，位于命名空间 `CuspForm`。
形式化陈述：divDiscriminant (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k - 12)
参数：f : CuspForm 𝒮ℒ k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Divide a cusp form by the discriminant to get a modular form of weight `k - 12`.
-/
def divDiscriminant (f : CuspForm 𝒮ℒ k) : ModularForm 𝒮ℒ (k - 12) := discriminantEquiv f

@[deprecated discriminantEquiv_apply (since := "2026-05-18")]
/-
**CuspForm.divDiscriminant_apply** 是 Mathlib 中的一个引理，位于命名空间 `CuspForm`。
形式化陈述：divDiscriminant_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) : (divDiscriminant f) z 
= f z / Δ z
参数：f : CuspForm 𝒮ℒ k；z : ℍ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma divDiscriminant_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    (divDiscriminant f) z = f z / Δ z := rfl

end CuspForm

namespace ModularForm

@[simp]
/-
**ModularForm.discriminant_mul_discriminantEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间
 `ModularForm`。
形式化陈述：discriminant_mul_discriminantEquiv_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) : Δ z
 * (CuspForm.discriminantEquiv f) z = f z
参数：f : CuspForm 𝒮ℒ k；z : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CuspForm.discriminantEquiv_apply`：discriminantEquiv_apply (f : CuspForm 
𝒮ℒ k) (z : ℍ) : (discriminantEquiv f) z = f z / Δ z
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用引理 `ModularForm.discriminant_ne_zero`：discriminant_ne_zero (z : ℍ) : Δ z != 
0
-/
lemma discriminant_mul_discriminantEquiv_apply (f : CuspForm 𝒮ℒ k) (z : ℍ) :
    Δ z * (CuspForm.discriminantEquiv f) z = f z := by
  rw [CuspForm.discriminantEquiv_apply, mul_div_cancel₀ _ (discriminant_ne_zero z)]

@[simp]
/-
**ModularForm.discriminant_mul_discriminantEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Modu
larForm`。
形式化陈述：discriminant_mul_discriminantEquiv (f : CuspForm 𝒮ℒ k) : Δ * (CuspForm.dis
criminantEquiv f : ℍ -> Complex) = f
参数：f : CuspForm 𝒮ℒ k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma discriminant_mul_discriminantEquiv (f : CuspForm 𝒮ℒ k) :
    Δ * (CuspForm.discriminantEquiv f : ℍ → ℂ) = f := by
  grind [Pi.mul_apply, discriminant_mul_discriminantEquiv_apply]

/-- The order of the q-expansion of the modular discriminant is 1: the zeroth coefficient
vanishes (Δ is a cusp form) and the first coefficient equals 1. -/
/-
**ModularForm.discriminant_qExpansion_order** 是 Mathlib 中的一个引理，位于命名空间 `ModularFo
rm`。
形式化陈述：discriminant_qExpansion_order : (qExpansion 1 Δ).order = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PowerSeries.order_eq_nat`：order_eq_nat {φ : R⟦X⟧} {n : Nat} : order φ = 
n ↔ coeff n φ != 0 ∧ forall i, i < n -> coeff i φ = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModularForm.discriminant_qExpansion_coeff_one`：discriminant_qExpansion_c
oeff_one : (qExpansion 1 Δ).coeff 1 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `CuspFormClass.qExpansion_coeff_zero`：∀ {k : ℤ} {F : Type u_1} [inst : Fu
nLike F UpperHalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F)   [CuspF
ormClass F Γ k], 0 < h → …
· 使用定理 `CuspFormClass.cuspForm`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ), CuspFor
mClass (CuspForm Γ k) Γ k
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `one_mem_strictPeriods_SL`：one_mem_strictPeriods_SL : (1 : Real) in (𝒮ℒ).
strictPeriods

--- 原说明 ---
The order of the q-expansion of the modular discriminant is 1: the zeroth coeffi
cient
vanishes (Δ is a cusp form) and the first coefficient equals 1.
-/
lemma discriminant_qExpansion_order : (qExpansion 1 Δ).order = 1 := by
  refine PowerSeries.order_eq_nat.mpr
    ⟨discriminant_qExpansion_coeff_one ▸ one_ne_zero, fun i hi ↦ ?_⟩
  obtain rfl : i = 0 := by lia
  simpa using CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

/-- The q-expansion of a level-1 modular form whose zeroth coefficient vanishes factors as
the q-expansion of `Δ` times the q-expansion of the corresponding form of weight `k - 12`
obtained via `discriminantEquiv`. -/
/-
**ModularForm.qExpansion_eq_qExpansion_discriminant_mul** 是 Mathlib 中的一个引理，位于命名空
间 `ModularForm`。
形式化陈述：qExpansion_eq_qExpansion_discriminant_mul (f : ModularForm 𝒮ℒ k) (hcusp : 
(qExpansion 1 f).coeff 0 = 0) : qExpansion 1 f = qExpansion 1 discriminant * qEx
pansion 1 (CuspForm.discriminantEquiv (toCuspForm f hcusp))
参数：f : ModularForm 𝒮ℒ k；hcusp : (qExpansion 1 f).coeff 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModularForm.discriminant_mul_discriminantEquiv`：discriminant_mul_discrim
inantEquiv (f : CuspForm 𝒮ℒ k) : Δ * (CuspForm.discriminantEquiv f : ℍ -> Comple
x) = f
· 使用引理 `CuspForm.coe_discriminant`：coe_discriminant : discriminant = Δ
· 使用定理 `ModularForm.qExpansion_mul_coe`：∀ {F : Type u_1} [inst : FunLike F Upper
HalfPlane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} {G : Type u_2}   [inst_1 : Fu
nLike G UpperHalfPla…
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `one_mem_strictPeriods_SL`：one_mem_strictPeriods_SL : (1 : Real) in (𝒮ℒ).
strictPeriods
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k
· 使用定理 `CuspFormClass.cuspForm`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ), CuspFor
mClass (CuspForm Γ k) Γ k
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k

--- 原说明 ---
The q-expansion of a level-1 modular form whose zeroth coefficient vanishes fact
ors as
the q-expansion of `Δ` times the q-expansion of the corresponding form of weight
 `k - 12`
obtained via `discriminantEquiv`.
-/
lemma qExpansion_eq_qExpansion_discriminant_mul (f : ModularForm 𝒮ℒ k)
    (hcusp : (qExpansion 1 f).coeff 0 = 0) :
    qExpansion 1 f = qExpansion 1 discriminant *
      qExpansion 1 (CuspForm.discriminantEquiv (toCuspForm f hcusp)) := by
  rw [show (f : ℍ → ℂ) = discriminant * (toCuspForm f hcusp).discriminantEquiv from
      (discriminant_mul_discriminantEquiv (toCuspForm f hcusp)).symm, ← CuspForm.coe_discriminant]
  exact ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_SL _ _

end ModularForm

end DeltaIsomorphism

section RankIdentity

variable {k : ℤ}

/-- A `𝒮ℒ` modular form of odd weight is zero (evaluate at `-1 ∈ SL(2, ℤ)`). -/
/-
**ModularForm.levelOne_odd_weight_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.levelOne_odd_weight_eq_zero (hk : Odd k) (f : ModularForm 𝒮ℒ k
) : f = 0
参数：hk : Odd k；f : ModularForm 𝒮ℒ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModularForm.eq_zero_of_neg_one_mem`：eq_zero_of_neg_one_mem [Γ.HasDetOne]
 (h_neg_one : -1 in Γ) (hk : Odd k) (f : ModularForm Γ k) : f = 0
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.SpecialLinearGroup.coe_int_neg`：coe_int_neg (g : SpecialLinearGro
up n Int) : ↑(-g) = (-↑g : SpecialLinearGroup n R)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A `𝒮ℒ` modular form of odd weight is zero (evaluate at `-1 ∈ SL(2, ℤ)`).
-/
lemma ModularForm.levelOne_odd_weight_eq_zero (hk : Odd k) (f : ModularForm 𝒮ℒ k) : f = 0 :=
  ModularForm.eq_zero_of_neg_one_mem (show (-1 : GL (Fin 2) ℝ) ∈ 𝒮ℒ from ⟨-1, by ext; simp⟩) hk f

/-- Modular forms of odd weight for `𝒮ℒ` are zero-dimensional. -/
/-
**ModularForm.levelOne_odd_weight_rank_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.levelOne_odd_weight_rank_zero (hk : Odd k) : Module.rank Compl
ex (ModularForm 𝒮ℒ k) = 0
参数：hk : Odd k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `rank_zero_iff_forall_zero`：rank_zero_iff_forall_zero : Module.rank R M =
 0 ↔ forall x : M, x = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `ModularForm.levelOne_odd_weight_eq_zero`：ModularForm.levelOne_odd_weight
_eq_zero (hk : Odd k) (f : ModularForm 𝒮ℒ k) : f = 0

--- 原说明 ---
Modular forms of odd weight for `𝒮ℒ` are zero-dimensional.
-/
lemma ModularForm.levelOne_odd_weight_rank_zero (hk : Odd k) :
    Module.rank ℂ (ModularForm 𝒮ℒ k) = 0 :=
  rank_zero_iff_forall_zero.mpr (levelOne_odd_weight_eq_zero hk)

/-- Cusp forms of weight `k < 12` for `𝒮ℒ` are zero-dimensional. -/
/-
**CuspForm.rank_eq_zero_of_weight_lt_twelve** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CuspForm.rank_eq_zero_of_weight_lt_twelve (hk : k < 12) : Module.rank Comp
lex (CuspForm 𝒮ℒ k) = 0
参数：hk : k < 12。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用引理 `ModularForm.levelOne_neg_weight_rank_zero`：ModularForm.levelOne_neg_weig
ht_rank_zero (hk : k < 0) : Module.rank Complex (ModularForm 𝒮ℒ k) = 0

--- 原说明 ---
Cusp forms of weight `k < 12` for `𝒮ℒ` are zero-dimensional.
-/
lemma CuspForm.rank_eq_zero_of_weight_lt_twelve (hk : k < 12) :
    Module.rank ℂ (CuspForm 𝒮ℒ k) = 0 :=
  CuspForm.discriminantEquiv.rank_eq.trans (levelOne_neg_weight_rank_zero (by lia))

/-- The space of weight 12 cusp forms for `𝒮ℒ` has rank 1. -/
/-
**CuspForm.rank_eq_one_of_weight_eq_twelve** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CuspForm.rank_eq_one_of_weight_eq_twelve : Module.rank Complex (CuspForm 𝒮
ℒ 12) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用引理 `ModularForm.levelOne_weight_zero_rank_one`：ModularForm.levelOne_weight_z
ero_rank_one : Module.rank Complex (ModularForm 𝒮ℒ 0) = 1

--- 原说明 ---
The space of weight 12 cusp forms for `𝒮ℒ` has rank 1.
-/
lemma CuspForm.rank_eq_one_of_weight_eq_twelve : Module.rank ℂ (CuspForm 𝒮ℒ 12) = 1 := by
  simpa [CuspForm.discriminantEquiv.rank_eq] using! levelOne_weight_zero_rank_one

/-- Every weight 12 cusp form for `𝒮ℒ` is a scalar multiple of the discriminant. -/
/-
**CuspForm.exists_smul_discriminant_of_weight_eq_twelve** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：CuspForm.exists_smul_discriminant_of_weight_eq_twelve (f : CuspForm 𝒮ℒ 12)
 : exists c : Complex, c • CuspForm.discriminant = f
参数：f : CuspForm 𝒮ℒ 12。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `finrank_eq_one_iff_of_nonzero'`：finrank_eq_one_iff_of_nonzero' (v : V) (
nz : v != 0) : finrank K V = 1 ↔ forall w : V, exists c : K, c • v = w
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DFunLike.ne_iff`：ne_iff {f g : F} : f != g ↔ exists a, f a != g a
· 使用引理 `ModularForm.discriminant_ne_zero`：discriminant_ne_zero (z : ℍ) : Δ z != 
0
· 使用引理 `Module.rank_eq_one_iff_finrank_eq_one`：rank_eq_one_iff_finrank_eq_one : 
Module.rank R M = 1 ↔ finrank R M = 1
· 使用引理 `CuspForm.rank_eq_one_of_weight_eq_twelve`：CuspForm.rank_eq_one_of_weight
_eq_twelve : Module.rank Complex (CuspForm 𝒮ℒ 12) = 1

--- 原说明 ---
Every weight 12 cusp form for `𝒮ℒ` is a scalar multiple of the discriminant.
-/
lemma CuspForm.exists_smul_discriminant_of_weight_eq_twelve (f : CuspForm 𝒮ℒ 12) :
    ∃ c : ℂ, c • CuspForm.discriminant = f :=
  (finrank_eq_one_iff_of_nonzero' _ (DFunLike.ne_iff.mpr ⟨I, discriminant_ne_zero _⟩)).mp
    (Module.rank_eq_one_iff_finrank_eq_one.mp CuspForm.rank_eq_one_of_weight_eq_twelve) f

/-- For even `k ≥ 3`, the rank of `𝒮ℒ` modular forms is one more than the rank of
cusp forms. -/
/-
**ModularForm.rank_eq_one_add_rank_cuspForm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.rank_eq_one_add_rank_cuspForm {k : Nat} (hk : 3 <= k) (hk2 : E
ven k) : Module.rank Complex (ModularForm 𝒮ℒ k) = 1 + Module.rank Complex (CuspF
orm 𝒮ℒ k)
参数：hk : 3 <= k；hk2 : Even k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `rank_eq_one`：rank_eq_one (v : M) (n : v != 0) (h : forall w : M, exists 
c : R, c • v = w) : Module.rank R M = 1
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用引理 `EisensteinSeries.E_qExpansion_coeff_zero`：EisensteinSeries.E_qExpansion_
coeff_zero {k : Nat} (hk : 3 <= k) (hk2 : Even k) : (qExpansion 1 (E hk)).coeff 
0 = 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ModularForm.isCuspForm_iff_coeffZero_eq_zero`：isCuspForm_iff_coeffZero_e
q_zero (f : ModularForm 𝒮ℒ k) : IsCuspForm f ↔ (qExpansion 1 f).coeff 0 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.forall`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring 
R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) 
{P : M ⧸ p → Pr…
· 使用定理 `Submodule.Quotient.mk_smul`：mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ 
p) = r • mk x
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用引理 `ModularForm.mem_cuspFormSubmodule_iff`：mem_cuspFormSubmodule_iff [Γ.HasD
etOne] {f : ModularForm Γ k} : f in cuspFormSubmodule Γ k ↔ IsCuspForm f
· 使用定理 `FunLike.coe_sub`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Sub F] [inst_2 : Sub β]   [IsSubApply F α β] (f g : F),
 ⇑(f …
· 使用定理 `ModularForm.instIsSubApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (Fi
n 2) ℝ)} {k : ℤ}, IsSubApply (ModularForm Γ k) UpperHalfPlane ℂ
· 使用定理 `ModularForm.qExpansion_sub`：∀ {F : Type u_1} [inst : FunLike F UpperHalf
Plane ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} {G : Type u_2}   [inst_1 : FunLik
e G UpperHalfPla…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.strictPeriods_SL2Z`：(Matrix.SpecialLinearGroup.mapGL ℝ).range.s
trictPeriods = AddSubgroup.zmultiples 1
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
· 使用定理 `FunLike.coe_smul`：coe_smul [SMul M F] [SMul M β] [IsSMulApply M F α β] (
n : M) (f : F) : ↑(n • f) = n • (f : α -> β)
· 使用定理 `ModularForm.instIsSMulApplyℂ`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {α
 : Type u_1} [inst : SMul α ℂ] [inst_1 : IsScalarTower α ℂ ℂ]   [inst_2 : Γ.HasD
etOne], IsSMulAppl…
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
For even `k ≥ 3`, the rank of `𝒮ℒ` modular forms is one more than the rank of
cusp forms.
-/
lemma ModularForm.rank_eq_one_add_rank_cuspForm {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    Module.rank ℂ (ModularForm 𝒮ℒ k) = 1 + Module.rank ℂ (CuspForm 𝒮ℒ k) := by
  suffices Module.rank ℂ (ModularForm 𝒮ℒ k ⧸ cuspFormSubmodule 𝒮ℒ k) = 1 by
    rw [(CuspForm.equivCuspFormSubmodule 𝒮ℒ k).rank_eq,
      ← Submodule.rank_quotient_add_rank (cuspFormSubmodule 𝒮ℒ k), this]
  apply rank_eq_one (Submodule.Quotient.mk (E hk))
  · intro h
    have hE := E_qExpansion_coeff_zero hk hk2
    rw [Submodule.Quotient.mk_eq_zero] at h
    exact one_ne_zero <| hE.symm.trans <| (isCuspForm_iff_coeffZero_eq_zero _).mp h
  · refine (Submodule.Quotient.forall _).mpr fun f ↦ ⟨(qExpansion 1 f).coeff 0, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, mem_cuspFormSubmodule_iff,
      isCuspForm_iff_coeffZero_eq_zero, FunLike.coe_sub, ModularForm.qExpansion_sub,
      FunLike.coe_smul, ModularForm.qExpansion_smul, map_sub,
      PowerSeries.coeff_smul, E_qExpansion_coeff_zero hk hk2, smul_eq_mul, mul_one, sub_self]
    all_goals simp

end RankIdentity

section DimensionFormula

namespace ModularForm

/-
**ModularForm.levelOne_weight_four_rank_one** 是 Mathlib 中的一个引理，位于命名空间 `ModularFo
rm`。
形式化陈述：levelOne_weight_four_rank_one : Module.rank Complex (ModularForm 𝒮ℒ 4) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用引理 `ModularForm.rank_eq_one_add_rank_cuspForm`：ModularForm.rank_eq_one_add_r
ank_cuspForm {k : Nat} (hk : 3 <= k) (hk2 : Even k) : Module.rank Complex (Modul
arForm 𝒮ℒ k) = 1 + Module.rank …
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CuspForm.rank_eq_zero_of_weight_lt_twelve`：CuspForm.rank_eq_zero_of_weig
ht_lt_twelve (hk : k < 12) : Module.rank Complex (CuspForm 𝒮ℒ k) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma levelOne_weight_four_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ 4) = 1 :=
  (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨2, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))
/-
**ModularForm.levelOne_weight_six_rank_one** 是 Mathlib 中的一个引理，位于命名空间 `ModularFor
m`。
形式化陈述：levelOne_weight_six_rank_one : Module.rank Complex (ModularForm 𝒮ℒ 6) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用引理 `ModularForm.rank_eq_one_add_rank_cuspForm`：ModularForm.rank_eq_one_add_r
ank_cuspForm {k : Nat} (hk : 3 <= k) (hk2 : Even k) : Module.rank Complex (Modul
arForm 𝒮ℒ k) = 1 + Module.rank …
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CuspForm.rank_eq_zero_of_weight_lt_twelve`：CuspForm.rank_eq_zero_of_weig
ht_lt_twelve (hk : k < 12) : Module.rank Complex (CuspForm 𝒮ℒ k) = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma levelOne_weight_six_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ 6) = 1 :=
  (rank_eq_one_add_rank_cuspForm (by norm_num) ⟨3, rfl⟩).trans
    ((congrArg (1 + ·) (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num))).trans
      (by norm_cast))
/-
**ModularForm.E** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：E {k : Nat} (hk : 3 <= k) : ModularForm 𝒮ℒ k
参数：hk : 3 <= k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma E₄_qExpansion_coeff_one : (qExpansion 1 E₄).coeff 1 = 240 := by
  norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, show bernoulli 4 = -1 / 30 by decide +kernel]
/-
**ModularForm.E** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：E {k : Nat} (hk : 3 <= k) : ModularForm 𝒮ℒ k
参数：hk : 3 <= k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma E₆_qExpansion_coeff_one : (qExpansion 1 E₆).coeff 1 = -504 := by
  norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, show bernoulli 6 = 1 / 42 by decide +kernel]

/- Algebraic core of the weight-2 vanishing argument: if `p : PowerSeries ℂ`
satisfies `c₄ • p₄ = p²` and `c₆ • p₆ = p³` for power series `p₄`, `p₆` with
constant term `1` and first-order coefficients `240` and `-504`, then `p = 0`. -/
/-
**ModularForm.eq_zero_of_pow_eq_smul** 是 Mathlib 中的一个引理，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebraic core of the weight-2 vanishing argument: if `p : PowerSeries ℂ`
satisfies `c₄ • p₄ = p²` and `c₆ • p₆ = p³` for power series `p₄`, `p₆` with
constant term `1` and first-order coefficients `240` and `-504`, then `p = 0`.
-/
private lemma eq_zero_of_pow_eq_smul {p p4 p6 : PowerSeries ℂ} {c4 c6 : ℂ}
    (hp4_0 : p4.coeff 0 = 1) (hp6_0 : p6.coeff 0 = 1) (hp4_1 : p4.coeff 1 = 240)
    (hp6_1 : p6.coeff 1 = -504) (hqc4 : c4 • p4 = p ^ 2)
    (hqc6 : c6 • p6 = p ^ 3) : p = 0 := by
  simp_all only [PowerSeries.coeff_zero_eq_constantCoeff]
  let D := (c4 • p4) ^ 3 - (c6 • p6) ^ 2
  have hD0 : D.coeff 0 = c4 ^ 3 - c6 ^ 2 := by simp [D, hp4_0, hp6_0]
  have hD1 : D.coeff 1 = 720 * c4 ^ 3 + 1008 * c6 ^ 2 := by
    simp [D, pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ]
    grind
  grind [pow_eq_zero_iff, zero_smul]
/-
**ModularForm.weight_two_qExpansion_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ModularFo
rm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma weight_two_qExpansion_eq_zero (f : ModularForm 𝒮ℒ 2) : qExpansion 1 f = 0 := by
  obtain ⟨c4, hc4⟩ : ∃ c4, c4 • E₄ = f.mul f :=
    (finrank_eq_one_iff_of_nonzero' E₄ (E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_four_rank_one) _
  obtain ⟨c6, hc6⟩ : ∃ c6, c6 • E₆ = (f.mul f).mul f :=
    (finrank_eq_one_iff_of_nonzero' E₆ (E_ne_zero _ ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp levelOne_weight_six_rank_one) _
  have hqc4 : c4 • qExpansion 1 (E₄ : ℍ → ℂ) = qExpansion 1 (f : ℍ → ℂ) ^ 2 := by
    rw [pow_two, ← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f f,
      ← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c4 E₄,
      show (c4 • E₄ : ℍ → ℂ) = (f.mul f) from congrArg DFunLike.coe hc4]
  have hqc6 : c6 • qExpansion 1 E₆ = qExpansion 1 (f : ℍ → ℂ) ^ 3 := by
    rw [pow_succ, pow_two, ← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f f,
      ← ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL (f.mul f) f,
      ← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c6 E₆,
      show (c6 • E₆ : ℍ → ℂ) = (f.mul f).mul f from congrArg DFunLike.coe hc6]
  exact eq_zero_of_pow_eq_smul (E_qExpansion_coeff_zero _ ⟨2, rfl⟩)
    (E_qExpansion_coeff_zero _ ⟨3, rfl⟩) E₄_qExpansion_coeff_one E₆_qExpansion_coeff_one hqc4 hqc6

/-- Modular forms of weight 2 for `𝒮ℒ` are zero. -/
/-
**ModularForm.levelOne_weight_two_rank_zero** 是 Mathlib 中的一个定理，位于命名空间 `ModularFo
rm`。
形式化陈述：levelOne_weight_two_rank_zero : Module.rank Complex (ModularForm 𝒮ℒ 2) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.strictPeriods_SL2Z`：(Matrix.SpecialLinearGroup.mapGL ℝ).range.s
trictPeriods = AddSubgroup.zmultiples 1
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula.0.M
odularForm.weight_two_qExpansion_eq_zero`：∀ (f : ModularForm (Matrix.SpecialLine
arGroup.mapGL ℝ).range 2), UpperHalfPlane.qExpansion 1 ⇑f = 0

--- 原说明 ---
Modular forms of weight 2 for `𝒮ℒ` are zero.
-/
theorem levelOne_weight_two_rank_zero : Module.rank ℂ (ModularForm 𝒮ℒ 2) = 0 := by
  simpa [rank_zero_iff_forall_zero, ModularForm.qExpansion_eq_zero_iff]
    using weight_two_qExpansion_eq_zero

/-- The dimension formula for `𝒮ℒ` modular forms of even weight. -/
/-
**ModularForm.dimension_level_one** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：dimension_level_one (k : Nat) (hk2 : Even k) : Module.rank Complex (Modula
rForm 𝒮ℒ k) = if k ≡ 2 [MOD 12] then k / 12 else k / 12 + 1
参数：k : Nat；hk2 : Even k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `ModularForm.levelOne_weight_two_rank_zero`：levelOne_weight_two_rank_zero
 : Module.rank Complex (ModularForm 𝒮ℒ 2) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.ge_of_not_lt`：∀ {n m : ℕ}, ¬n < m → n ≥ m
· 使用定理 `Mathlib.Tactic.IntervalCases.of_lt_right`：of_lt_right [LinearOrder α] (h
 : (a : α) < b) (eq : b = b') : ¬b' <= a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `ModularForm.levelOne_weight_zero_rank_one`：ModularForm.levelOne_weight_z
ero_rank_one : Module.rank Complex (ModularForm 𝒮ℒ 0) = 1
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用引理 `ModularForm.rank_eq_one_add_rank_cuspForm`：ModularForm.rank_eq_one_add_r
ank_cuspForm {k : Nat} (hk : 3 <= k) (hk2 : Even k) : Module.rank Complex (Modul
arForm 𝒮ℒ k) = 1 + Module.rank …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用引理 `ModularForm.levelOne_neg_weight_rank_zero`：ModularForm.levelOne_neg_weig
ht_rank_zero (hk : k < 0) : Module.rank Complex (ModularForm 𝒮ℒ k) = 0
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
The dimension formula for `𝒮ℒ` modular forms of even weight.
-/
theorem dimension_level_one (k : ℕ) (hk2 : Even k) :
    Module.rank ℂ (ModularForm 𝒮ℒ k) =
      if k ≡ 2 [MOD 12] then k / 12 else k / 12 + 1 := by
  induction k using Nat.strong_induction_on with | h k ihn =>
  have : k < 3 ∨ (3 ≤ k ∧ k < 12) ∨ 12 ≤ k := by grind
  rcases this with hk | hk | hk
  · -- `k < 3`: direct case-by-case check
    interval_cases k
    · simpa using! levelOne_weight_zero_rank_one
    · grind
    · simpa [Nat.ModEq] using levelOne_weight_two_rank_zero
  · -- `3 ≤ k < 12`: rank decomposition + the weight `k - 12` space is zero
    rw [rank_eq_one_add_rank_cuspForm hk.1 hk2, CuspForm.discriminantEquiv.rank_eq,
      levelOne_neg_weight_rank_zero (by lia)]
    have : k ∈ (Finset.Icc 3 11).filter Even := by grind
    fin_cases this <;> simp [Nat.ModEq]
  · -- `12 ≤ k`: rank decomposition + induction hypothesis at weight `k - 12`
    rw [rank_eq_one_add_rank_cuspForm (by lia) hk2, CuspForm.discriminantEquiv.rank_eq,
      show ((k : ℤ) - 12 : ℤ) = ((k - 12 : ℕ) : ℤ) by lia,
      ihn (k - 12) (by lia) (by grind)]
    simp only [Nat.ModEq, show k / 12 = (k - 12) / 12 + 1 by lia,
      show (k - 12) % 12 = k % 12 by lia]
    split_ifs <;> grind
/-
**ModularForm.** 是 Mathlib 中的一个实例，位于命名空间 `ModularForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (k : ℤ) : FiniteDimensional ℂ (ModularForm 𝒮ℒ k) := by
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  rcases lt_or_ge k 0 with hk_neg | hk_nonneg
  · rw [levelOne_neg_weight_rank_zero hk_neg]
    exact Cardinal.aleph0_pos
  rcases Int.even_or_odd k with hk_even | hk_odd
  · lift k to ℕ using hk_nonneg
    rw [dimension_level_one k (mod_cast hk_even)]
    split_ifs <;> exact_mod_cast Cardinal.natCast_lt_aleph0
  · rw [levelOne_odd_weight_rank_zero hk_odd]
    exact Cardinal.aleph0_pos

/-- **Sturm bound for level-1 modular forms (natural weight).** If a modular form `f` of weight
`k : ℕ` has q-expansion of order strictly greater than `k / 12`, then `f` is identically zero. -/
/-
**ModularForm.sturm_bound_levelOne_nat** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：sturm_bound_levelOne_nat {k : Nat} {f : ModularForm 𝒮ℒ (k : Int)} (h : (↑(
k / 12) : Nat∞) < (qExpansion 1 f).order) : f = 0
参数：k : Int；h : (↑(k / 12) : Nat∞) < (qExpansion 1 f).order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `rank_zero_iff_forall_zero`：rank_zero_iff_forall_zero : Module.rank R M =
 0 ↔ forall x : M, x = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `ModularForm.levelOne_neg_weight_rank_zero`：ModularForm.levelOne_neg_weig
ht_rank_zero (hk : k < 0) : Module.rank Complex (ModularForm 𝒮ℒ k) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModularForm.mcast_eq_zero_iff`：mcast_eq_zero_iff {a b : Int} {Γ Γ' : Sub
group (GL (Fin 2) Real)} (h : a = b) (hΓ : Γ' = Γ) (f : ModularForm Γ a) : mcast
 h f hΓ = 0 ↔ f = 0
· 使用引理 `ENat.add_lt_add_iff_right`：add_lt_add_iff_right {k : Nat∞} (h : k != ⊤) 
: n + k < m + k ↔ n < m
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ModularForm.discriminant_qExpansion_order`：discriminant_qExpansion_order
 : (qExpansion 1 Δ).order = 1
· 使用定理 `PowerSeries.order_mul`：order_mul (φ ψ : R⟦X⟧) : order (φ * ψ) = order φ 
+ order ψ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `ModularForm.qExpansion_eq_qExpansion_discriminant_mul`：qExpansion_eq_qEx
pansion_discriminant_mul (f : ModularForm 𝒮ℒ k) (hcusp : (qExpansion 1 f).coeff 
0 = 0) : qExpansion 1 f = qExpansion 1 disc…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ModularForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (F
in 2) ℝ)} {k : ℤ}, IsZeroApply (ModularForm Γ k) UpperHalfPlane ℂ
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
**Sturm bound for level-1 modular forms (natural weight).** If a modular form `f
` of weight
`k : ℕ` has q-expansion of order strictly greater than `k / 12`, then `f` is ide
ntically zero.
-/
theorem sturm_bound_levelOne_nat {k : ℕ} {f : ModularForm 𝒮ℒ (k : ℤ)}
    (h : (↑(k / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0 := by
  induction k using Nat.strong_induction_on with | _ k ih =>
  have h0 : (qExpansion 1 f).coeff 0 = 0 :=
    PowerSeries.coeff_of_lt_order _ ((Nat.cast_nonneg _).trans_lt h)
  suffices CuspForm.discriminantEquiv (toCuspForm f h0) = 0 by
    simpa [CuspForm.discriminantEquiv.map_eq_zero_iff, DFunLike.ext_iff]
  rcases lt_or_ge k 12 with hk12 | hk12
  · apply rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero (by lia))
  · rw [← mcast_eq_zero_iff (b := ↑(k - 12)) (by lia) rfl]
    refine ih (k - 12) (by lia) ?_
    have hsucc : k / 12 = (k - 12) / 12 + 1 := by lia
    rw [qExpansion_eq_qExpansion_discriminant_mul f h0, PowerSeries.order_mul,
      discriminant_qExpansion_order, add_comm, hsucc, Nat.cast_add, Nat.cast_one] at h
    exact (ENat.add_lt_add_iff_right (ENat.natCast_ne_top 1)).mp h

/-- **Sturm bound for level-1 modular forms.** If a modular form `f` of weight `k` for `SL(2, ℤ)`
has q-expansion of order strictly greater than `k / 12`, then `f` is identically zero.
Corollary of the natural-weight version `sturm_bound_levelOne_nat`. -/
/-
**ModularForm.sturm_bound_levelOne** 是 Mathlib 中的一个定理，位于命名空间 `ModularForm`。
形式化陈述：sturm_bound_levelOne {k : Int} {f : ModularForm 𝒮ℒ k} (h : (↑(k.toNat / 12
) : Nat∞) < (qExpansion 1 f).order) : f = 0
参数：h : (↑(k.toNat / 12) : Nat∞) < (qExpansion 1 f).order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `rank_zero_iff_forall_zero`：rank_zero_iff_forall_zero : Module.rank R M =
 0 ↔ forall x : M, x = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用引理 `ModularForm.levelOne_neg_weight_rank_zero`：ModularForm.levelOne_neg_weig
ht_rank_zero (hk : k < 0) : Module.rank Complex (ModularForm 𝒮ℒ k) = 0
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftIntNatCastLeOfNat`：CanLift ℤ ℕ (fun n => ↑n) fun x => 0 ≤ x
· 使用定理 `ModularForm.sturm_bound_levelOne_nat`：sturm_bound_levelOne_nat {k : Nat}
 {f : ModularForm 𝒮ℒ (k : Int)} (h : (↑(k / 12) : Nat∞) < (qExpansion 1 f).order
) : f = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
**Sturm bound for level-1 modular forms.** If a modular form `f` of weight `k` f
or `SL(2, ℤ)`
has q-expansion of order strictly greater than `k / 12`, then `f` is identically
 zero.
Corollary of the natural-weight version `sturm_bound_levelOne_nat`.
-/
theorem sturm_bound_levelOne {k : ℤ} {f : ModularForm 𝒮ℒ k}
    (h : (↑(k.toNat / 12) : ℕ∞) < (qExpansion 1 f).order) : f = 0 := by
  rcases lt_or_ge k 0 with hk | hk
  · exact rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk) f
  · lift k to ℕ using hk
    exact sturm_bound_levelOne_nat (mod_cast h)

end ModularForm

end DimensionFormula

