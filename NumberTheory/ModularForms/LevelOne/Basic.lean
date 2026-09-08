/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.Modular
public import Mathlib.NumberTheory.ModularForms.QExpansion
/-!
# Level one modular forms

This file contains results specific to modular forms of level one, i.e. modular forms for
`SL(2, ℤ)`.

Finite-dimensionality of these spaces is proved in a later file
(`Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`).
-/

public section

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex
  CongruenceSubgroup Real Function SlashInvariantFormClass ModularFormClass Periodic MatrixGroups

local notation "𝕢" => qParam

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

namespace SlashInvariantForm

variable [SlashInvariantFormClass F 𝒮ℒ k]

/-
**SlashInvariantForm.exists_one_half_le_im_and_norm_le** 是 Mathlib 中的一个引理，位于命名空间
 `SlashInvariantForm`。
形式化陈述：exists_one_half_le_im_and_norm_le (hk : k <= 0) (f : F) (τ : ℍ) : exists ξ
 : ℍ, 1 / 2 <= ξ.im ∧ ‖f τ‖ <= ‖f ξ‖
参数：hk : k <= 0；f : F；τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ModularGroup.exists_one_half_le_im_smul_and_norm_denom_le`：exists_one_ha
lf_le_im_smul_and_norm_denom_le (τ : ℍ) : exists γ : SL(2, Int), 1 / 2 <= im (γ 
• τ) ∧ ‖denom γ τ‖ <= 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CongruenceSubgroup.Gamma_one_coe_eq_SL`：Gamma_one_coe_eq_SL : (↑(Gamma 1
) : Subgroup (GL (Fin 2) Real)) = 𝒮ℒ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SlashInvariantForm.slash_action_eqn_SL''`：slash_action_eqn_SL'' {k : Int
} {Γ : Subgroup SL(2, Int)} [SlashInvariantFormClass F Γ k] (f : F) {γ} (hγ : γ 
in Γ) (z : ℍ) : f (γ • z) = (d…
· 使用引理 `CongruenceSubgroup.mem_Gamma_one`：mem_Gamma_one (γ : SL(2, Int)) : γ in 
Γ(1)
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `le_mul_of_one_le_left`：le_mul_of_one_le_left [MulPosMono α] (hb : 0 <= b
) (h : 1 <= a) : b <= a * b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `one_le_zpow_of_nonpos₀`：one_le_zpow_of_nonpos₀ (ha₀ : 0 < a) (ha₁ : a <=
 1) (hn : n <= 0) : 1 <= a ^ n
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
-/
lemma exists_one_half_le_im_and_norm_le (hk : k ≤ 0) (f : F) (τ : ℍ) :
    ∃ ξ : ℍ, 1 / 2 ≤ ξ.im ∧ ‖f τ‖ ≤ ‖f ξ‖ :=
  let ⟨γ, hγ, hdenom⟩ := exists_one_half_le_im_smul_and_norm_denom_le τ
  ⟨γ • τ, hγ, by
    have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
    simpa only [slash_action_eqn_SL'' _ (mem_Gamma_one γ), norm_mul, norm_zpow]
      using le_mul_of_one_le_left (norm_nonneg _) <|
        one_le_zpow_of_nonpos₀ (norm_pos_iff.2 (denom_ne_zero _ _)) hdenom hk⟩

variable (k) in
/-- If a constant function is modular of weight `k`, then either `k = 0`, or the constant is `0`. -/
/-
**SlashInvariantForm.wt_eq_zero_of_eq_const** 是 Mathlib 中的一个引理，位于命名空间 `SlashInva
riantForm`。
形式化陈述：wt_eq_zero_of_eq_const {f : F} {c : Complex} (hf : ⇑f = Function.const _ c
) : k = 0 ∨ c = 0
参数：hf : ⇑f = Function.const _ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CongruenceSubgroup.Gamma_one_coe_eq_SL`：Gamma_one_coe_eq_SL : (↑(Gamma 1
) : Subgroup (GL (Fin 2) Real)) = 𝒮ℒ
· 使用定理 `SlashInvariantForm.slash_action_eqn_SL''`：slash_action_eqn_SL'' {k : Int
} {Γ : Subgroup SL(2, Int)} [SlashInvariantFormClass F Γ k] (f : F) {γ} (hγ : γ 
in Γ) (z : ℍ) : f (γ • z) = (d…
· 使用引理 `CongruenceSubgroup.mem_Gamma_one`：mem_Gamma_one (γ : SL(2, Int)) : γ in 
Γ(1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_zpow`：ofReal_zpow (r : Real) (n : Int) : ((r ^ n : Real) 
: Complex) = (r : Complex) ^ n
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
· 使用引理 `zpow_eq_one_iff_right₀`：zpow_eq_one_iff_right₀ (ha₀ : 0 <= a) (ha₁ : a !
= 1) {n : Int} : a ^ n = 1 ↔ n = 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_zpow`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (a b : α) (n : 
ℤ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ModularGroup.denom_S`：∀ (z : UpperHalfPlane),   UpperHalfPlane.denom    
   (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRing
Hom ℝ)) Mo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If a constant function is modular of weight `k`, then either `k = 0`, or the con
stant is `0`.
-/
lemma wt_eq_zero_of_eq_const {f : F} {c : ℂ} (hf : ⇑f = Function.const _ c) :
    k = 0 ∨ c = 0 := by
  have : SlashInvariantFormClass F Γ(1) k := Gamma_one_coe_eq_SL ▸ ‹_›
  have hI := slash_action_eqn_SL'' f (mem_Gamma_one S) I
  have h2I2 := slash_action_eqn_SL'' f (mem_Gamma_one S) ((⟨2, two_pos⟩ : {x : ℝ // 0 < x}) • .I)
  simp_rw [sl_moeb, hf, Function.const, denom_S] at hI h2I2
  suffices (2 : ℂ) ^ k = 1 ↔ k = 0 by
    simpa [mul_zpow, zpow_ne_zero, this] using h2I2.symm.trans hI
  simpa using ofReal_inj.trans <| zpow_eq_one_iff_right₀ (two_pos.le : (0 : ℝ) ≤ 2) (by norm_num1)
/-
**SlashInvariantForm.slash_action_generators_SL2Z** 是 Mathlib 中的一个定理，位于命名空间 `Sla
shInvariantForm`。
形式化陈述：slash_action_generators_SL2Z {f : ℍ -> Complex} {k : Int} (hS : f ∣[k] S =
 f) (hT : f ∣[k] T = f) : forall γ : SL(2, Int), f ∣[k] γ = f
参数：hS : f ∣[k] S = f；hT : f ∣[k] T = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SpecialLinearGroup.SL2Z_generators`：SpecialLinearGroup.SL2Z_generators :
 closure {S, T} = ⊤
· 使用定理 `MonoidHom.map_closure`：map_closure (f : G ->* N) (s : Set G) : (closure 
s).map f = closure (f '' s)
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SlashInvariantForm.slash_action_generators`：slash_action_generators {f :
 ℍ -> Complex} {Γ : Subgroup (GL (Fin 2) Real)} {s : Set (GL (Fin 2) Real)} (hΓ 
: Γ = Subgroup.closure s) {k : I…
· 使用定理 `MonoidHom.mem_range`：mem_range {f : G ->* N} {y : N} : y in f.range ↔ ex
ists x, f x = y
-/
theorem slash_action_generators_SL2Z {f : ℍ → ℂ} {k : ℤ}
    (hS : f ∣[k] S = f) (hT : f ∣[k] T = f) : ∀ γ : SL(2, ℤ), f ∣[k] γ = f := by
  intro γ
  have h𝒮ℒ : 𝒮ℒ = Subgroup.closure ({↑S, ↑T} : Set (GL (Fin 2) ℝ)) := by
    rw [MonoidHom.range_eq_map, ← SpecialLinearGroup.SL2Z_generators, MonoidHom.map_closure,
      Set.image_pair]
    rfl
  exact (slash_action_generators h𝒮ℒ).mpr (fun g hg ↦ by rcases hg with rfl | rfl <;> assumption)
    _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)

end SlashInvariantForm

/-
**one_mem_strictPeriods_SL** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：one_mem_strictPeriods_SL : (1 : Real) in (𝒮ℒ).strictPeriods
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.strictPeriods_SL2Z`：(Matrix.SpecialLinearGroup.mapGL ℝ).range.s
trictPeriods = AddSubgroup.zmultiples 1
-/
lemma one_mem_strictPeriods_SL : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by simp

namespace ModularFormClass

variable [ModularFormClass F 𝒮ℒ k]

/-
**ModularFormClass.cuspFunction_eqOn_const_of_nonpos_wt** 是 Mathlib 中的一个定理，位于命名空
间 `ModularFormClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem cuspFunction_eqOn_const_of_nonpos_wt (hk : k ≤ 0) (f : F) :
    Set.EqOn (cuspFunction 1 f) (const ℂ (cuspFunction 1 f 0)) (Metric.ball 0 1) := by
  refine eq_const_of_exists_le (fun q hq ↦ ?_) (exp_nonneg (-π)) ?_ (fun q hq ↦ ?_)
  · exact (ModularFormClass.differentiableAt_cuspFunction f one_pos one_mem_strictPeriods_SL
      (mem_ball_zero_iff.mp hq)).differentiableWithinAt
  · simp [pi_pos]
  · simp only [Metric.mem_closedBall, dist_zero_right]
    rcases eq_or_ne q 0 with rfl | hq'
    · refine ⟨0, by simpa only [norm_zero] using exp_nonneg _, le_rfl⟩
    · obtain ⟨ξ, hξ, hξ₂⟩ := exists_one_half_le_im_and_norm_le hk f
        ⟨_, im_invQParam_pos_of_norm_lt_one Real.zero_lt_one (mem_ball_zero_iff.mp hq) hq'⟩
      exact ⟨_, norm_qParam_le_of_one_half_le_im hξ,
        by simpa [← SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL
            one_ne_zero, qParam_right_inv one_ne_zero hq'] using hξ₂⟩
/-
**ModularFormClass.levelOne_nonpos_wt_const** 是 Mathlib 中的一个定理，位于命名空间 `ModularFo
rmClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem levelOne_nonpos_wt_const (hk : k ≤ 0) (f : F) :
    f = Function.const ℍ (cuspFunction 1 f 0) := by
  ext z
  have hQ : 𝕢 1 z ∈ (Metric.ball 0 1) := by
    simpa using (norm_qParam_lt_iff zero_lt_one 0 z.1).mpr z.2
  simpa [← SlashInvariantFormClass.eq_cuspFunction f _ one_mem_strictPeriods_SL one_ne_zero]
    using cuspFunction_eqOn_const_of_nonpos_wt hk f hQ
/-
**ModularFormClass.levelOne_neg_weight_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Modula
rFormClass`。
形式化陈述：levelOne_neg_weight_eq_zero (hk : k < 0) (f : F) : ⇑f = 0
参数：hk : k < 0；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.LevelOne.Basic.0.ModularFormC
lass.levelOne_nonpos_wt_const`：∀ {F : Type u_1} [inst : FunLike F UpperHalfPlane
 ℂ] {k : ℤ}   [ModularFormClass F (Matrix.SpecialLinearGroup.mapGL ℝ).range k], 
  k ≤ 0 → ∀…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `SlashInvariantForm.wt_eq_zero_of_eq_const`：wt_eq_zero_of_eq_const {f : F
} {c : Complex} (hf : ⇑f = Function.const _ c) : k = 0 ∨ c = 0
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.const_zero`：∀ {α : Type u_2} {M : Type u_7} [inst : Zero M], Fu
nction.const α 0 = 0
-/
lemma levelOne_neg_weight_eq_zero (hk : k < 0) (f : F) : ⇑f = 0 := by
  have hf := levelOne_nonpos_wt_const hk.le f
  rcases wt_eq_zero_of_eq_const k hf with rfl | hf₀
  · exact (lt_irrefl _ hk).elim
  · rw [hf, hf₀, const_zero]
/-
**ModularFormClass.levelOne_weight_zero_const** 是 Mathlib 中的一个引理，位于命名空间 `Modular
FormClass`。
形式化陈述：levelOne_weight_zero_const [ModularFormClass F 𝒮ℒ 0] (f : F) : exists c, ⇑
f = Function.const _ c
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.LevelOne.Basic.0.ModularFormC
lass.levelOne_nonpos_wt_const`：∀ {F : Type u_1} [inst : FunLike F UpperHalfPlane
 ℂ] {k : ℤ}   [ModularFormClass F (Matrix.SpecialLinearGroup.mapGL ℝ).range k], 
  k ≤ 0 → ∀…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma levelOne_weight_zero_const [ModularFormClass F 𝒮ℒ 0] (f : F) :
    ∃ c, ⇑f = Function.const _ c :=
  ⟨_, levelOne_nonpos_wt_const le_rfl f⟩

end ModularFormClass

/-
**ModularForm.levelOne_weight_zero_rank_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.levelOne_weight_zero_rank_one : Module.rank Complex (ModularFo
rm 𝒮ℒ 0) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rank_eq_one`：rank_eq_one (v : M) (n : v != 0) (h : forall w : M, exists 
c : R, c • v = w) : Module.rank R M = 1
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
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ModularForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (F
in 2) ℝ)} {k : ℤ}, IsZeroApply (ModularForm Γ k) UpperHalfPlane ℂ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `ModularFormClass.levelOne_weight_zero_const`：levelOne_weight_zero_const 
[ModularFormClass F 𝒮ℒ 0] (f : F) : exists c, ⇑f = Function.const _ c
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
· 使用定理 `ModularForm.ext`：ModularForm.ext {f g : ModularForm Γ k} (h : forall x, 
f x = g x) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `ModularForm.instIsSMulApplyℂ`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {α
 : Type u_1} [inst : SMul α ℂ] [inst_1 : IsScalarTower α ℂ ℂ]   [inst_2 : Γ.HasD
etOne], IsSMulAppl…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma ModularForm.levelOne_weight_zero_rank_one : Module.rank ℂ (ModularForm 𝒮ℒ 0) = 1 := by
  refine rank_eq_one (const 1) (by simp [DFunLike.ne_iff]) fun g ↦ ?_
  obtain ⟨c', hc'⟩ := levelOne_weight_zero_const g
  aesop
/-
**ModularForm.levelOne_neg_weight_rank_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.levelOne_neg_weight_rank_zero (hk : k < 0) : Module.rank Compl
ex (ModularForm 𝒮ℒ k) = 0
参数：hk : k < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用引理 `rank_eq_zero_iff`：rank_eq_zero_iff {R M} [Ring R] [AddCommGroup M] [Modu
le R M] : Module.rank R M = 0 ↔ forall x : M, exists a : R, a != 0 ∧ a • x = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `ModularForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (F
in 2) ℝ)} {k : ℤ}, IsZeroApply (ModularForm Γ k) UpperHalfPlane ℂ
· 使用引理 `ModularFormClass.levelOne_neg_weight_eq_zero`：levelOne_neg_weight_eq_zer
o (hk : k < 0) (f : F) : ⇑f = 0
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
-/
lemma ModularForm.levelOne_neg_weight_rank_zero (hk : k < 0) :
    Module.rank ℂ (ModularForm 𝒮ℒ k) = 0 := by
  refine rank_eq_zero_iff.mpr fun f ↦ ⟨_, one_ne_zero, ?_⟩
  simpa [← FunLike.coe_zero_iff] using levelOne_neg_weight_eq_zero hk f
