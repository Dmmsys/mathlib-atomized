/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic

/-!
# Norm and trace maps

Given two subgroups `𝒢, ℋ` of `GL(2, ℝ)` with `𝒢.relindex ℋ ≠ 0` (i.e. `𝒢 ⊓ ℋ` has finite index
in `ℋ`), we define a trace map from `ModularForm (𝒢 ⊓ ℋ) k` to `ModularForm ℋ k`.
-/

@[expose] public noncomputable section

open UpperHalfPlane

open scoped ModularForm Topology Filter Manifold

variable {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} (f : F) [FunLike F ℍ ℂ] {k : ℤ}

local notation "𝒬" => ℋ ⧸ (𝒢.subgroupOf ℋ)

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction ℋ ℋ := Monoid.toMulAction ..
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction ℋ 𝒬 := .quotient ..

namespace SlashInvariantForm

variable [SlashInvariantFormClass F 𝒢 k]

/-- For `f` invariant under `𝒢`, this is a function on `(ℋ ⧸ 𝒢 ⊓ ℋ) × ℍ → ℂ` which packages up the
translates of `f` by `ℋ`. -/
/-
**SlashInvariantForm.quotientFunc** 是 Mathlib 中的一个定义，位于命名空间 `SlashInvariantForm`
。
形式化陈述：quotientFunc (q : 𝒬) (τ : ℍ) : Complex
参数：q : 𝒬；τ : ℍ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `f` invariant under `𝒢`, this is a function on `(ℋ ⧸ 𝒢 ⊓ ℋ) × ℍ → ℂ` which p
ackages up the
translates of `f` by `ℋ`.
-/
def quotientFunc (q : 𝒬) (τ : ℍ) : ℂ :=
  q.liftOn (fun g ↦ ((f : ℍ → ℂ) ∣[k] g.val⁻¹) τ) (fun h h' hhh' ↦ by
    obtain ⟨j, hj, hj'⟩ : ∃ g ∈ 𝒢, h' = h * g := by
      rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply] at hhh'
      exact ⟨h⁻¹ * h', hhh', mod_cast (mul_inv_cancel_left h h').symm⟩
    simp [hj', SlashAction.slash_mul, SlashInvariantFormClass.slash_action_eq f j⁻¹ (inv_mem hj)])
/-
**SlashInvariantForm.quotientFunc_mk** 是 Mathlib 中的一个定理，位于命名空间 `SlashInvariantFo
rm`。
形式化陈述：∀ {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type u_1} (f : F) [inst : FunLike F
 UpperHalfPlane ℂ] {k : ℤ}   [inst_1 : SlashInvariantFormClass F 𝒢 k] (h : ↥ℋ), 
SlashInvariantForm.quotientFunc f ⟦h⟧ = SlashAction.map k (↑h)⁻¹ ⇑f
参数：GL (Fin 2) ℝ；f : F；h : ↥ℋ；↑h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma quotientFunc_mk (h : ℋ) : quotientFunc f ⟦h⟧ = (f : ℍ → ℂ) ∣[k] h.val⁻¹ :=
  rfl
/-
**SlashInvariantForm.quotientFunc_smul** 是 Mathlib 中的一个引理，位于命名空间 `SlashInvariant
Form`。
形式化陈述：quotientFunc_smul {h} (hh : h in ℋ) (q : 𝒬) : quotientFunc f q ∣[k] h = qu
otientFunc f ((⟨h, hh⟩ : ℋ)⁻¹ • q)
参数：hh : h in ℋ；q : 𝒬。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `SlashAction.slash_mul`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (g h
 : G) (a : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quotientFunc_smul {h} (hh : h ∈ ℋ) (q : 𝒬) :
    quotientFunc f q ∣[k] h = quotientFunc f ((⟨h, hh⟩ : ℋ)⁻¹ • q) := by
  induction q using Quotient.inductionOn with
  | h r => simp [SlashAction.slash_mul]

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- The trace of a slash-invariant form, as a slash-invariant form. -/
@[simps! -fullyApplied]
/-
**SlashInvariantForm.trace** 是 Mathlib 中的一个定义，位于命名空间 `SlashInvariantForm`。
形式化陈述：{𝒢 : Subgroup (GL (Fin 2) ℝ)} →   (ℋ : Subgroup (GL (Fin 2) ℝ)) →     {F :
 Type u_1} →       F →         [inst : FunLike F UpperHalfPlane ℂ] →           {
k : ℤ} → [SlashInvariantFormClass F 𝒢 k] → [𝒢.IsFiniteRelIndex ℋ] → SlashInvaria
ntForm ℋ k
参数：GL (Fin 2) ℝ；ℋ : Subgroup (GL (Fin 2) ℝ)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trace of a slash-invariant form, as a slash-invariant form.
-/
protected def trace : SlashInvariantForm ℋ k where
  toFun := let := Fintype.ofFinite 𝒬; ∑ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [SlashAction.sum_slash, quotientFunc_smul f hh]
      using Equiv.sum_comp (MulAction.toPerm (_ : ℋ)) _

/-- The norm of a slash-invariant form, as a slash-invariant form. -/
@[simps! -fullyApplied]
/-
**SlashInvariantForm.norm** 是 Mathlib 中的一个定义，位于命名空间 `SlashInvariantForm`。
形式化陈述：{𝒢 : Subgroup (GL (Fin 2) ℝ)} →   (ℋ : Subgroup (GL (Fin 2) ℝ)) →     {F :
 Type u_1} →       F →         [inst : FunLike F UpperHalfPlane ℂ] →           {
k : ℤ} →             [SlashInvariantFormClass F 𝒢 k] →               [𝒢.IsFinite
RelIndex ℋ] →                 [ℋ.HasDetPlusMinusOne] → SlashInvariantForm ℋ (k *
 ↑(Nat.card (↥ℋ ⧸ 𝒢.subgroupOf ℋ)))
参数：GL (Fin 2) ℝ；ℋ : Subgroup (GL (Fin 2) ℝ)；k * ↑(Nat.card (↥ℋ ⧸ 𝒢.subgroupOf ℋ)
)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm of a slash-invariant form, as a slash-invariant form.
-/
protected def norm [ℋ.HasDetPlusMinusOne] : SlashInvariantForm ℋ (k * Nat.card 𝒬) where
  toFun := let := Fintype.ofFinite 𝒬; ∏ q : 𝒬, quotientFunc f q
  slash_action_eq' h hh := by
    let := Fintype.ofFinite 𝒬
    simpa [← Finset.card_univ, ModularForm.prod_slash,
      quotientFunc_smul f hh, Subgroup.HasDetPlusMinusOne.abs_det hh,
      -Matrix.GeneralLinearGroup.val_det_apply] using Equiv.prod_comp (MulAction.toPerm (_ : ℋ)) _

end SlashInvariantForm

open SlashInvariantForm

section ModularForm

variable (ℋ) [𝒢.IsFiniteRelIndex ℋ]

/-- The trace of a modular form, as a modular form. -/
@[simps! -fullyApplied]
/-
**ModularForm.trace** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：{𝒢 : Subgroup (GL (Fin 2) ℝ)} →   (ℋ : Subgroup (GL (Fin 2) ℝ)) →     {F :
 Type u_1} →       F →         [inst : FunLike F UpperHalfPlane ℂ] →           {
k : ℤ} → [𝒢.IsFiniteRelIndex ℋ] → [ModularFormClass F 𝒢 k] → ModularForm ℋ k
参数：GL (Fin 2) ℝ；ℋ : Subgroup (GL (Fin 2) ℝ)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …

--- 原说明 ---
The trace of a modular form, as a modular form.
-/
protected def ModularForm.trace [ModularFormClass F 𝒢 k] : ModularForm ℋ k where
  __ := SlashInvariantForm.trace ℋ f
  holo' := .sum (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ (translate f r⁻¹).holo')
  bdd_at_cusps' h γ := by
    rintro rfl
    rw [SlashInvariantForm.trace, IsBoundedAtImInfty, Filter.BoundedAtFilter,
      SlashAction.sum_slash, Finset.sum_fn]
    refine .fun_sum (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ (translate f _).bdd_at_cusps' ?_ γ rfl)
    simpa using h.of_isFiniteRelIndex_conj hr

/-- The trace of a cusp form, as a cusp form. -/
@[simps! -fullyApplied]
/-
**CuspForm.trace** 是 Mathlib 中的一个定义，位于命名空间 `CuspForm`。
形式化陈述：{𝒢 : Subgroup (GL (Fin 2) ℝ)} →   (ℋ : Subgroup (GL (Fin 2) ℝ)) →     {F :
 Type u_1} →       F → [inst : FunLike F UpperHalfPlane ℂ] → {k : ℤ} → [𝒢.IsFini
teRelIndex ℋ] → [CuspFormClass F 𝒢 k] → CuspForm ℋ k
参数：GL (Fin 2) ℝ；ℋ : Subgroup (GL (Fin 2) ℝ)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CuspForm.instModularFormClassOfCuspFormClass`：∀ {F : Type u_1} {Γ : Subg
roup (GL (Fin 2) ℝ)} {k : ℤ} [inst : FunLike F UpperHalfPlane ℂ] [CuspFormClass 
F Γ k],   ModularFormClass F Γ k
· 使用定理 `ModularForm.holo'`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (self : Modul
arForm Γ k), MDiff ⇑self.toSlashInvariantForm

--- 原说明 ---
The trace of a cusp form, as a cusp form.
-/
protected def CuspForm.trace [CuspFormClass F 𝒢 k] : CuspForm ℋ k where
  __ := ModularForm.trace ℋ f
  zero_at_cusps' h γ := by
    rintro rfl
    simp_rw [ModularForm.toFun_eq_coe, ModularForm.coe_trace, IsZeroAtImInfty, Filter.ZeroAtFilter,
      SlashAction.sum_slash, Finset.sum_fn]
    let := Fintype.ofFinite 𝒬
    rw [show (0 : ℂ) = ∑ c : ℋ ⧸ 𝒢.subgroupOf ℋ, 0 by simp]
    refine tendsto_finsetSum _ (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ ?_)
    refine (translate f _).zero_at_cusps' ?_ γ rfl
    simpa using h.of_isFiniteRelIndex_conj hr

/-- The norm of a modular form, as a modular form. -/
@[simps! -fullyApplied]
/-
**ModularForm.norm** 是 Mathlib 中的一个定义，位于命名空间 `ModularForm`。
形式化陈述：{𝒢 : Subgroup (GL (Fin 2) ℝ)} →   (ℋ : Subgroup (GL (Fin 2) ℝ)) →     {F :
 Type u_1} →       F →         [inst : FunLike F UpperHalfPlane ℂ] →           {
k : ℤ} →             [𝒢.IsFiniteRelIndex ℋ] →               [ℋ.HasDetPlusMinusOn
e] → [ModularFormClass F 𝒢 k] → ModularForm ℋ (k * ↑(Nat.card (↥ℋ ⧸ 𝒢.subgroupOf
 ℋ)))
参数：GL (Fin 2) ℝ；ℋ : Subgroup (GL (Fin 2) ℝ)；k * ↑(Nat.card (↥ℋ ⧸ 𝒢.subgroupOf ℋ)
)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …

--- 原说明 ---
The norm of a modular form, as a modular form.
-/
protected def ModularForm.norm [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k] :
    ModularForm ℋ (k * Nat.card 𝒬) where
  __ := SlashInvariantForm.norm ℋ f
  holo' := .prod (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ (translate f r⁻¹).holo')
  bdd_at_cusps' h γ := by
    rintro rfl
    simp_rw [SlashInvariantForm.norm, IsBoundedAtImInfty, Filter.BoundedAtFilter]
    let := Fintype.ofFinite 𝒬
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ, ModularForm.prod_slash]
    apply Asymptotics.IsBigO.const_smul_left
    rw [show (1 : ℍ → ℝ) = (fun x ↦ ∏ (i : 𝒬), 1) by ext; simp, Finset.prod_fn]
    refine .finsetProd (Quotient.forall.mpr fun ⟨r, hr⟩ _ ↦ (translate f _).bdd_at_cusps' ?_ γ rfl)
    simpa using h.of_isFiniteRelIndex_conj hr

variable {f} in
/-
**ModularForm.norm_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.norm_ne_zero [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k] (
hf : (f : ℍ -> Complex) != 0) : ModularForm.norm ℋ f != 0
参数：hf : (f : ℍ -> Complex) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用引理 `UpperHalfPlane.prod_eq_zero_iff`：prod_eq_zero_iff {ι : Type*} {f : ι -> 
ℍ -> Complex} {s : Finset ι} (hf : forall i in s, MDiff (f i)) : ∏ i in s, f i =
 0 ↔ exists i in s, f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.forall`：Quotient.forall {α : Sort*} {s : Setoid α} {p : Quotien
t s -> Prop} : (forall a, p a) ↔ forall a : α, p ⟦a⟧
· 使用定理 `ModularForm.holo'`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (self : Modul
arForm Γ k), MDiff ⇑self.toSlashInvariantForm
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `ModularForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (F
in 2) ℝ)} {k : ℤ}, IsZeroApply (ModularForm Γ k) UpperHalfPlane ℂ
· 使用定理 `ModularForm.coe_norm`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} (ℋ : Subgroup (GL 
(Fin 2) ℝ)) {F : Type u_1} (f : F) [inst : FunLike F UpperHalfPlane ℂ]   {k : ℤ}
 [inst_1 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma ModularForm.norm_ne_zero [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k]
    (hf : (f : ℍ → ℂ) ≠ 0) : ModularForm.norm ℋ f ≠ 0 := by
  contrapose hf
  rw [← DFunLike.coe_injective.eq_iff, coe_norm, FunLike.coe_zero, prod_eq_zero_iff] at hf
  · simpa [QuotientGroup.exists_mk] using hf
  · exact Quotient.forall.mpr fun r _ ↦ (translate f r.val⁻¹).holo'
/-
**ModularForm.norm_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.norm_eq_zero_iff [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 
k] : ModularForm.norm ℋ f = 0 ↔ (f : ℍ -> Complex) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `ModularForm.norm_ne_zero`：ModularForm.norm_ne_zero [ℋ.HasDetPlusMinusOne
] [ModularFormClass F 𝒢 k] (hf : (f : ℍ -> Complex) != 0) : ModularForm.norm ℋ f
 != 0
· 使用定理 `ModularForm.ext`：ModularForm.ext {f g : ModularForm Γ k} (h : forall x, 
f x = g x) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModularFormClass.toSlashInvariantFormClass`：∀ {F : Type u_2} {Γ : outPar
am (Subgroup (GL (Fin 2) ℝ))} {k : outParam ℤ} {inst : FunLike F UpperHalfPlane 
ℂ}   [self : ModularFormClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ModularForm.coe_norm`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} (ℋ : Subgroup (GL 
(Fin 2) ℝ)) {F : Type u_1} (f : F) [inst : FunLike F UpperHalfPlane ℂ]   {k : ℤ}
 [inst_1 :…
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ModularForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (F
in 2) ℝ)} {k : ℤ}, IsZeroApply (ModularForm Γ k) UpperHalfPlane ℂ
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `SlashAction.slash_one`：∀ {β : Type u_1} {G : Type u_2} {α : Type u_3} {i
nst : Monoid G} {inst_1 : AddMonoid α} [self : SlashAction β G α]   (k : β) (a :
 α), SlashA…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
lemma ModularForm.norm_eq_zero_iff [ℋ.HasDetPlusMinusOne] [ModularFormClass F 𝒢 k] :
    ModularForm.norm ℋ f = 0 ↔ (f : ℍ → ℂ) = 0 := by
  refine ⟨fun hn ↦ ?_, fun hf ↦ ?_⟩
  · contrapose! hn
    exact norm_ne_zero ℋ hn
  · ext τ
    simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk]
      using ⟨1, by simpa using congr_fun hf τ⟩

open scoped MatrixGroups
/-
**ModularForm.isZero_of_neg_weight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.isZero_of_neg_weight [𝒢.IsArithmetic] {k : Int} (hk : k < 0) (
f : ModularForm 𝒢 k) : f = 0
参数：hk : k < 0；f : ModularForm 𝒢 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.IsArithmetic.isFiniteRelIndexSL`：∀ (𝒢 : Subgroup (GL (Fin 2) ℝ)
) [𝒢.IsArithmetic], 𝒢.IsFiniteRelIndex (Matrix.SpecialLinearGroup.mapGL ℝ).range
· 使用定理 `Subgroup.instHasDetPlusMinusOneFinOfNatNatRealOfIsArithmetic`：∀ {Γ : Sub
group (GL (Fin 2) ℝ)} [h : Γ.IsArithmetic], Γ.HasDetPlusMinusOne
· 使用定理 `Subgroup.instIsArithmeticRangeSpecialLinearGroupFinOfNatNatIntGeneralLin
earGroupRealMapGL`：(Matrix.SpecialLinearGroup.mapGL ℝ).range.IsArithmetic
· 使用定理 `ModularForm.instModularFormClass`：∀ (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ
), ModularFormClass (ModularForm Γ k) Γ k
· 使用定理 `ModularForm.ext`：ModularForm.ext {f g : ModularForm Γ k} (h : forall x, 
f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModularFormClass.levelOne_neg_weight_eq_zero`：levelOne_neg_weight_eq_zer
o (hk : k < 0) (f : F) : ⇑f = 0
· 使用定理 `mul_neg_of_neg_of_pos`：mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : 
a < 0) (hb : 0 < b) : a * b < 0
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Subgroup.relIndex_ne_zero`：∀ {G : Type u_1} [inst : Group G] {H K : Subg
roup G} [H.IsFiniteRelIndex K], H.relIndex K ≠ 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ModularForm.instIsZeroApplyUpperHalfPlaneComplex`：∀ {Γ : Subgroup (GL (F
in 2) ℝ)} {k : ℤ}, IsZeroApply (ModularForm Γ k) UpperHalfPlane ℂ
-/
lemma ModularForm.isZero_of_neg_weight [𝒢.IsArithmetic]
    {k : ℤ} (hk : k < 0) (f : ModularForm 𝒢 k) : f = 0 := by
  suffices ModularForm.norm 𝒮ℒ f = 0 by simpa [ModularForm.norm_eq_zero_iff]
  ext
  rw [ModularFormClass.levelOne_neg_weight_eq_zero
    (mul_neg_of_neg_of_pos hk <| mod_cast Nat.pos_of_ne_zero 𝒢.relIndex_ne_zero)
    (ModularForm.norm 𝒮ℒ f), Pi.zero_apply, zero_apply]
/-
**ModularForm.eq_const_of_weight_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.eq_const_of_weight_zero [𝒢.IsArithmetic] (f : ModularForm 𝒢 0)
 : exists c, (f : ℍ -> Complex) = Function.const ℍ c
参数：f : ModularForm 𝒢 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.NormTrace.0.ModularForm.eq_co
nst_of_weight_zero₀`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetO
ne] (f : ModularForm 𝒢 0),   ∃ c, ⇑f = Function.const UpperHalfPlane c
· 使用定理 `Subgroup.IsArithmetic.inter`：∀ {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.IsAri
thmetic] [Γ'.IsArithmetic], (Γ ⊓ Γ').IsArithmetic
· 使用定理 `Subgroup.instIsArithmeticRangeSpecialLinearGroupFinOfNatNatIntGeneralLin
earGroupRealMapGL`：(Matrix.SpecialLinearGroup.mapGL ℝ).range.IsArithmetic
· 使用定理 `Subgroup.instHasDetOneMinGeneralLinearGroup_1`：∀ {n : Type u_1} [inst : 
Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_2 : CommRing R]   (Γ Γ'
 : Subgroup (GL n R)) [Γ.HasDetOne]…
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `SlashInvariantForm.slash_action_eq'`：∀ {Γ : outParam (Subgroup (GL (Fin 
2) ℝ))} {k : outParam ℤ} (self : SlashInvariantForm Γ k),   ∀ γ ∈ Γ, SlashAction
.map k γ self.toFun = sel…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ModularForm.holo'`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (self : Modul
arForm Γ k), MDiff ⇑self.toSlashInvariantForm
· 使用定理 `ModularForm.bdd_at_cusps'`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (self
 : ModularForm Γ k) {c : OnePoint ℝ},   IsCusp c Γ → c.IsBoundedAt self.toFun k
· 使用引理 `IsCusp.mono`：IsCusp.mono {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoin
t Real} (hGH : 𝒢 <= ℋ) (hc : IsCusp c 𝒢) : IsCusp c ℋ
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
private lemma ModularForm.eq_const_of_weight_zero₀ [𝒢.IsArithmetic] [𝒢.HasDetOne]
    (f : ModularForm 𝒢 0) : ∃ c, (f : ℍ → ℂ) = Function.const ℍ c := by
  -- Consider the norm of `f - (f I)`. This must be a constant, since it's a weight 0 level 1 form.
  let : ModularFormClass (ModularForm 𝒮ℒ (0 * Nat.card (𝒮ℒ ⧸ 𝒢.subgroupOf 𝒮ℒ))) 𝒮ℒ 0 := by
    rw [zero_mul]; infer_instance
  obtain ⟨c, hc⟩ := ModularFormClass.levelOne_weight_zero_const
    (ModularForm.norm 𝒮ℒ (f - .const (f I)))
  -- But the constant must be 0, since `f - f I` vanishes at `I`.
  have : ModularForm.norm 𝒮ℒ (f - .const (f I)) I = 0 := by
    simpa [Finset.prod_eq_zero_iff, QuotientGroup.exists_mk] using ⟨1, by simp⟩
  obtain rfl : c = 0 := by simpa [hc]
  -- So `f - f I` has zero norm, hence it's the zero form.
  simp only [Function.const_zero, FunLike.coe_zero_iff, norm_eq_zero_iff, sub_eq_zero] at hc
  exact ⟨f I, by rw [hc, ModularForm.coe_const, Function.const_apply]⟩
/-
**ModularForm.eq_const_of_weight_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ModularForm.eq_const_of_weight_zero [𝒢.IsArithmetic] (f : ModularForm 𝒢 0)
 : exists c, (f : ℍ -> Complex) = Function.const ℍ c
参数：f : ModularForm 𝒢 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.ModularForms.NormTrace.0.ModularForm.eq_co
nst_of_weight_zero₀`：∀ {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic] [𝒢.HasDetO
ne] (f : ModularForm 𝒢 0),   ∃ c, ⇑f = Function.const UpperHalfPlane c
· 使用定理 `Subgroup.IsArithmetic.inter`：∀ {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} [Γ.IsAri
thmetic] [Γ'.IsArithmetic], (Γ ⊓ Γ').IsArithmetic
· 使用定理 `Subgroup.instIsArithmeticRangeSpecialLinearGroupFinOfNatNatIntGeneralLin
earGroupRealMapGL`：(Matrix.SpecialLinearGroup.mapGL ℝ).range.IsArithmetic
· 使用定理 `Subgroup.instHasDetOneMinGeneralLinearGroup_1`：∀ {n : Type u_1} [inst : 
Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_2 : CommRing R]   (Γ Γ'
 : Subgroup (GL n R)) [Γ.HasDetOne]…
· 使用定理 `Subgroup.instHasDetOneRangeSpecialLinearGroupGeneralLinearGroupMapGL`：∀ 
{n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_2} [inst_
2 : CommRing R] {S : Type u_3}   [inst_3 : CommRing S] [in…
· 使用定理 `SlashInvariantForm.slash_action_eq'`：∀ {Γ : outParam (Subgroup (GL (Fin 
2) ℝ))} {k : outParam ℤ} (self : SlashInvariantForm Γ k),   ∀ γ ∈ Γ, SlashAction
.map k γ self.toFun = sel…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ModularForm.holo'`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (self : Modul
arForm Γ k), MDiff ⇑self.toSlashInvariantForm
· 使用定理 `ModularForm.bdd_at_cusps'`：∀ {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (self
 : ModularForm Γ k) {c : OnePoint ℝ},   IsCusp c Γ → c.IsBoundedAt self.toFun k
· 使用引理 `IsCusp.mono`：IsCusp.mono {𝒢 ℋ : Subgroup (GL (Fin 2) Real)} {c : OnePoin
t Real} (hGH : 𝒢 <= ℋ) (hc : IsCusp c 𝒢) : IsCusp c ℋ
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
lemma ModularForm.eq_const_of_weight_zero [𝒢.IsArithmetic] (f : ModularForm 𝒢 0) :
    ∃ c, (f : ℍ → ℂ) = Function.const ℍ c :=
  eq_const_of_weight_zero₀ (𝒢 := 𝒢 ⊓ 𝒮ℒ) {
    toFun := f
    holo' := f.holo'
    bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono inf_le_left)
    slash_action_eq' γ hγ := f.slash_action_eq' γ hγ.1 }

end ModularForm

end

