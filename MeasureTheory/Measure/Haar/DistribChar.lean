/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The distributive character of Haar measures

Given a group `G` acting by additive morphisms on a locally compact additive commutative group `A`,
and an element `g : G`, one can pull back the Haar measure `μ` of `A`
along the map `(g • ·) : A → A` to get another Haar measure `μ'` on `A`.
By unicity of Haar measures, there exists some nonnegative real number `r` such that `μ' = r • μ`.
We can thus define a map `distribHaarChar : G → ℝ≥0` sending `g` to its associated real number `r`.
Furthermore, this number doesn't depend on the Haar measure `μ` we started with,
and `distribHaarChar` is a group homomorphism.

## See also

`MeasureTheory.Measure.modularCharacter` for the analogous definition when the action is
multiplicative instead of distributive.

[Zulip](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/canonical.20norm.20coming.20from.20Haar.20measure/near/480050592)
-/

@[expose] public section

open MeasureTheory.Measure
open scoped NNReal Pointwise ENNReal

namespace MeasureTheory
variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A] {g : G}

variable (A) in
/-- The distributive Haar character of a group `G` acting distributively on a group `A` is the
unique positive real number `Δ(g)` such that `μ (g • s) = Δ(g) * μ s` for all Haar
measures `μ : Measure A`, set `s : Set A` and `g : G`. -/
@[simps -isSimp]
/-
**MeasureTheory.distribHaarChar** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：distribHaarChar : G ->* Real>=0
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distributive Haar character of a group `G` acting distributively on a group 
`A` is the
unique positive real number `Δ(g)` such that `μ (g • s) = Δ(g) * μ s` for all Ha
ar
measures `μ : Measure A`, set `s : Set A` and `g : G`.
-/
noncomputable def distribHaarChar : G →* ℝ≥0 :=
  letI := borel A
  haveI : BorelSpace A := ⟨rfl⟩
  {
    toFun g := addHaarScalarFactor (DomMulAct.mk g • addHaar) (addHaar (G := A))
    map_one' := by simp
    map_mul' g g' := by
      simp_rw [DomMulAct.mk_mul]
      rw [addHaarScalarFactor_eq_mul _ (DomMulAct.mk g' • addHaar (G := A))]
      congr 1
      simp_rw [mul_smul]
      rw [addHaarScalarFactor_domSMul]
  }
/-
**MeasureTheory.distribHaarChar_pos** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：distribHaarChar_pos : 0 < distribHaarChar A g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
-/
lemma distribHaarChar_pos : 0 < distribHaarChar A g :=
  pos_iff_ne_zero.mpr ((Group.isUnit g).map (distribHaarChar A)).ne_zero

variable [MeasurableSpace A] [BorelSpace A] {μ : Measure A} [μ.IsAddHaarMeasure]

variable (μ) in
/-
**MeasureTheory.addHaarScalarFactor_smul_eq_distribHaarChar** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory`。
形式化陈述：addHaarScalarFactor_smul_eq_distribHaarChar (g : G) : addHaarScalarFactor 
(DomMulAct.mk g • μ) μ = distribHaarChar A g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
· 使用定理 `ContinuousConstSMul.toMeasurableConstSMul`：∀ {M : Type u_7} {α : Type u_
8} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [BorelSpace α]   [in
st_3 : SMul M α] [ContinuousCon…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.domSMul`：∀ {G : Type u_3} {A : Ty
pe u_4} [inst : Group G] [inst_1 : AddCommGroup A] [inst_2 : DistribMulAction G 
A]   [inst_3 : MeasurableSpace A] [i…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用引理 `MeasureTheory.Measure.addHaarScalarFactor_smul_congr'`：addHaarScalarFact
or_smul_congr' (g : Gᵈᵐᵃ) : addHaarScalarFactor (g • μ) μ = addHaarScalarFactor 
(g • ν) ν
· 使用定理 `MeasureTheory.Measure.isAddHaarMeasure_addHaarMeasure`：∀ {G : Type u_1} 
[inst : AddGroup G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGrou
p G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma addHaarScalarFactor_smul_eq_distribHaarChar (g : G) :
    addHaarScalarFactor (DomMulAct.mk g • μ) μ = distribHaarChar A g := by
  borelize A
  exact addHaarScalarFactor_smul_congr' ..

variable (μ) in
/-
**MeasureTheory.addHaarScalarFactor_smul_inv_eq_distribHaarChar** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory`。
形式化陈述：addHaarScalarFactor_smul_inv_eq_distribHaarChar (g : G) : addHaarScalarFac
tor μ ((DomMulAct.mk g)⁻¹ • μ) = distribHaarChar A g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousConstSMul.toMeasurableConstSMul`：∀ {M : Type u_7} {α : Type u_
8} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [BorelSpace α]   [in
st_3 : SMul M α] [ContinuousCon…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.domSMul`：∀ {G : Type u_3} {A : Ty
pe u_4} [inst : Group G] [inst_1 : AddCommGroup A] [inst_2 : DistribMulAction G 
A]   [inst_3 : MeasurableSpace A] [i…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.addHaarScalarFactor_domSMul`：addHaarScalarFactor_d
omSMul (g : Gᵈᵐᵃ) : addHaarScalarFactor (g • μ) (g • ν) = addHaarScalarFactor μ 
ν
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.addHaarScalarFactor.congr_simp`：∀ {G : Type u_1} [
inst : TopologicalSpace G] [inst_1 : AddGroup G] [inst_2 : IsTopologicalAddGroup
 G]   [inst_3 : MeasurableSpace G] [inst_4…
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `MeasureTheory.addHaarScalarFactor_smul_eq_distribHaarChar`：addHaarScalar
Factor_smul_eq_distribHaarChar (g : G) : addHaarScalarFactor (DomMulAct.mk g • μ
) μ = distribHaarChar A g
-/
lemma addHaarScalarFactor_smul_inv_eq_distribHaarChar (g : G) :
    addHaarScalarFactor μ ((DomMulAct.mk g)⁻¹ • μ) = distribHaarChar A g := by
  rw [← addHaarScalarFactor_domSMul _ _ (DomMulAct.mk g)]
  simp_rw [← mul_smul, mul_inv_cancel, one_smul]
  exact addHaarScalarFactor_smul_eq_distribHaarChar ..

variable (μ) in
/-
**MeasureTheory.addHaarScalarFactor_smul_eq_distribHaarChar_inv** 是 Mathlib 中的一个
引理，位于命名空间 `MeasureTheory`。
形式化陈述：addHaarScalarFactor_smul_eq_distribHaarChar_inv (g : G) : addHaarScalarFac
tor μ (DomMulAct.mk g • μ) = (distribHaarChar A g)⁻¹
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousConstSMul.toMeasurableConstSMul`：∀ {M : Type u_7} {α : Type u_
8} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [BorelSpace α]   [in
st_3 : SMul M α] [ContinuousCon…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.domSMul`：∀ {G : Type u_3} {A : Ty
pe u_4} [inst : Group G] [inst_1 : AddCommGroup A] [inst_2 : DistribMulAction G 
A]   [inst_3 : MeasurableSpace A] [i…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用引理 `MeasureTheory.addHaarScalarFactor_smul_inv_eq_distribHaarChar`：addHaarSc
alarFactor_smul_inv_eq_distribHaarChar (g : G) : addHaarScalarFactor μ ((DomMulA
ct.mk g)⁻¹ • μ) = distribHaarChar A g
· 使用引理 `DomMulAct.mk_inv`：mk_inv [Inv M] (a : M) : mk (a⁻¹) = (mk a)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma addHaarScalarFactor_smul_eq_distribHaarChar_inv (g : G) :
    addHaarScalarFactor μ (DomMulAct.mk g • μ) = (distribHaarChar A g)⁻¹ := by
  rw [← map_inv, ← addHaarScalarFactor_smul_inv_eq_distribHaarChar μ, DomMulAct.mk_inv, inv_inv]

variable [Regular μ] {s : Set A}

variable (μ) in
/-
**MeasureTheory.distribHaarChar_mul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：distribHaarChar_mul (g : G) (s : Set A) : distribHaarChar A g * μ s = μ (g
 • s)
参数：g : G；s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousConstSMul.toMeasurableConstSMul`：∀ {M : Type u_7} {α : Type u_
8} [inst : TopologicalSpace α] [inst_1 : MeasurableSpace α] [BorelSpace α]   [in
st_3 : SMul M α] [ContinuousCon…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `MeasureTheory.Measure.domSMul_apply`：domSMul_apply (μ : Measure A) (g : 
Gᵈᵐᵃ) (s : Set A) : (g • μ) s = μ (DomMulAct.mk.symm g • s)
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.nnreal_smul_coe_apply`：nnreal_smul_coe_apply {_m :
 MeasurableSpace α} (c : Real>=0) (μ : Measure α) (s : Set α) : c • μ s = c * μ 
s
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts`：∀ {G
 : Type u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : Measura
bleSpace G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.domSMul`：∀ {G : Type u_3} {A : Ty
pe u_4} [inst : Group G] [inst_1 : AddCommGroup A] [inst_2 : DistribMulAction G 
A]   [inst_3 : MeasurableSpace A] [i…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用引理 `MeasureTheory.addHaarScalarFactor_smul_eq_distribHaarChar`：addHaarScalar
Factor_smul_eq_distribHaarChar (g : G) : addHaarScalarFactor (DomMulAct.mk g • μ
) μ = distribHaarChar A g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `MeasureTheory.Measure.Regular.toIsFiniteMeasureOnCompacts`：∀ {α : Type u
_1} {inst : MeasurableSpace α} {inst_1 : TopologicalSpace α} {μ : MeasureTheory.
Measure α}   [self : μ.Regular], MeasureTheory.…
· 使用定理 `MeasureTheory.Measure.Regular.domSMul`：∀ {G : Type u_3} {A : Type u_4} [
inst : Group G] [inst_1 : AddCommGroup A] [inst_2 : DistribMulAction G A]   [ins
t_3 : MeasurableSpace A] [i…
· 使用定理 `MeasureTheory.Measure.isAddLeftInvariant_eq_smul_of_regular`：∀ {G : Type
 u_1} [inst : TopologicalSpace G] [inst_1 : AddGroup G] [inst_2 : IsTopologicalA
ddGroup G]   [inst_3 : MeasurableSpace G] [inst_4…
-/
lemma distribHaarChar_mul (g : G) (s : Set A) : distribHaarChar A g * μ s = μ (g • s) := by
  have : (DomMulAct.mk g • μ) s = μ (g • s) := by simp [domSMul_apply]
  rw [eq_comm, ← nnreal_smul_coe_apply, ← addHaarScalarFactor_smul_eq_distribHaarChar μ,
    ← this, ← Measure.smul_apply, ← isAddLeftInvariant_eq_smul_of_regular]
/-
**MeasureTheory.distribHaarChar_eq_div** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：distribHaarChar_eq_div (hs₀ : μ s != 0) (hs : μ s != ∞) (g : G) : distribH
aarChar A g = μ (g • s) / μ s
参数：hs₀ : μ s != 0；hs : μ s != ∞；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.distribHaarChar_mul`：distribHaarChar_mul (g : G) (s : Set 
A) : distribHaarChar A g * μ s = μ (g • s)
· 使用定理 `ENNReal.mul_div_cancel_right`：∀ {a b : ENNReal}, b ≠ 0 → b ≠ ⊤ → a * b /
 b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma distribHaarChar_eq_div (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (g : G) :
    distribHaarChar A g = μ (g • s) / μ s := by
  rw [← distribHaarChar_mul, ENNReal.mul_div_cancel_right] <;> simp [*]
/-
**MeasureTheory.distribHaarChar_eq_of_measure_smul_eq_mul** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory`。
形式化陈述：distribHaarChar_eq_of_measure_smul_eq_mul (hs₀ : μ s != 0) (hs : μ s != ∞)
 {r : Real>=0} (hμgs : μ (g • s) = r * μ s) : distribHaarChar A g = r
参数：hs₀ : μ s != 0；hs : μ s != ∞；hμgs : μ (g • s) = r * μ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.coe_injective`：coe_injective : Injective ((↑) : Real>=0 -> Real>
=0∞)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.distribHaarChar_eq_div`：distribHaarChar_eq_div (hs₀ : μ s 
!= 0) (hs : μ s != ∞) (g : G) : distribHaarChar A g = μ (g • s) / μ s
· 使用定理 `ENNReal.mul_div_cancel_right`：∀ {a b : ENNReal}, b ≠ 0 → b ≠ ⊤ → a * b /
 b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma distribHaarChar_eq_of_measure_smul_eq_mul (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) {r : ℝ≥0}
    (hμgs : μ (g • s) = r * μ s) : distribHaarChar A g = r := by
  refine ENNReal.coe_injective ?_
  rw [distribHaarChar_eq_div hs₀ hs, hμgs, ENNReal.mul_div_cancel_right] <;> simp [*]

end MeasureTheory

