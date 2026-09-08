/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable space structure on `WithLp`

If `X` is a measurable space, we set the measurable space structure on `WithLp p X` to be the
same as the one on `X`.
-/

@[expose] public section

open scoped ENNReal

variable (p : ℝ≥0∞) (X : Type*) [MeasurableSpace X]

namespace WithLp

/-
**WithLp.measurableSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：measurableSpace : MeasurableSpace (WithLp p X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance measurableSpace : MeasurableSpace (WithLp p X) :=
  MeasurableSpace.comap ofLp inferInstance

@[fun_prop]
/-
**WithLp.measurable_ofLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：measurable_ofLp : Measurable (@ofLp p X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comap_measurable`：comap_measurable {m : MeasurableSpace β} (f : α -> β) 
: Measurable[m.comap f] f
-/
lemma measurable_ofLp : Measurable (@ofLp p X) := comap_measurable _

@[fun_prop]
/-
**WithLp.measurable_toLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：measurable_toLp : Measurable (@toLp p X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
-/
lemma measurable_toLp : Measurable (@toLp p X) := fun s hs ↦ by
  obtain ⟨t, ht, rfl⟩ := hs
  simpa [Set.preimage_preimage]

variable (Y : Type*) [MeasurableSpace Y] [TopologicalSpace X] [TopologicalSpace Y]
  [BorelSpace X] [BorelSpace Y] [SecondCountableTopologyEither X Y]
/-
**WithLp.borelSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：borelSpace : BorelSpace (WithLp p (X × Y)) where measurable_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithLp.instProdTopologicalSpace.eq_1`：∀ (p : ENNReal) (α : Type u_2) (β 
: Type u_3) [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β],   WithLp.
instProdTopologicalSpace p…
· 使用定理 `borel_comap`：borel_comap {f : α -> β} {t : TopologicalSpace β} : @borel 
α (t.induced f) = (@borel β t).comap f
· 使用定理 `WithLp.measurableSpace.eq_1`：∀ (p : ENNReal) (X : Type u_1) [inst : Meas
urableSpace X],   WithLp.measurableSpace p X = MeasurableSpace.comap WithLp.ofLp
 inferInstance
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
-/
instance borelSpace : BorelSpace (WithLp p (X × Y)) where
  measurable_eq := by
    rw [instProdTopologicalSpace, borel_comap, measurableSpace,
      BorelSpace.measurable_eq (α := X × Y)]

end WithLp

namespace PiLp

variable {ι : Type*} {X : ι → Type*} [Countable ι] [∀ i, MeasurableSpace (X i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, BorelSpace (X i)] [∀ i, SecondCountableTopology (X i)]

/-
**PiLp.borelSpace** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：borelSpace : BorelSpace (PiLp p X) where measurable_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.topologicalSpace.eq_1`：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type
 u_4) [inst : (i : ι) → TopologicalSpace (β i)],   PiLp.topologicalSpace p β = T
opologicalSpace.…
· 使用定理 `borel_comap`：borel_comap {f : α -> β} {t : TopologicalSpace β} : @borel 
α (t.induced f) = (@borel β t).comap f
· 使用定理 `WithLp.measurableSpace.eq_1`：∀ (p : ENNReal) (X : Type u_1) [inst : Meas
urableSpace X],   WithLp.measurableSpace p X = MeasurableSpace.comap WithLp.ofLp
 inferInstance
· 使用定理 `BorelSpace.measurable_eq`：∀ {α : Type u_6} {inst : TopologicalSpace α} {
inst_1 : MeasurableSpace α} [self : BorelSpace α], inst_1 = borel α
-/
instance borelSpace : BorelSpace (PiLp p X) where
  measurable_eq := by
    rw [topologicalSpace, borel_comap, WithLp.measurableSpace,
      BorelSpace.measurable_eq (α := Π i, X i)]

end PiLp

namespace MeasurableEquiv

/-- The map from `X` to `WithLp p X` as a measurable equivalence. -/
/-
**MeasurableEquiv.toLp** 是 Mathlib 中的一个定义，位于命名空间 `MeasurableEquiv`。
形式化陈述：(p : ENNReal) → (X : Type u_1) → [inst : MeasurableSpace X] → X ≃ᵐ WithLp 
p X
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `WithLp.measurable_toLp`：measurable_toLp : Measurable (@toLp p X)
· 使用引理 `WithLp.measurable_ofLp`：measurable_ofLp : Measurable (@ofLp p X)

--- 原说明 ---
The map from `X` to `WithLp p X` as a measurable equivalence.
-/
protected def toLp : X ≃ᵐ (WithLp p X) where
  toEquiv := (WithLp.equiv p X).symm
  measurable_toFun := WithLp.measurable_toLp p X
  measurable_invFun := WithLp.measurable_ofLp p X
/-
**MeasurableEquiv.coe_toLp** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithLp.toLp p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toLp : ⇑(MeasurableEquiv.toLp p X) = WithLp.toLp p := rfl
/-
**MeasurableEquiv.coe_toLp_symm** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：coe_toLp_symm : ⇑(MeasurableEquiv.toLp p X).symm = WithLp.ofLp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toLp_symm : ⇑(MeasurableEquiv.toLp p X).symm = WithLp.ofLp := rfl

@[simp]
/-
**MeasurableEquiv.toLp_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：toLp_apply (x : X) : MeasurableEquiv.toLp p X x = WithLp.toLp p x
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLp_apply (x : X) : MeasurableEquiv.toLp p X x = WithLp.toLp p x := rfl

@[simp]
/-
**MeasurableEquiv.toLp_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasurableEquiv`。
形式化陈述：toLp_symm_apply (x : WithLp p X) : (MeasurableEquiv.toLp p X).symm x = Wit
hLp.ofLp x
参数：x : WithLp p X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLp_symm_apply (x : WithLp p X) :
    (MeasurableEquiv.toLp p X).symm x = WithLp.ofLp x := rfl

end MeasurableEquiv

