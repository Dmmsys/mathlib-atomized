/-
Copyright (c) 2022 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Haar quotient measure

In this file, we consider properties of fundamental domains and measures for the action of a
subgroup `Γ` of a topological group `G` on `G` itself. Let `μ` be a measure on `G ⧸ Γ`.

## Main results

* `MeasureTheory.QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient`: If `μ` satisfies
  `QuotientMeasureEqMeasurePreimage` relative to a both left- and right-invariant measure on `G`,
  then it is a `G` invariant measure on `G ⧸ Γ`.

The next two results assume that `Γ` is normal, and that `G` is equipped with a left- and
right-invariant measure.

* `MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient`: If `μ` satisfies
  `QuotientMeasureEqMeasurePreimage`, then `μ` is a left-invariant measure.

* `MeasureTheory.leftInvariantIsQuotientMeasureEqMeasurePreimage`: If `μ` is left-invariant, and
  the action of `Γ` on `G` has finite covolume, and `μ` satisfies the right scaling condition, then
  it satisfies `QuotientMeasureEqMeasurePreimage`. This is a converse to
  `MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient`.

The last result assumes that `G` is locally compact, that `Γ` is countable and normal, that its
action on `G` has a fundamental domain, and that `μ` is a finite measure. We also assume that `G`
is equipped with a sigma-finite Haar measure.

* `MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient`: If `μ` satisfies
  `QuotientMeasureEqMeasurePreimage`, then it is itself Haar. This is a variant of
  `MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient`.

Note that a group `G` with Haar measure that is both left and right invariant is called
**unimodular**.
-/

public section

open Set MeasureTheory TopologicalSpace MeasureTheory.Measure

open scoped Pointwise NNReal ENNReal

section

/-- Measurability of the action of the topological group `G` on the left-coset space `G / Γ`. -/
@[to_additive /-- Measurability of the action of the additive topological group `G` on the
  left-coset space `G / Γ`. -/]
/-
**QuotientGroup.measurableSMul** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {Γ : Subgroup G} [inst_1 : MeasurableSpa
ce G] [inst_2 : TopologicalSpace G]   [IsTopologicalGroup G] [BorelSpace G] [Bor
elSpace (G ⧸ Γ)], MeasurableSMul G (G ⧸ Γ)
参数：G ⧸ Γ；G ⧸ Γ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousSMul.toMeasurableSMul`：∀ {M : Type u_7} {α : Type u_8} [inst :
 TopologicalSpace M] [inst_1 : TopologicalSpace α] [inst_2 : MeasurableSpace M] 
  [inst_3 : Measurabl…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Measurable.smul_const`：Measurable.smul_const (hf : Measurable f) (y : X)
 : Measurable fun x => f x • y
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
-/
instance QuotientGroup.measurableSMul {G : Type*} [Group G] {Γ : Subgroup G} [MeasurableSpace G]
    [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [BorelSpace (G ⧸ Γ)] :
    MeasurableSMul G (G ⧸ Γ) where

end

section smulInvariantMeasure

variable {G : Type*} [Group G] [MeasurableSpace G] (ν : Measure G) {Γ : Subgroup G}
  {μ : Measure (G ⧸ Γ)}
  [QuotientMeasureEqMeasurePreimage ν μ]

/-- Given a subgroup `Γ` of a topological group `G` with measure `ν`, and a measure 'μ' on the
  quotient `G ⧸ Γ` satisfying `QuotientMeasureEqMeasurePreimage`, the restriction
  of `ν` to a fundamental domain is measure-preserving with respect to `μ`. -/
@[to_additive /-- Given a subgroup `Γ` of a topological additive group `G` with measure `ν`, and a
  measure 'μ' on the quotient `G ⧸ Γ` satisfying `AddQuotientMeasureEqMeasurePreimage`, the
  restriction of `ν` to a fundamental domain is measure-preserving with respect to `μ`. -/]
/-
**measurePreserving_quotientGroup_mk_of_QuotientMeasureEqMeasurePreimage** 是 Mat
hlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurePreserving_quotientGroup_mk_of_QuotientMeasureEqMeasurePreimage {𝓕 
: Set G} (h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν) (μ : Measure (G ⧸ Γ)) [QuotientMeas
ureEqMeasurePreimage ν μ] : MeasurePreserving (@QuotientGroup.mk G _ Γ) (ν.restr
ict 𝓕) μ
参数：h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν；μ : Measure (G ⧸ Γ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.measurePreserving_quotient_mk`：∀ {G : 
Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : Mea
surableSpace α]   {ν : MeasureTheory.Measure α} {𝓕 : …
-/
theorem measurePreserving_quotientGroup_mk_of_QuotientMeasureEqMeasurePreimage
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν) (μ : Measure (G ⧸ Γ))
    [QuotientMeasureEqMeasurePreimage ν μ] :
    MeasurePreserving (@QuotientGroup.mk G _ Γ) (ν.restrict 𝓕) μ :=
  h𝓕.measurePreserving_quotient_mk μ

local notation "π" => @QuotientGroup.mk G _ Γ

variable [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] [PolishSpace G]
  [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)]

/-- If `μ` satisfies `QuotientMeasureEqMeasurePreimage` relative to a both left- and right-
  invariant measure `ν` on `G`, then it is a `G` invariant measure on `G ⧸ Γ`. -/
@[to_additive /-- If `μ` satisfies `AddQuotientMeasureEqMeasurePreimage` relative to a both left-
  and right-invariant measure `ν` on `G`, then it is a `G` invariant measure on `G ⧸ Γ`. -/]
/-
**MeasureTheory.QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient**
 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasureTheory.QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotie
nt [IsMulLeftInvariant ν] [hasFun : HasFundamentalDomain Γ.op G ν] : SMulInvaria
ntMeasure G (G ⧸ Γ) μ where measure_preimage_smul g A hA
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
· 使用定理 `MeasureTheory.HasFundamentalDomain.ExistsIsFundamentalDomain`：∀ {G : Typ
e u_6} {α : Type u_7} {inst : One G} {inst_1 : SMul G α} {inst_2 : MeasurableSpa
ce α}   {ν : autoParam (MeasureTheory.Measure α) M…
· 使用定理 `MeasureTheory.IsFundamentalDomain.smul_of_comm`：smul_of_comm {G' : Type*
} [Group G'] [MulAction G' α] [MeasurableConstSMul G' α] [SMulInvariantMeasure G
' α μ] [SMulCommClass G' G α] (h : I…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `measurableSMul_of_mul`：∀ (M : Type u_2) [inst : Mul M] [inst_1 : Measura
bleSpace M] [MeasurableMul M], MeasurableSMul M M
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.smulInvariantMeasure`：∀ {G : Ty
pe u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 : Mul G
] [μ.IsMulLeftInvariant],   MeasureTheory.SMulInvar…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IsFundamentalDomain.projection_respects_measure_apply`：∀ {
G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 :
 MeasurableSpace α]   {ν : MeasureTheory.Measure α} (μ : …
· 使用定理 `measurableSet_preimage`：measurableSet_preimage {t : Set β} (hf : Measura
ble f) (ht : MeasurableSet t) : MeasurableSet (f ⁻¹' t)
· 使用定理 `MeasurableConstSMul.measurable_const_smul`：∀ {M : Type u_2} {α : Type u_
3} {inst : SMul M α} {inst_1 : MeasurableSpace α} [self : MeasurableConstSMul M 
α] (c : M),   Measurable fun x …
· 使用定理 `QuotientGroup.measurableSMul`：∀ {G : Type u_1} [inst : Group G] {Γ : Sub
group G} [inst_1 : MeasurableSpace G] [inst_2 : TopologicalSpace G]   [IsTopolog
icalGroup G] [Bore…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.preimage_inter`：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f
 ⁻¹' s inter f ⁻¹' t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 33 条，此处仅展示前 30 条）
-/
lemma MeasureTheory.QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient
    [IsMulLeftInvariant ν] [hasFun : HasFundamentalDomain Γ.op G ν] :
    SMulInvariantMeasure G (G ⧸ Γ) μ where
  measure_preimage_smul g A hA := by
    have meas_π : Measurable π := continuous_quotient_mk'.measurable
    obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
    have h𝓕_translate_fundom : IsFundamentalDomain Γ.op (g • 𝓕) ν := h𝓕.smul_of_comm g
    rw [h𝓕.projection_respects_measure_apply (μ := μ)
      (meas_π (measurableSet_preimage (measurable_const_smul g) hA)),
      h𝓕_translate_fundom.projection_respects_measure_apply (μ := μ) hA]
    change ν ((π ⁻¹' _) ∩ _) = ν ((π ⁻¹' _) ∩ _)
    set π_preA := π ⁻¹' A
    have : π ⁻¹' ((fun x : G ⧸ Γ => g • x) ⁻¹' A) = (g * ·) ⁻¹' π_preA := by ext1; simp [π_preA]
    rw [this]
    have : ν ((g * ·) ⁻¹' π_preA ∩ 𝓕) = ν (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕) := by
      trans ν ((g * ·) ⁻¹' (π_preA ∩ (g⁻¹ * ·) ⁻¹' 𝓕))
      · rw [preimage_inter]
        congr 2
        simp [Set.preimage]
      rw [measure_preimage_mul]
    rw [this, ← preimage_smul_inv]; rfl

end smulInvariantMeasure

section normal

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] [PolishSpace G] {Γ : Subgroup G} [Subgroup.Normal Γ]
  [T2Space (G ⧸ Γ)] [SecondCountableTopology (G ⧸ Γ)] {μ : Measure (G ⧸ Γ)}

section mulInvariantMeasure

variable (ν : Measure G) [IsMulLeftInvariant ν]

/-- If `μ` on `G ⧸ Γ` satisfies `QuotientMeasureEqMeasurePreimage` relative to a both left- and
  right-invariant measure on `G` and `Γ` is a normal subgroup, then `μ` is a left-invariant
  measure. -/
@[to_additive /-- If `μ` on `G ⧸ Γ` satisfies `AddQuotientMeasureEqMeasurePreimage` relative to a
  both left- and right-invariant measure on `G` and `Γ` is a normal subgroup, then `μ` is a
  left-invariant measure. -/]
/-
**MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient** 
是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotien
t [hasFun : HasFundamentalDomain Γ.op G ν] [QuotientMeasureEqMeasurePreimage ν μ
] : μ.IsMulLeftInvariant where map_mul_left_eq_self x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_preimage_smul`：measure_preimage_smul (c : G) (s : 
Set α) : μ ((c • ·) ⁻¹' s) = μ s
· 使用引理 `MeasureTheory.QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quot
ient`：MeasureTheory.QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotie
nt [IsMulLeftInvariant ν] [hasFun : HasFundamentalDomain Γ.op G ν]…
-/
lemma MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient
    [hasFun : HasFundamentalDomain Γ.op G ν] [QuotientMeasureEqMeasurePreimage ν μ] :
    μ.IsMulLeftInvariant where
  map_mul_left_eq_self x := by
    ext A hA
    obtain ⟨x₁, h⟩ := @Quotient.exists_rep _ (QuotientGroup.leftRel Γ) x
    convert! measure_preimage_smul μ x₁ A using 1
    · rw [← h, Measure.map_apply (measurable_const_mul _) hA]
      simp [← MulAction.Quotient.coe_smul_out, ← Quotient.mk''_eq_mk]
    exact smulInvariantMeasure_quotient ν

variable [Countable Γ] [IsMulRightInvariant ν] [SigmaFinite ν]
  [IsMulLeftInvariant μ] [SigmaFinite μ]

local notation "π" => @QuotientGroup.mk G _ Γ

/-- Assume that a measure `μ` is `IsMulLeftInvariant`, that the action of `Γ` on `G` has a
measurable fundamental domain `s` with positive finite volume, and that there is a single measurable
set `V ⊆ G ⧸ Γ` along which the pullback of `μ` and `ν` agree (so the scaling is right). Then
`μ` satisfies `QuotientMeasureEqMeasurePreimage`. The main tool of the proof is the uniqueness of
left invariant measures, if normalized by a single positive finite-measured set. -/
@[to_additive
/-- Assume that a measure `μ` is `IsAddLeftInvariant`, that the action of `Γ` on `G` has a
measurable fundamental domain `s` with positive finite volume, and that there is a single measurable
set `V ⊆ G ⧸ Γ` along which the pullback of `μ` and `ν` agree (so the scaling is right). Then
`μ` satisfies `AddQuotientMeasureEqMeasurePreimage`. The main tool of the proof is the uniqueness of
left invariant measures, if normalized by a single positive finite-measured set. -/]
/-
**MeasureTheory.Measure.IsMulLeftInvariant.quotientMeasureEqMeasurePreimage_of_s
et** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.Measure.IsMulLeftInvariant.quotientMeasureEqMeasurePreimage_
of_set {s : Set G} (fund_dom_s : IsFundamentalDomain Γ.op s ν) {V : Set (G ⧸ Γ)}
 (meas_V : MeasurableSet V) (neZeroV : μ V != 0) (hV : μ V = ν (π ⁻¹' V inter s)
) (neTopV : μ V != ⊤) : QuotientMeasureEqMeasurePreimage ν μ
参数：fund_dom_s : IsFundamentalDomain Γ.op s ν；G ⧸ Γ；meas_V : MeasurableSet V；neZe
roV : μ V != 0；hV : μ V = ν (π ⁻¹' V inter s)；neTopV : μ V != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.quotientMeasureEqMeasurePreimage`：∀ {G
 : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : 
MeasurableSpace α]   {ν : MeasureTheory.Measure α} [Meas…
· 使用定理 `MeasureTheory.Subgroup.smulInvariantMeasure`：∀ {G : Type u_3} {α : Type 
u_4} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpace α]   {μ
 : MeasureTheory.Measure α} [Meas…
· 使用定理 `MeasureTheory.Measure.IsMulRightInvariant.toSMulInvariantMeasure_op`：∀ {
G : Type u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 :
 Mul G] [μ.IsMulRightInvariant],   MeasureTheory.SMulInva…
· 使用定理 `Subgroup.instCountableSubtypeMulOppositeMemOp`：∀ {G : Type u_2} [inst : 
Group G] (H : Subgroup G) [Countable ↥H], Countable ↥H.op
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
· 使用定理 `MeasureTheory.IsFundamentalDomain.quotientMeasureEqMeasurePreimage_quoti
entMeasure`：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction
 G α] [inst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} [Meas…
· 使用引理 `MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quoti
ent`：MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient
 [hasFun : HasFundamentalDomain Γ.op G ν] [QuotientMeasureEqMeasu…
· 使用定理 `MeasureTheory.QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient`：∀ {G
 : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : 
MeasurableSpace α]   {ν : MeasureTheory.Measure α} [Meas…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_eq_div_smul`：measure_eq_div_smul (h2s : ν' s != 0)
 (h3s : ν' s != ∞) : μ' = (μ' s / ν' s) • ν'
· 使用定理 `ContinuousMul.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Mul γ] [Con…
· 使用定理 `ContinuousInv.measurableInv`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Inv γ]   [ContinuousInv 
γ], MeasurableInv…
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `measurableSet_quotient`：measurableSet_quotient {s : Setoid α} {t : Set (
Quotient s)} : MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t)
（共 32 条，此处仅展示前 30 条）
-/
theorem MeasureTheory.Measure.IsMulLeftInvariant.quotientMeasureEqMeasurePreimage_of_set {s : Set G}
    (fund_dom_s : IsFundamentalDomain Γ.op s ν) {V : Set (G ⧸ Γ)}
    (meas_V : MeasurableSet V) (neZeroV : μ V ≠ 0) (hV : μ V = ν (π ⁻¹' V ∩ s))
    (neTopV : μ V ≠ ⊤) : QuotientMeasureEqMeasurePreimage ν μ := by
  apply fund_dom_s.quotientMeasureEqMeasurePreimage
  ext U _
  have meas_π : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := continuous_quotient_mk'.measurable
  let μ' : Measure (G ⧸ Γ) := (ν.restrict s).map π
  have has_fund : HasFundamentalDomain Γ.op G ν := ⟨⟨s, fund_dom_s⟩⟩
  have i : QuotientMeasureEqMeasurePreimage ν μ' :=
    fund_dom_s.quotientMeasureEqMeasurePreimage_quotientMeasure
  have : μ'.IsMulLeftInvariant :=
    MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient ν
  suffices μ = μ' by
    rw [this]
    rfl
  have : SigmaFinite μ' := i.sigmaFiniteQuotient
  rw [measure_eq_div_smul μ' μ neZeroV neTopV, hV]
  symm
  suffices (μ' V / ν (QuotientGroup.mk ⁻¹' V ∩ s)) = 1 by rw [this, one_smul]
  rw [Measure.map_apply meas_π meas_V, Measure.restrict_apply]
  · convert! ENNReal.div_self ..
    · exact trans hV.symm neZeroV
    · exact trans hV.symm neTopV
  exact measurableSet_quotient.mp meas_V

/-- If a measure `μ` is left-invariant and satisfies the right scaling condition, then it
  satisfies `QuotientMeasureEqMeasurePreimage`. -/
@[to_additive /-- If a measure `μ` is
left-invariant and satisfies the right scaling condition, then it satisfies
`AddQuotientMeasureEqMeasurePreimage`. -/]
/-
**MeasureTheory.leftInvariantIsQuotientMeasureEqMeasurePreimage** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：MeasureTheory.leftInvariantIsQuotientMeasureEqMeasurePreimage [IsFiniteMea
sure μ] [hasFun : HasFundamentalDomain Γ.op G ν] (h : covolume Γ.op G ν = μ univ
) : QuotientMeasureEqMeasurePreimage ν μ
参数：h : covolume Γ.op G ν = μ univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.HasFundamentalDomain.ExistsIsFundamentalDomain`：∀ {G : Typ
e u_6} {α : Type u_7} {inst : One G} {inst_1 : SMul G α} {inst_2 : MeasurableSpa
ce α}   {ν : autoParam (MeasureTheory.Measure α) M…
· 使用定理 `MeasureTheory.measure_lt_top`：measure_lt_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s < ∞
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.IsFundamentalDomain.covolume_eq_volume`：∀ {G : Type u_1} {
α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpac
e α]   (ν : MeasureTheory.Measure α) [Coun…
· 使用定理 `Subgroup.instCountableSubtypeMulOppositeMemOp`：∀ {G : Type u_2} [inst : 
Group G] (H : Subgroup G) [Countable ↥H], Countable ↥H.op
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Subgroup.smulInvariantMeasure`：∀ {G : Type u_3} {α : Type 
u_4} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpace α]   {μ
 : MeasureTheory.Measure α} [Meas…
· 使用定理 `MeasureTheory.Measure.IsMulRightInvariant.toSMulInvariantMeasure_op`：∀ {
G : Type u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 :
 Mul G] [μ.IsMulRightInvariant],   MeasureTheory.SMulInva…
· 使用定理 `MeasureTheory.IsFundamentalDomain.quotientMeasureEqMeasurePreimage_of_ze
ro`：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [i
nst_2 : MeasurableSpace α]   {ν : MeasureTheory.Measure α} [Meas…
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.quotientMeasureEqMeasurePreimag
e_of_set`：MeasureTheory.Measure.IsMulLeftInvariant.quotientMeasureEqMeasurePreim
age_of_set {s : Set G} (fund_dom_s : IsFundamentalDomain Γ.op s ν) {V …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem MeasureTheory.leftInvariantIsQuotientMeasureEqMeasurePreimage [IsFiniteMeasure μ]
    [hasFun : HasFundamentalDomain Γ.op G ν]
    (h : covolume Γ.op G ν = μ univ) : QuotientMeasureEqMeasurePreimage ν μ := by
  obtain ⟨s, fund_dom_s⟩ := hasFun.ExistsIsFundamentalDomain
  have finiteCovol : μ univ < ⊤ := measure_lt_top μ univ
  rw [fund_dom_s.covolume_eq_volume] at h
  by_cases meas_s_ne_zero : ν s = 0
  · convert! fund_dom_s.quotientMeasureEqMeasurePreimage_of_zero meas_s_ne_zero
    rw [← @measure_univ_eq_zero, ← h, meas_s_ne_zero]
  apply IsMulLeftInvariant.quotientMeasureEqMeasurePreimage_of_set (fund_dom_s := fund_dom_s)
    (meas_V := MeasurableSet.univ)
  · rw [← h]
    exact meas_s_ne_zero
  · rw [← h]
    simp
  · rw [← h]
    convert! finiteCovol.ne

end mulInvariantMeasure

section haarMeasure

variable [Countable Γ] (ν : Measure G) [IsHaarMeasure ν] [IsMulRightInvariant ν]

local notation "π" => @QuotientGroup.mk G _ Γ

/-- If a measure `μ` on the quotient `G ⧸ Γ` of a group `G` by a discrete normal subgroup `Γ` having
fundamental domain, satisfies `QuotientMeasureEqMeasurePreimage` relative to a standardized choice
of Haar measure on `G`, and assuming `μ` is finite, then `μ` is itself Haar.
TODO: Is it possible to drop the assumption that `μ` is finite? -/
@[to_additive /-- If a measure `μ` on the quotient `G ⧸ Γ` of an additive group `G` by a discrete
normal subgroup `Γ` having fundamental domain, satisfies `AddQuotientMeasureEqMeasurePreimage`
relative to a standardized choice of Haar measure on `G`, and assuming `μ` is finite, then `μ` is
itself Haar. -/]
/-
**MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient** 是 Mathli
b 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient [Local
lyCompactSpace G] [QuotientMeasureEqMeasurePreimage ν μ] [i : HasFundamentalDoma
in Γ.op G ν] [IsFiniteMeasure μ] : IsHaarMeasure μ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `QuotientGroup.continuous_mk`：continuous_mk {N : Subgroup G} : Continuous
 (mk : G -> G ⧸ N)
· 使用定理 `QuotientGroup.isOpenMap_coe`：isOpenMap_coe : IsOpenMap ((↑) : G -> G ⧸ N
)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用引理 `MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quoti
ent`：MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient
 [hasFun : HasFundamentalDomain Γ.op G ν] [QuotientMeasureEqMeasu…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.haarMeasure_unique`：haarMeasure_unique (μ : Measur
e G) [SigmaFinite μ] [IsMulLeftInvariant μ] (K₀ : PositiveCompacts G) : μ = μ K₀
 • haarMeasure K₀
· 使用定理 `MeasureTheory.sigmaFinite_of_locallyFinite`：∀ {α : Type u_1} {m0 : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace α]   [Secon
dCountableTopology α] [MeasureTh…
· 使用定理 `MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure`：∀ {α : Type u_1}
 {m0 : MeasurableSpace α} [inst : TopologicalSpace α] (μ : MeasureTheory.Measure
 α)   [MeasureTheory.IsFiniteMeasure μ], Mea…
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `MeasureTheory.QuotientMeasureEqMeasurePreimage.covolume_ne_top`：∀ {G : T
ype u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : Meas
urableSpace α]   {ν : MeasureTheory.Measure α} [Meas…
· 使用定理 `MeasureTheory.Subgroup.smulInvariantMeasure`：∀ {G : Type u_3} {α : Type 
u_4} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpace α]   {μ
 : MeasureTheory.Measure α} [Meas…
· 使用定理 `MeasureTheory.Measure.IsMulRightInvariant.toSMulInvariantMeasure_op`：∀ {
G : Type u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 :
 Mul G] [μ.IsMulRightInvariant],   MeasureTheory.SMulInva…
· 使用定理 `Subgroup.instCountableSubtypeMulOppositeMemOp`：∀ {G : Type u_2} [inst : 
Group G] (H : Subgroup G) [Countable ↥H], Countable ↥H.op
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `MeasureTheory.IsFundamentalDomain.projection_respects_measure_apply`：∀ {
G : Type u_1} {α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 :
 MeasurableSpace α]   {ν : MeasureTheory.Measure α} (μ : …
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.smul`：∀ {G : Type u_1} [inst : Measu
rableSpace G] [inst_1 : Group G] [inst_2 : TopologicalSpace G]   (μ : MeasureThe
ory.Measure G) [μ.IsHaarMeasur…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `MeasureTheory.Measure.IsOpenPosMeasure.open_pos`：∀ {X : Type u_1} {inst 
: TopologicalSpace X} {m : MeasurableSpace X} {μ : MeasureTheory.Measure X}   [s
elf : μ.IsOpenPosMeasure] (U : Set X)…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `TopologicalSpace.PositiveCompacts.interior_nonempty`：interior_nonempty (
s : PositiveCompacts α) : (interior (s : Set α)).Nonempty
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
（共 43 条，此处仅展示前 30 条）
-/
theorem MeasureTheory.QuotientMeasureEqMeasurePreimage.haarMeasure_quotient [LocallyCompactSpace G]
    [QuotientMeasureEqMeasurePreimage ν μ] [i : HasFundamentalDomain Γ.op G ν]
    [IsFiniteMeasure μ] : IsHaarMeasure μ := by
  obtain ⟨K⟩ := PositiveCompacts.nonempty' (α := G)
  let K' : PositiveCompacts (G ⧸ Γ) :=
    K.map π QuotientGroup.continuous_mk QuotientGroup.isOpenMap_coe
  have : IsMulLeftInvariant μ :=
    MeasureTheory.QuotientMeasureEqMeasurePreimage.mulInvariantMeasure_quotient ν
  rw [haarMeasure_unique μ K']
  have finiteCovol : covolume Γ.op G ν ≠ ⊤ :=
    ne_top_of_lt <| QuotientMeasureEqMeasurePreimage.covolume_ne_top μ (ν := ν)
  obtain ⟨s, fund_dom_s⟩ := i
  rw [fund_dom_s.covolume_eq_volume] at finiteCovol
  rw [fund_dom_s.projection_respects_measure_apply μ K'.isCompact.measurableSet]
  apply IsHaarMeasure.smul
  · intro h
    have i' : IsOpenPosMeasure (ν : Measure G) := inferInstance
    apply IsOpenPosMeasure.open_pos (interior K) (μ := ν) (self := i')
    · exact isOpen_interior
    · exact K.interior_nonempty
    refine measure_mono_null (interior_subset.trans ?_) <|
      fund_dom_s.measure_zero_of_invariant _ (fun g ↦ QuotientGroup.sound _ _ g) h
    rw [QuotientGroup.coe_mk']
    change (K : Set G) ⊆ π ⁻¹' π '' K
    exact subset_preimage_image π K
  · change ν (π ⁻¹' (π '' K) ∩ s) ≠ ⊤
    apply ne_of_lt
    refine lt_of_le_of_lt ?_ finiteCovol.lt_top
    apply measure_mono
    exact inter_subset_right

variable [SigmaFinite ν]

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `QuotientMeasureEqMeasurePreimage`. -/
@[to_additive /-- Given a normal
subgroup `Γ` of an additive topological group `G` with Haar measure `μ`, which is also
right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
properly normalized, satisfies `AddQuotientMeasureEqMeasurePreimage`. -/]
/-
**IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_HaarMeasure** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_HaarMeasure {𝓕 : Set 
G} (h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν) [IsMulLeftInvariant μ] [SigmaFinite μ] {V
 : Set (G ⧸ Γ)} (hV : (interior V).Nonempty) (meas_V : MeasurableSet V) (hμK : μ
 V = ν ((π ⁻¹' V) inter 𝓕)) (neTopV : μ V != ⊤) : QuotientMeasureEqMeasurePreima
ge ν μ
参数：h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν；G ⧸ Γ；hV : (interior V).Nonempty；meas_V : M
easurableSet V；hμK : μ V = ν ((π ⁻¹' V) inter 𝓕)；neTopV : μ V != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.IsMulLeftInvariant.quotientMeasureEqMeasurePreimag
e_of_set`：MeasureTheory.Measure.IsMulLeftInvariant.quotientMeasureEqMeasurePreim
age_of_set {s : Set G} (fund_dom_s : IsFundamentalDomain Γ.op s ν) {V …
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsMulLeftInvariant`：∀ {G : Type u_
3} {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}  
 {μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.IsOpenPosMeasure.open_pos`：∀ {X : Type u_1} {inst 
: TopologicalSpace X} {m : MeasurableSpace X} {μ : MeasureTheory.Measure X}   [s
elf : μ.IsOpenPosMeasure] (U : Set X)…
· 使用定理 `MeasureTheory.Measure.IsHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u_3}
 {inst : Group G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace G}   {
μ : MeasureTheory.Measure G} [self : μ.IsHaa…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `preimage_interior_subset_interior_preimage`：preimage_interior_subset_int
erior_preimage {t : Set Y} (hf : Continuous f) : f ⁻¹' interior t subseteq inter
ior (f ⁻¹' t)
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
· 使用定理 `Set.Nonempty.preimage'`：∀ {α : Type u_1} {β : Type u_2} {s : Set β}, s.N
onempty → ∀ {f : α → β}, s ⊆ Set.range f → (f ⁻¹' s).Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `QuotientGroup.range_mk`：range_mk : range (QuotientGroup.mk (s
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `MeasureTheory.IsFundamentalDomain.measure_zero_of_invariant`：measure_zer
o_of_invariant (h : IsFundamentalDomain G s μ) (t : Set α) (ht : forall g : G, g
 • t = t) (hts : μ (t inter s) = 0) : μ t = 0
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Subgroup.smulInvariantMeasure`：∀ {G : Type u_3} {α : Type 
u_4} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpace α]   {μ
 : MeasureTheory.Measure α} [Meas…
· 使用定理 `MeasureTheory.Measure.IsMulRightInvariant.toSMulInvariantMeasure_op`：∀ {
G : Type u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 :
 Mul G] [μ.IsMulRightInvariant],   MeasureTheory.SMulInva…
· 使用定理 `Subgroup.instCountableSubtypeMulOppositeMemOp`：∀ {G : Type u_2} [inst : 
Group G] (H : Subgroup G) [Countable ↥H], Countable ↥H.op
· 使用定理 `QuotientGroup.sound`：sound (U : Set (G ⧸ N)) (g : N.op) : g • (mk' N) ⁻¹
' U = (mk' N) ⁻¹' U
-/
theorem IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_HaarMeasure {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν) [IsMulLeftInvariant μ] [SigmaFinite μ]
    {V : Set (G ⧸ Γ)} (hV : (interior V).Nonempty) (meas_V : MeasurableSet V)
    (hμK : μ V = ν ((π ⁻¹' V) ∩ 𝓕)) (neTopV : μ V ≠ ⊤) :
    QuotientMeasureEqMeasurePreimage ν μ := by
  apply IsMulLeftInvariant.quotientMeasureEqMeasurePreimage_of_set (fund_dom_s := h𝓕)
    (meas_V := meas_V)
  · rw [hμK]
    intro c_eq_zero
    apply IsOpenPosMeasure.open_pos (interior (π ⁻¹' V)) (μ := ν)
    · simp
    · apply Set.Nonempty.mono (preimage_interior_subset_interior_preimage continuous_coinduced_rng)
      apply hV.preimage'
      simp
    · apply measure_mono_null (h := interior_subset)
      apply h𝓕.measure_zero_of_invariant (ht := fun g ↦ QuotientGroup.sound _ _ g)
      exact c_eq_zero
  · exact hμK
  · exact neTopV

variable (K : PositiveCompacts (G ⧸ Γ))

/-- Given a normal subgroup `Γ` of a topological group `G` with Haar measure `μ`, which is also
  right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
  properly normalized, satisfies `QuotientMeasureEqMeasurePreimage`. -/
@[to_additive /-- Given a
normal subgroup `Γ` of an additive topological group `G` with Haar measure `μ`, which is also
right-invariant, and a finite volume fundamental domain `𝓕`, the quotient map to `G ⧸ Γ`,
properly normalized, satisfies `AddQuotientMeasureEqMeasurePreimage`. -/]
/-
**IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_smulHaarMeasure** 是 Mathl
ib 中的一个定理，位于命名空间 ``。
形式化陈述：IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_smulHaarMeasure {𝓕 : 
Set G} (h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν) (h𝓕_finite : ν 𝓕 != ⊤) : QuotientMeas
ureEqMeasurePreimage ν ((ν ((π ⁻¹' (K : Set (G ⧸ Γ))) inter 𝓕)) • haarMeasure K)
参数：h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν；h𝓕_finite : ν 𝓕 != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_inter_ne_top_of_right_ne_top`：measure_inter_ne_top
_of_right_ne_top (ht_finite : μ t != ∞) : μ (s inter t) != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.haarMeasure_self`：haarMeasure_self {K₀ : PositiveC
ompacts G} : haarMeasure K₀ K₀ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `MeasureTheory.SMul.sigmaFinite`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ] (c : NNReal),   Me
asureTheory.SigmaFin…
· 使用定理 `IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_HaarMeasure`：IsFund
amentalDomain.QuotientMeasureEqMeasurePreimage_HaarMeasure {𝓕 : Set G} (h𝓕 : IsF
undamentalDomain Γ.op 𝓕 ν) [IsMulLeftInvariant μ] [Sig…
· 使用定理 `IsCompact.measurableSet`：IsCompact.measurableSet [T2Space α] (h : IsComp
act s) : MeasurableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `TopologicalSpace.PositiveCompacts.isCompact`：∀ {α : Type u_1} [inst : To
pologicalSpace α] (s : TopologicalSpace.PositiveCompacts α), IsCompact ↑s
· 使用定理 `TopologicalSpace.PositiveCompacts.interior_nonempty`：interior_nonempty (
s : PositiveCompacts α) : (interior (s : Set α)).Nonempty
-/
theorem IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_smulHaarMeasure {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ.op 𝓕 ν) (h𝓕_finite : ν 𝓕 ≠ ⊤) :
    QuotientMeasureEqMeasurePreimage ν
      ((ν ((π ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)) • haarMeasure K) := by
  set c := ν ((π ⁻¹' (K : Set (G ⧸ Γ))) ∩ 𝓕)
  have c_ne_top : c ≠ ∞ := measure_inter_ne_top_of_right_ne_top h𝓕_finite
  set μ := c • haarMeasure K
  have hμK : μ K = c := by simp [μ, haarMeasure_self]
  have : SigmaFinite μ := by
    clear_value c
    lift c to NNReal using c_ne_top
    exact SMul.sigmaFinite c
  apply IsFundamentalDomain.QuotientMeasureEqMeasurePreimage_HaarMeasure (h𝓕 := h𝓕)
    (meas_V := K.isCompact.measurableSet) (μ := μ)
  · exact K.interior_nonempty
  · exact hμK
  · rw [hμK]
    exact c_ne_top

end haarMeasure

end normal

section UnfoldingTrick

variable {G : Type*} [Group G] [MeasurableSpace G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BorelSpace G] {μ : Measure G} {Γ : Subgroup G}

variable {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ.op 𝓕 μ)
include h𝓕

variable [Countable Γ] [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]

local notation "μ_𝓕" => Measure.map (@QuotientGroup.mk G _ Γ) (μ.restrict 𝓕)

/-- The `essSup` of a function `g` on the quotient space `G ⧸ Γ` with respect to the pushforward
  of the restriction, `μ_𝓕`, of a right-invariant measure `μ` to a fundamental domain `𝓕`, is the
  same as the `essSup` of `g`'s lift to the universal cover `G` with respect to `μ`. -/
@[to_additive /-- The `essSup` of a function `g` on the additive quotient space `G ⧸ Γ` with respect
  to the pushforward of the restriction, `μ_𝓕`, of a right-invariant measure `μ` to a fundamental
  domain `𝓕`, is the same as the `essSup` of `g`'s lift to the universal cover `G` with respect
  to `μ`. -/]
/-
**essSup_comp_quotientGroup_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：essSup_comp_quotientGroup_mk [μ.IsMulRightInvariant] {g : G ⧸ Γ -> Real>=0
∞} (g_ae_measurable : AEMeasurable g μ_𝓕) : essSup g μ_𝓕 = essSup (fun (x : G) =
> g x) μ
参数：g_ae_measurable : AEMeasurable g μ_𝓕。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `essSup_map_measure`：essSup_map_measure (hg : AEMeasurable g (Measure.map
 f μ)) (hf : AEMeasurable f μ) (hg_co : IsCoboundedUnder (· <= ·) (ae (Measure.m
ap f μ))…
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `MeasureTheory.IsFundamentalDomain.essSup_measure_restrict`：essSup_measur
e_restrict (hs : IsFundamentalDomain G s μ) {f : α -> Real>=0∞} (hf : forall γ :
 G, forall x : α, f (γ • x) = f x) : essSup f (…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Subgroup.smulInvariantMeasure`：∀ {G : Type u_3} {α : Type 
u_4} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpace α]   {μ
 : MeasureTheory.Measure α} [Meas…
· 使用定理 `MeasureTheory.Measure.IsMulRightInvariant.toSMulInvariantMeasure_op`：∀ {
G : Type u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 :
 Mul G] [μ.IsMulRightInvariant],   MeasureTheory.SMulInva…
· 使用定理 `Subgroup.instCountableSubtypeMulOppositeMemOp`：∀ {G : Type u_2} [inst : 
Group G] (H : Subgroup G) [Countable ↥H], Countable ↥H.op
· 使用定理 `QuotientGroup.mk_mul_of_mem`：mk_mul_of_mem (a : α) (hb : b in s) : (mk (
a * b) : α ⧸ s) = mk a
-/
lemma essSup_comp_quotientGroup_mk [μ.IsMulRightInvariant] {g : G ⧸ Γ → ℝ≥0∞}
    (g_ae_measurable : AEMeasurable g μ_𝓕) : essSup g μ_𝓕 = essSup (fun (x : G) ↦ g x) μ := by
  have hπ : Measurable (QuotientGroup.mk : G → G ⧸ Γ) := continuous_quotient_mk'.measurable
  rw [essSup_map_measure g_ae_measurable hπ.aemeasurable]
  refine h𝓕.essSup_measure_restrict ?_
  intro ⟨γ, hγ⟩ x
  dsimp
  congr 1
  exact QuotientGroup.mk_mul_of_mem x hγ

/-- Given a quotient space `G ⧸ Γ` where `Γ` is `Countable`, and the restriction,
  `μ_𝓕`, of a right-invariant measure `μ` on `G` to a fundamental domain `𝓕`, a set
  in the quotient which has `μ_𝓕`-measure zero, also has measure zero under the
  folding of `μ` under the quotient. Note that, if `Γ` is infinite, then the folded map
  will take the value `∞` on any open set in the quotient! -/
@[to_additive /-- Given an additive quotient space `G ⧸ Γ` where `Γ` is `Countable`, and the
  restriction, `μ_𝓕`, of a right-invariant measure `μ` on `G` to a fundamental domain `𝓕`, a set
  in the quotient which has `μ_𝓕`-measure zero, also has measure zero under the
  folding of `μ` under the quotient. Note that, if `Γ` is infinite, then the folded map
  will take the value `∞` on any open set in the quotient! -/]
/-
**_root_.MeasureTheory.IsFundamentalDomain.absolutelyContinuous_map** 是 Mathlib 
中的一个引理，位于命名空间 ``。
形式化陈述：_root_.MeasureTheory.IsFundamentalDomain.absolutelyContinuous_map [μ.IsMul
RightInvariant] : map (QuotientGroup.mk : G -> G ⧸ Γ) μ ≪ map (QuotientGroup.mk 
: G -> G ⧸ Γ) (μ.restrict 𝓕)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.MeasureTheory.IsFundamentalDomain.absolutelyContinuous_map
    [μ.IsMulRightInvariant] :
    map (QuotientGroup.mk : G → G ⧸ Γ) μ ≪ map (QuotientGroup.mk : G → G ⧸ Γ) (μ.restrict 𝓕) := by
  set π : G → G ⧸ Γ := QuotientGroup.mk
  have meas_π : Measurable π := continuous_quotient_mk'.measurable
  apply AbsolutelyContinuous.mk
  intro s s_meas hs
  rw [map_apply meas_π s_meas] at hs ⊢
  rw [Measure.restrict_apply] at hs
  · apply h𝓕.measure_zero_of_invariant _ _ hs
    intro γ
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, mem_preimage, mem_preimage]
    congr! 1
    convert! QuotientGroup.mk_mul_of_mem g (γ⁻¹).2 using 1
  exact MeasurableSet.preimage s_meas meas_π

attribute [-instance] Quotient.instMeasurableSpace

/-- This is a simple version of the **Unfolding Trick**: Given a subgroup `Γ` of a group `G`, the
  integral of a function `f` on `G` with respect to a right-invariant measure `μ` is equal to the
  integral over the quotient `G ⧸ Γ` of the automorphization of `f`. -/
@[to_additive /-- This is a simple version of the **Unfolding Trick**: Given a subgroup `Γ` of an
  additive group `G`, the integral of a function `f` on `G` with respect to a right-invariant
  measure `μ` is equal to the integral over the quotient `G ⧸ Γ` of the automorphization of `f`. -/]
/-
**QuotientGroup.integral_eq_integral_automorphize** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuotientGroup.integral_eq_integral_automorphize {E : Type*} [NormedAddComm
Group E] [NormedSpace Real E] [μ.IsMulRightInvariant] {f : G -> E} (hf₁ : Integr
able f μ) (hf₂ : AEStronglyMeasurable (automorphize f) μ_𝓕) : ∫ x : G, f x ∂μ = 
∫ x : G ⧸ Γ, automorphize f x ∂μ_𝓕
参数：hf₁ : Integrable f μ；hf₂ : AEStronglyMeasurable (automorphize f) μ_𝓕。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.IsFundamentalDomain.integral_eq_tsum''`：∀ {G : Type u_1} {
α : Type u_3} {E : Type u_5} [inst : Group G] [inst_1 : MulAction G α] [inst_2 :
 MeasurableSpace α]   [inst_3 : NormedAddC…
· 使用定理 `MeasurableSMul.toMeasurableConstSMul`：∀ {M : Type u_2} {α : Type u_3} {i
nst : SMul M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableSMul M α], M…
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.Subgroup.smulInvariantMeasure`：∀ {G : Type u_3} {α : Type 
u_4} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpace α]   {μ
 : MeasureTheory.Measure α} [Meas…
· 使用定理 `MeasureTheory.Measure.IsMulRightInvariant.toSMulInvariantMeasure_op`：∀ {
G : Type u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 :
 Mul G] [μ.IsMulRightInvariant],   MeasureTheory.SMulInva…
· 使用定理 `Subgroup.instCountableSubtypeMulOppositeMemOp`：∀ {G : Type u_2} [inst : 
Group G] (H : Subgroup G) [Countable ↥H], Countable ↥H.op
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_tsum`：integral_tsum {ι} [Countable ι] {f : ι -> α
 -> G} (hf : forall i, AEStronglyMeasurable (f i) μ) (hf' : ∑' i, ∫⁻ a : α, ‖f i
 a‖ₑ ∂μ != ∞) : ∫…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.restrict`：∀ {α : Type u_1} {β : Type 
u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   {f : α → β},   Measur…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving`：comp_qua
siMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} 
{f : γ -> α} {μ : Measure γ} {ν : Measure α} (hg : A…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
· 使用定理 `MeasureTheory.measurePreserving_smul`：measurePreserving_smul : MeasurePr
eserving (c • ·) μ μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IsFundamentalDomain.lintegral_eq_tsum''`：∀ {G : Type u_1} 
{α : Type u_3} [inst : Group G] [inst_1 : MulAction G α] [inst_2 : MeasurableSpa
ce α] {s : Set α}   {μ : MeasureTheory.Meas…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `Continuous.aemeasurable`：Continuous.aemeasurable {f : α -> γ} (h : Conti
nuous f) {μ : Measure α} : AEMeasurable f μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
-/
lemma QuotientGroup.integral_eq_integral_automorphize {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [μ.IsMulRightInvariant] {f : G → E}
    (hf₁ : Integrable f μ) (hf₂ : AEStronglyMeasurable (automorphize f) μ_𝓕) :
    ∫ x : G, f x ∂μ = ∫ x : G ⧸ Γ, automorphize f x ∂μ_𝓕 := by
  calc ∫ x : G, f x ∂μ = ∑' γ : Γ.op, ∫ x in 𝓕, f (γ • x) ∂μ :=
    h𝓕.integral_eq_tsum'' f hf₁
    _ = ∫ x in 𝓕, ∑' γ : Γ.op, f (γ • x) ∂μ := ?_
    _ = ∫ x : G ⧸ Γ, automorphize f x ∂μ_𝓕 :=
      (integral_map continuous_quotient_mk'.aemeasurable hf₂).symm
  rw [integral_tsum]
  · exact fun i ↦ (hf₁.1.comp_quasiMeasurePreserving
      (measurePreserving_smul i μ).quasiMeasurePreserving).restrict
  · rw [← h𝓕.lintegral_eq_tsum'' (‖f ·‖ₑ)]
    exact ne_of_lt hf₁.2

-- we can't use `to_additive`, because it tries to translate `*` into `+`
/-- This is the **Unfolding Trick**: Given a subgroup `Γ` of a group `G`, the integral of a
  function `f` on `G` times the lift to `G` of a function `g` on the quotient `G ⧸ Γ` with respect
  to a right-invariant measure `μ` on `G`, is equal to the integral over the quotient of the
  automorphization of `f` times `g`. -/
/-
**QuotientGroup.integral_mul_eq_integral_automorphize_mul** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：QuotientGroup.integral_mul_eq_integral_automorphize_mul {K : Type*} [Norme
dField K] [NormedSpace Real K] [μ.IsMulRightInvariant] {f : G -> K} (f_ℒ_1 : Int
egrable f μ) {g : G ⧸ Γ -> K} (hg : AEStronglyMeasurable g μ_𝓕) (g_ℒ_infinity : 
essSup (fun x => ↑‖g x‖ₑ) μ_𝓕 != ∞) (F_ae_measurable : AEStronglyMeasurable (Quo
tientGroup.automorphize f) μ_𝓕) : ∫ x : G, g (x : G ⧸ Γ) * (f x) ∂μ = ∫ x : G ⧸ 
Γ, g x * (QuotientGroup.automorphize f x) ∂μ_𝓕
参数：f_ℒ_1 : Integrable f μ；hg : AEStronglyMeasurable g μ_𝓕；g_ℒ_infinity : essSup 
(fun x => ↑‖g x‖ₑ) μ_𝓕 != ∞；F_ae_measurable : AEStronglyMeasurable (QuotientGrou
p.automorphize f) μ_𝓕。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
· 使用引理 `QuotientGroup.automorphize_smul_left`：QuotientGroup.automorphize_smul_le
ft (f : G -> M) (g : G ⧸ Γ -> R) : (QuotientGroup.automorphize ((g ∘ (@Quotient.
mk' _ (_)) : G -> R) • f) …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_measurable`：comp_measurable {γ :
 Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measur
e γ} (hg : AEStronglyMeasurable g (Measu…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.IsFundamentalDomain.absolutelyContinuous_map`：∀ {G : Type 
u_1} [inst : Group G] [inst_1 : MeasurableSpace G] [inst_2 : TopologicalSpace G]
 [IsTopologicalGroup G]   [BorelSpace G] {μ : Me…
· 使用定理 `MeasureTheory.Integrable.essSup_smul`：∀ {α : Type u_1} {β : Type u_2} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β
]   {R : Type u_8} [inst_1…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `essSup_comp_quotientGroup_mk`：essSup_comp_quotientGroup_mk [μ.IsMulRight
Invariant] {g : G ⧸ Γ -> Real>=0∞} (g_ae_measurable : AEMeasurable g μ_𝓕) : essS
up g μ_𝓕 = essSup …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用引理 `QuotientGroup.integral_eq_integral_automorphize`：QuotientGroup.integral_
eq_integral_automorphize {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
 [μ.IsMulRightInvariant] {f : G -> E}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
This is the **Unfolding Trick**: Given a subgroup `Γ` of a group `G`, the integr
al of a
  function `f` on `G` times the lift to `G` of a function `g` on the quotient `G
 ⧸ Γ` with respect
  to a right-invariant measure `μ` on `G`, is equal to the integral over the quo
tient of the
  automorphization of `f` times `g`.
-/
lemma QuotientGroup.integral_mul_eq_integral_automorphize_mul {K : Type*} [NormedField K]
    [NormedSpace ℝ K] [μ.IsMulRightInvariant] {f : G → K}
    (f_ℒ_1 : Integrable f μ) {g : G ⧸ Γ → K} (hg : AEStronglyMeasurable g μ_𝓕)
    (g_ℒ_infinity : essSup (fun x ↦ ↑‖g x‖ₑ) μ_𝓕 ≠ ∞)
    (F_ae_measurable : AEStronglyMeasurable (QuotientGroup.automorphize f) μ_𝓕) :
    ∫ x : G, g (x : G ⧸ Γ) * (f x) ∂μ
      = ∫ x : G ⧸ Γ, g x * (QuotientGroup.automorphize f x) ∂μ_𝓕 := by
  let π : G → G ⧸ Γ := QuotientGroup.mk
  have meas_π : Measurable π := continuous_quotient_mk'.measurable
  have H₀ : QuotientGroup.automorphize ((g ∘ π) * f) = g * (QuotientGroup.automorphize f) := by
    exact QuotientGroup.automorphize_smul_left f g
  calc ∫ (x : G), g (π x) * (f x) ∂μ =
        ∫ (x : G ⧸ Γ), QuotientGroup.automorphize ((g ∘ π) * f) x ∂μ_𝓕 := ?_
    _ = ∫ (x : G ⧸ Γ), g x * (QuotientGroup.automorphize f x) ∂μ_𝓕 := by simp [H₀]
  have H₁ : Integrable ((g ∘ π) * f) μ := by
    have : AEStronglyMeasurable (fun (x : G) ↦ g (x : (G ⧸ Γ))) μ :=
      (hg.mono_ac h𝓕.absolutelyContinuous_map).comp_measurable meas_π
    refine Integrable.essSup_smul f_ℒ_1 this ?_
    have hg' : AEStronglyMeasurable (‖g ·‖ₑ) μ_𝓕 := continuous_enorm.comp_aestronglyMeasurable hg
    rw [← essSup_comp_quotientGroup_mk h𝓕 hg'.aemeasurable]
    exact g_ℒ_infinity
  have H₂ : AEStronglyMeasurable (QuotientGroup.automorphize ((g ∘ π) * f)) μ_𝓕 := by
    simp_rw [H₀]
    exact hg.mul F_ae_measurable
  apply QuotientGroup.integral_eq_integral_automorphize h𝓕 H₁ H₂

end UnfoldingTrick

section

variable {G' : Type*} [AddGroup G'] [MeasurableSpace G'] [TopologicalSpace G']
  [IsTopologicalAddGroup G'] [BorelSpace G'] {μ' : Measure G'} {Γ' : AddSubgroup G'}
  {𝓕' : Set G'} (h𝓕 : IsAddFundamentalDomain Γ'.op 𝓕' μ')
  [Countable Γ'] [MeasurableSpace (G' ⧸ Γ')] [BorelSpace (G' ⧸ Γ')]
include h𝓕

local notation "μ_𝓕" => Measure.map (@QuotientAddGroup.mk G' _ Γ') (μ'.restrict 𝓕')

/-- This is the **Unfolding Trick**: Given an additive subgroup `Γ'` of an additive group `G'`, the
  integral of a function `f` on `G'` times the lift to `G'` of a function `g` on the quotient
  `G' ⧸ Γ'` with respect to a right-invariant measure `μ` on `G'`, is equal to the integral over
  the quotient of the automorphization of `f` times `g`. -/
/-
**QuotientAddGroup.integral_mul_eq_integral_automorphize_mul** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：QuotientAddGroup.integral_mul_eq_integral_automorphize_mul {K : Type*} [No
rmedField K] [NormedSpace Real K] [μ'.IsAddRightInvariant] {f : G' -> K} (f_ℒ_1 
: Integrable f μ') {g : G' ⧸ Γ' -> K} (hg : AEStronglyMeasurable g μ_𝓕) (g_ℒ_inf
inity : essSup (‖g ·‖ₑ) μ_𝓕 != ∞) (F_ae_measurable : AEStronglyMeasurable (Quoti
entAddGroup.automorphize f) μ_𝓕) : ∫ x : G', g (x : G' ⧸ Γ') * (f x) ∂μ' = ∫ x :
 G' ⧸ Γ', g x * (QuotientAddGroup.automorphize f x) ∂μ_𝓕
参数：f_ℒ_1 : Integrable f μ'；hg : AEStronglyMeasurable g μ_𝓕；g_ℒ_infinity : essSup
 (‖g ·‖ₑ) μ_𝓕 != ∞；F_ae_measurable : AEStronglyMeasurable (QuotientAddGroup.auto
morphize f) μ_𝓕。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `continuous_quotient_mk'`：continuous_quotient_mk' : Continuous (@Quotient
.mk' X s)
· 使用引理 `QuotientAddGroup.automorphize_smul_left`：QuotientAddGroup.automorphize_s
mul_left (f : G -> M) (g : G ⧸ Γ -> R) : QuotientAddGroup.automorphize ((g ∘ (@Q
uotient.mk' _ (_))) • f) = g …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_measurable`：comp_measurable {γ :
 Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ -> α} {μ : Measur
e γ} (hg : AEStronglyMeasurable g (Measu…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_ac`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ ν : MeasureTheory.
Measure α}   {f : α → β},   ν.Ab…
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.absolutelyContinuous_map`：∀ {G : Ty
pe u_1} [inst : AddGroup G] [inst_1 : MeasurableSpace G] [inst_2 : TopologicalSp
ace G]   [IsTopologicalAddGroup G] [BorelSpace G] {…
· 使用定理 `MeasureTheory.Integrable.essSup_smul`：∀ {α : Type u_1} {β : Type u_2} {m
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β
]   {R : Type u_8} [inst_1…
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `essSup_comp_quotientAddGroup_mk`：∀ {G : Type u_1} [inst : AddGroup G] [i
nst_1 : MeasurableSpace G] [inst_2 : TopologicalSpace G]   [IsTopologicalAddGrou
p G] [BorelSpace G] {…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `QuotientAddGroup.integral_eq_integral_automorphize`：∀ {G : Type u_1} [in
st : AddGroup G] [inst_1 : MeasurableSpace G] [inst_2 : TopologicalSpace G]   [I
sTopologicalAddGroup G] [BorelSpace G] {…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
This is the **Unfolding Trick**: Given an additive subgroup `Γ'` of an additive 
group `G'`, the
  integral of a function `f` on `G'` times the lift to `G'` of a function `g` on
 the quotient
  `G' ⧸ Γ'` with respect to a right-invariant measure `μ` on `G'`, is equal to t
he integral over
  the quotient of the automorphization of `f` times `g`.
-/
lemma QuotientAddGroup.integral_mul_eq_integral_automorphize_mul {K : Type*} [NormedField K]
    [NormedSpace ℝ K] [μ'.IsAddRightInvariant] {f : G' → K}
    (f_ℒ_1 : Integrable f μ') {g : G' ⧸ Γ' → K} (hg : AEStronglyMeasurable g μ_𝓕)
    (g_ℒ_infinity : essSup (‖g ·‖ₑ) μ_𝓕 ≠ ∞)
    (F_ae_measurable : AEStronglyMeasurable (QuotientAddGroup.automorphize f) μ_𝓕) :
    ∫ x : G', g (x : G' ⧸ Γ') * (f x) ∂μ'
      = ∫ x : G' ⧸ Γ', g x * (QuotientAddGroup.automorphize f x) ∂μ_𝓕 := by
  let π : G' → G' ⧸ Γ' := QuotientAddGroup.mk
  have meas_π : Measurable π := continuous_quotient_mk'.measurable
  have H₀ : QuotientAddGroup.automorphize ((g ∘ π) * f) = g * (QuotientAddGroup.automorphize f) :=
    QuotientAddGroup.automorphize_smul_left f g
  calc ∫ (x : G'), g (π x) * f x ∂μ' =
    ∫ (x : G' ⧸ Γ'), QuotientAddGroup.automorphize ((g ∘ π) * f) x ∂μ_𝓕 := ?_
    _ = ∫ (x : G' ⧸ Γ'), g x * (QuotientAddGroup.automorphize f x) ∂μ_𝓕 := by simp [H₀]
  have H₁ : Integrable ((g ∘ π) * f) μ' := by
    have : AEStronglyMeasurable (fun (x : G') ↦ g (x : (G' ⧸ Γ'))) μ' :=
      (hg.mono_ac h𝓕.absolutelyContinuous_map).comp_measurable meas_π
    refine Integrable.essSup_smul f_ℒ_1 this ?_
    have hg' : AEStronglyMeasurable (‖g ·‖ₑ) μ_𝓕 := continuous_enorm.comp_aestronglyMeasurable hg
    rw [← essSup_comp_quotientAddGroup_mk h𝓕 hg'.aemeasurable]
    exact g_ℒ_infinity
  have H₂ : AEStronglyMeasurable (QuotientAddGroup.automorphize ((g ∘ π) * f)) μ_𝓕 := by
    simp_rw [H₀]
    exact hg.mul F_ae_measurable
  apply QuotientAddGroup.integral_eq_integral_automorphize h𝓕 H₁ H₂

end

