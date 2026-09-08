/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.ZeroFamily
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-!
# Quasi-compact precoverage

In this file we define the quasi-compact precoverage. A cover is covering in the quasi-compact
precoverage if it is a quasi-compact cover, i.e., if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

The fpqc precoverage is the precoverage by flat covers that are quasi-compact in this sense.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

@[simp]
/-
**AlgebraicGeometry.Scheme.quasiCompactCover_shrink_iff** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：quasiCompactCover_shrink_iff (E : PreZeroHypercover.{w} S) : QuasiCompactC
over E.shrink ↔ QuasiCompactCover E
参数：E : PreZeroHypercover.{w} S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.QuasiCompactCover.of_hom`：of_hom {𝒱 : PreZeroHypercove
r.{w'} S} (f : 𝒱.Hom 𝒰) [QuasiCompactCover 𝒱] : QuasiCompactCover 𝒰
-/
lemma quasiCompactCover_shrink_iff (E : PreZeroHypercover.{w} S) :
    QuasiCompactCover E.shrink ↔ QuasiCompactCover E :=
  ⟨fun _ ↦ .of_hom E.fromShrink, fun _ ↦ .of_hom E.toShrink⟩

/-- The pre-`0`-hypercover family on the category of schemes underlying the fpqc precoverage. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.qcCoverFamily** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：qcCoverFamily : PreZeroHypercoverFamily Scheme.{u} where property X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-`0`-hypercover family on the category of schemes underlying the fpqc pre
coverage.
-/
def qcCoverFamily : PreZeroHypercoverFamily Scheme.{u} where
  property X := X.quasiCompactCover
  iff_shrink {_} E := (quasiCompactCover_shrink_iff E).symm

/--
The quasi-compact precoverage on the category of schemes is the precoverage
given by quasi-compact covers. The intersection of this precoverage
with the precoverage defined by jointly surjective families of flat morphisms is
the fpqc-precoverage.
-/
/-
**AlgebraicGeometry.Scheme.qcPrecoverage** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：qcPrecoverage : Precoverage Scheme.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quasi-compact precoverage on the category of schemes is the precoverage
given by quasi-compact covers. The intersection of this precoverage
with the precoverage defined by jointly surjective families of flat morphisms is
the fpqc-precoverage.
-/
def qcPrecoverage : Precoverage Scheme.{u} :=
  qcCoverFamily.precoverage

@[simp]
/-
**AlgebraicGeometry.Scheme.presieve** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry
.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma presieve₀_mem_qcPrecoverage_iff {E : PreZeroHypercover.{w} S} :
    E.presieve₀ ∈ Scheme.qcPrecoverage S ↔ QuasiCompactCover E := by
  rw [← PreZeroHypercover.presieve₀_shrink, Scheme.qcPrecoverage,
    E.shrink.presieve₀_mem_precoverage_iff]
  simp
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : qcPrecoverage.HasIsos := .of_preZeroHypercoverFamily fun X Y f hf ↦ by
  rw [qcCoverFamily_property, Scheme.quasiCompactCover_iff]
  infer_instance
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : qcPrecoverage.IsStableUnderBaseChange := by
  refine .of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms ?_ ?_
  · intro X
    exact X.isClosedUnderIsomorphisms_quasiCompactCover
  · intro X Y f E h hE
    simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE ⊢
    infer_instance
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : qcPrecoverage.IsStableUnderComposition := by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF ↦ ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : qcPrecoverage.IsStableUnderSup := by
  refine .of_preZeroHypercoverFamily fun {X} E F hE hF ↦ ?_
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance
/-
**AlgebraicGeometry.Scheme.bot_mem_qcPrecoverage** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：bot_mem_qcPrecoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ in qcPrecoverage X
参数：X : Scheme.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.PreZeroHypercover.presieve₀_empty`：presieve₀_empty : (emp
ty.{w} S).presieve₀ = ⊥
· 使用引理 `AlgebraicGeometry.Scheme.presieve₀_mem_qcPrecoverage_iff`：presieve₀_mem_
qcPrecoverage_iff {E : PreZeroHypercover.{w} S} : E.presieve₀ in Scheme.qcPrecov
erage S ↔ QuasiCompactCover E
· 使用定理 `AlgebraicGeometry.QuasiCompactCover.instOfIsEmptyCarrierCarrierCommRingC
at`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : CategoryTheory.PreZeroHypercover S} [I
sEmpty ↥S],   AlgebraicGeometry.QuasiCompactCover 𝒰
-/
lemma bot_mem_qcPrecoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ qcPrecoverage X := by
  rw [← PreZeroHypercover.presieve₀_empty.{0}, presieve₀_mem_qcPrecoverage_iff]
  infer_instance

/-- If `P` implies being an open map, the by `P` induced precoverage is coarser
than the quasi-compact precoverage. -/
/-
**AlgebraicGeometry.Scheme.precoverage_le_qcPrecoverage_of_isOpenMap** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：precoverage_le_qcPrecoverage_of_isOpenMap {P : MorphismProperty Scheme.{u}
} (hP : P <= fun _ _ f => IsOpenMap f.base) : precoverage P <= qcPrecoverage
参数：hP : P <= fun _ _ f => IsOpenMap f.base。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Precoverage.le_of_zeroHypercover`：le_of_zeroHypercover {J
 K : Precoverage C} (h : forall ⦃X : C⦄ ⦃E : ZeroHypercover.{max u v} J X⦄, E.pr
esieve₀ in K X) : J <= K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.presieve₀_mem_qcPrecoverage_iff`：presieve₀_mem_
qcPrecoverage_iff {E : PreZeroHypercover.{w} S} : E.presieve₀ in Scheme.qcPrecov
erage S ↔ QuasiCompactCover E
· 使用引理 `AlgebraicGeometry.QuasiCompactCover.of_isOpenMap`：of_isOpenMap {𝒰 : S.Co
ver K} [Scheme.JointlySurjective K] (h : forall i, IsOpenMap (𝒰.f i)) : QuasiCom
pactCover 𝒰.toPreZeroHypercover where …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.map_prop`：∀ {X : AlgebraicGeometry.Scheme
} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   (𝒰 : Algebrai
cGeometry.Scheme.Cover (Algeb…

--- 原说明 ---
If `P` implies being an open map, the by `P` induced precoverage is coarser
than the quasi-compact precoverage.
-/
lemma precoverage_le_qcPrecoverage_of_isOpenMap {P : MorphismProperty Scheme.{u}}
    (hP : P ≤ fun _ _ f ↦ IsOpenMap f.base) :
    precoverage P ≤ qcPrecoverage := by
  refine Precoverage.le_of_zeroHypercover fun X E ↦ ?_
  rw [presieve₀_mem_qcPrecoverage_iff]
  exact .of_isOpenMap fun i ↦ hP _ (Scheme.Cover.map_prop E i)
/-
**AlgebraicGeometry.Scheme.zariskiPrecoverage_le_qcPrecoverage** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：zariskiPrecoverage_le_qcPrecoverage : zariskiPrecoverage <= qcPrecoverage
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.precoverage_le_qcPrecoverage_of_isOpenMap`：prec
overage_le_qcPrecoverage_of_isOpenMap {P : MorphismProperty Scheme.{u}} (hP : P 
<= fun _ _ f => IsOpenMap f.base) : precoverage P <= qcP…
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
-/
lemma zariskiPrecoverage_le_qcPrecoverage :
    zariskiPrecoverage ≤ qcPrecoverage :=
  precoverage_le_qcPrecoverage_of_isOpenMap fun _ _ f _ ↦ f.isOpenEmbedding.isOpenMap
/-
**AlgebraicGeometry.Scheme.Hom.singleton_mem_qcPrecoverage** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Surjecti
ve f] [AlgebraicGeometry.QuasiCompact f],   CategoryTheory.Presieve.singleton f 
∈ AlgebraicGeometry.Scheme.qcPrecoverage.coverings Y
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.qcPrecoverage.eq_1`：AlgebraicGeometry.Scheme.qc
Precoverage = AlgebraicGeometry.Scheme.qcCoverFamily.precoverage
· 使用定理 `CategoryTheory.PreZeroHypercoverFamily.mem_precoverage_iff`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.PreZeroHypercov
erFamily C} {X : C}   {R : CategoryTheory.Presie…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.qcCoverFamily_property`：∀ (X : AlgebraicGeometr
y.Scheme) (a : CategoryTheory.PreZeroHypercover X),   AlgebraicGeometry.Scheme.q
cCoverFamily.property a = X.quasiComp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Hom.presieve₀_cover`：∀ {P : CategoryTheory.Morp
hismProperty AlgebraicGeometry.Scheme} {X S : AlgebraicGeometry.Scheme} (f : X ⟶
 S) (hf : P f)   [inst : Algebraic…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.singleton_mem_qcPrecoverage {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [QuasiCompact f] : Presieve.singleton f ∈ qcPrecoverage Y := by
  let E : Cover.{u} _ _ := f.cover (P := ⊤) trivial
  rw [qcPrecoverage, PreZeroHypercoverFamily.mem_precoverage_iff]
  refine ⟨(f.cover (P := ⊤) trivial).toPreZeroHypercover, ?_, by simp⟩
  simp only [qcCoverFamily_property, quasiCompactCover_iff]
  infer_instance

section Property

variable {P : MorphismProperty Scheme.{u}}

/-- The `qc`-precoverage of a scheme wrt. to a morphism property `P` is the precoverage
given by quasi-compact covers satisfying `P`. -/
/-
**AlgebraicGeometry.Scheme.propQCPrecoverage** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：propQCPrecoverage (P : MorphismProperty Scheme.{u}) : Precoverage Scheme.{
u}
参数：P : MorphismProperty Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `qc`-precoverage of a scheme wrt. to a morphism property `P` is the precover
age
given by quasi-compact covers satisfying `P`.
-/
abbrev propQCPrecoverage (P : MorphismProperty Scheme.{u}) : Precoverage Scheme.{u} :=
  qcPrecoverage ⊓ Scheme.precoverage P

@[grind .]
/-
**AlgebraicGeometry.Scheme.propQCPrecoverage_le_precoverage** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：propQCPrecoverage_le_precoverage : propQCPrecoverage P <= precoverage P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma propQCPrecoverage_le_precoverage : propQCPrecoverage P ≤ precoverage P :=
  inf_le_right
/-
**AlgebraicGeometry.Scheme.propQCPrecoverage_monotone** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：propQCPrecoverage_monotone : Monotone propQCPrecoverage
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.propQCPrecoverage.eq_1`：∀ (P : CategoryTheory.M
orphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.propQCPrec
overage P =     AlgebraicGeometry.Sch…
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.precoverage_mono`：precoverage_mono {P Q : Morph
ismProperty Scheme.{u}} (h : P <= Q) : precoverage P <= precoverage Q
-/
lemma propQCPrecoverage_monotone : Monotone propQCPrecoverage := by
  intro P Q h
  rw [propQCPrecoverage, propQCPrecoverage]
  gcongr
  exact precoverage_mono h
/-
**AlgebraicGeometry.Scheme.zariskiPrecoverage_le_propQCPrecoverage** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：zariskiPrecoverage_le_propQCPrecoverage [P.ContainsIdentities] [IsZariskiL
ocalAtSource P] : zariskiPrecoverage <= propQCPrecoverage P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.propQCPrecoverage.eq_1`：∀ (P : CategoryTheory.M
orphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.propQCPrec
overage P =     AlgebraicGeometry.Sch…
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用引理 `AlgebraicGeometry.Scheme.zariskiPrecoverage_le_qcPrecoverage`：zariskiPre
coverage_le_qcPrecoverage : zariskiPrecoverage <= qcPrecoverage
· 使用引理 `AlgebraicGeometry.Scheme.precoverage_mono`：precoverage_mono {P Q : Morph
ismProperty Scheme.{u}} (h : P <= Q) : precoverage P <= precoverage Q
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`：of_isOpenIm
mersion [P.ContainsIdentities] [IsOpenImmersion f] : P f
-/
lemma zariskiPrecoverage_le_propQCPrecoverage [P.ContainsIdentities] [IsZariskiLocalAtSource P] :
    zariskiPrecoverage ≤ propQCPrecoverage P := by
  rw [propQCPrecoverage, le_inf_iff]
  refine ⟨zariskiPrecoverage_le_qcPrecoverage, precoverage_mono fun X Y f hf ↦ ?_⟩
  apply IsZariskiLocalAtSource.of_isOpenImmersion
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    QuasiCompactCover 𝒰.toPreZeroHypercover := by
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1
/-
**AlgebraicGeometry.Scheme.bot_mem_propQCPrecoverage** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme`。
形式化陈述：bot_mem_propQCPrecoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ in propQCPrecov
erage P X
参数：X : Scheme.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.bot_mem_qcPrecoverage`：bot_mem_qcPrecoverage (X
 : Scheme.{u}) [IsEmpty X] : ⊥ in qcPrecoverage X
· 使用引理 `AlgebraicGeometry.Scheme.bot_mem_precoverage`：bot_mem_precoverage (X : S
cheme.{u}) [IsEmpty X] : ⊥ in Scheme.precoverage P X
-/
lemma bot_mem_propQCPrecoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ propQCPrecoverage P X :=
  ⟨bot_mem_qcPrecoverage _, bot_mem_precoverage _ _⟩

/-- Forget being quasi-compact. -/
@[simps toPreZeroHypercover]
/-
**AlgebraicGeometry.Scheme.Cover.forgetQc** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   {S : Al
gebraicGeometry.Scheme} →     AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.
Scheme.propQCPrecoverage P) S →       AlgebraicGeometry.Scheme.Cover (AlgebraicG
eometry.Scheme.precoverage P) S
参数：AlgebraicGeometry.Scheme.propQCPrecoverage P；AlgebraicGeometry.Scheme.precove
rage P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forget being quasi-compact.
-/
abbrev Cover.forgetQc {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    S.Cover (precoverage P) where
  __ := 𝒰.toPreZeroHypercover
  mem₀ := 𝒰.mem₀.2
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Scheme.{u}} (𝒰 : Scheme.Cover (propQCPrecoverage P) S) :
    QuasiCompactCover 𝒰.forgetQc.toPreZeroHypercover := by
  dsimp; infer_instance

/-- Construct a cover in the `P`-qc topology from a quasi-compact cover in the `P`-topology. -/
@[simps toPreZeroHypercover]
/-
**AlgebraicGeometry.Scheme.Cover.ofQuasiCompactCover** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   {S : Al
gebraicGeometry.Scheme} →     (𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeom
etry.Scheme.precoverage P) S) →       [qc : AlgebraicGeometry.QuasiCompactCover 
𝒰.toPreZeroHypercover] →         AlgebraicGeometry.Scheme.Cover (AlgebraicGeomet
ry.Scheme.propQCPrecoverage P) S
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) S
；AlgebraicGeometry.Scheme.propQCPrecoverage P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a cover in the `P`-qc topology from a quasi-compact cover in the `P`-t
opology.
-/
def Cover.ofQuasiCompactCover {S : Scheme.{u}} (𝒰 : Scheme.Cover (precoverage P) S)
    [qc : QuasiCompactCover 𝒰.1] :
    Scheme.Cover (propQCPrecoverage P) S where
  __ := 𝒰.toPreZeroHypercover
  mem₀ := ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr ‹_›, 𝒰.mem₀⟩

/-- Lift a quasi-compact `P`-cover of a `u`-scheme in an arbitrary universe to universe `u`.
This is again quasi-compact. -/
/-
**AlgebraicGeometry.Scheme.Cover.qculift** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   {S : Al
gebraicGeometry.Scheme} →     (𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeom
etry.Scheme.precoverage P) S) →       [AlgebraicGeometry.QuasiCompactCover 𝒰.toP
reZeroHypercover] →         AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Sc
heme.precoverage P) S
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) S
；AlgebraicGeometry.Scheme.precoverage P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a quasi-compact `P`-cover of a `u`-scheme in an arbitrary universe to unive
rse `u`.
This is again quasi-compact.
-/
noncomputable def Cover.qculift {S : Scheme.{u}} (𝒰 : Cover.{w} (precoverage P) S)
    [QuasiCompactCover 𝒰.1] : Scheme.Cover.{u} (precoverage P) S where
  __ := 𝒰.ulift.toPreZeroHypercover.sum (QuasiCompactCover.ulift 𝒰.1)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨.inl x, 𝒰.covers _⟩, fun i ↦ ?_⟩
    induction i <;> exact 𝒰.map_prop _
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [QuasiCompactCover 𝒰.1] :
    QuasiCompactCover (Scheme.Cover.qculift 𝒰).1 :=
  .of_hom (PreZeroHypercover.sumInr _ _)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Precoverage.Small.{u} (propQCPrecoverage P) where
  zeroHypercoverSmall {S} (𝒰 : S.Cover _) := by
    refine ⟨𝒰.forgetQc.qculift.I₀, Sum.elim 𝒰.forgetQc.idx (QuasiCompactCover.uliftHom _).s₀,
      ⟨?_, ?_⟩⟩
    · rw [Scheme.presieve₀_mem_qcPrecoverage_iff]
      exact .of_hom (𝒱 := QuasiCompactCover.ulift 𝒰.1) ⟨Sum.inr, fun i ↦ 𝟙 _, by cat_disch⟩
    · rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ ⟨Sum.inl x, 𝒰.forgetQc.covers _⟩, fun i ↦ 𝒰.forgetQc.map_prop _⟩
/-
**AlgebraicGeometry.Scheme.mem_propQCPrecoverage_iff_exists_quasiCompactCover** 
是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：mem_propQCPrecoverage_iff_exists_quasiCompactCover {S : Scheme.{u}} {R : P
resieve S} : R in propQCPrecoverage P S ↔ exists (𝒰 : Scheme.Cover.{u + 1} (prec
overage P) S), QuasiCompactCover 𝒰.toPreZeroHypercover ∧ R = 𝒰.presieve₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover`：mem_iff_exists
_zeroHypercover {X : C} {R : Presieve X} : R in J X ↔ exists (𝒰 : ZeroHypercover
.{max u v} J X), R = Presieve.ofArrows 𝒰.X 𝒰.f
· 使用引理 `AlgebraicGeometry.Scheme.propQCPrecoverage_le_precoverage`：propQCPrecove
rage_le_precoverage : propQCPrecoverage P <= precoverage P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.presieve₀_mem_qcPrecoverage_iff`：presieve₀_mem_
qcPrecoverage_iff {E : PreZeroHypercover.{w} S} : E.presieve₀ in Scheme.qcPrecov
erage S ↔ QuasiCompactCover E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
-/
lemma mem_propQCPrecoverage_iff_exists_quasiCompactCover {S : Scheme.{u}} {R : Presieve S} :
    R ∈ propQCPrecoverage P S ↔ ∃ (𝒰 : Scheme.Cover.{u + 1} (precoverage P) S),
      QuasiCompactCover 𝒰.toPreZeroHypercover ∧ R = 𝒰.presieve₀ := by
  rw [Precoverage.mem_iff_exists_zeroHypercover]
  refine ⟨fun ⟨𝒰, h⟩ ↦ ⟨𝒰.weaken propQCPrecoverage_le_precoverage, ?_, h⟩,
    fun ⟨𝒰, _, h⟩ ↦ ⟨⟨𝒰.1, ⟨by simpa, 𝒰.mem₀⟩⟩, h⟩⟩
  rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
  exact 𝒰.mem₀.1

@[grind .]
/-
**AlgebraicGeometry.Scheme.Hom.singleton_mem_propQCPrecoverage** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {X Y : Al
gebraicGeometry.Scheme} {f : X ⟶ Y},   P f →     ∀ [AlgebraicGeometry.Surjective
 f] [AlgebraicGeometry.QuasiCompact f],       CategoryTheory.Presieve.singleton 
f ∈ (AlgebraicGeometry.Scheme.propQCPrecoverage P).coverings Y
参数：AlgebraicGeometry.Scheme.propQCPrecoverage P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.singleton_mem_qcPrecoverage`：∀ {X Y : Algeb
raicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f] [AlgebraicGeom
etry.QuasiCompact f],   CategoryTheory.Presiev…
-/
lemma Hom.singleton_mem_propQCPrecoverage {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : P f) [Surjective f]
    [QuasiCompact f] : Presieve.singleton f ∈ propQCPrecoverage P Y := by
  refine ⟨f.singleton_mem_qcPrecoverage, ?_⟩
  grind [singleton_mem_precoverage_iff]

/-- The `P`-`qc`-topology on the category of schemes wrt. to a morphism property `P` is the
topology generated by quasi-compact covers satisfying `P`. -/
/-
**AlgebraicGeometry.Scheme.propQCTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：propQCTopology (P : MorphismProperty Scheme.{u}) : GrothendieckTopology Sc
heme.{u}
参数：P : MorphismProperty Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `P`-`qc`-topology on the category of schemes wrt. to a morphism property `P`
 is the
topology generated by quasi-compact covers satisfying `P`.
-/
abbrev propQCTopology (P : MorphismProperty Scheme.{u}) : GrothendieckTopology Scheme.{u} :=
  (propQCPrecoverage P).toGrothendieck
/-
**AlgebraicGeometry.Scheme.bot_mem_propQCTopology** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme`。
形式化陈述：bot_mem_propQCTopology (X : Scheme.{u}) [IsEmpty X] : ⊥ in propQCTopology 
P X
参数：X : Scheme.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sieve.generate_bot`：generate_bot : generate (⊥ : Presieve
 X) = ⊥
· 使用引理 `CategoryTheory.Precoverage.generate_mem_toGrothendieck`：generate_mem_toG
rothendieck {X : C} {R : Presieve X} (hR : R in J X) : Sieve.generate R in J.toG
rothendieck X
· 使用引理 `AlgebraicGeometry.Scheme.bot_mem_propQCPrecoverage`：bot_mem_propQCPrecov
erage (X : Scheme.{u}) [IsEmpty X] : ⊥ in propQCPrecoverage P X
-/
lemma bot_mem_propQCTopology (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ propQCTopology P X := by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_propQCPrecoverage X)

@[grind .]
/-
**AlgebraicGeometry.Scheme.Hom.generate_singleton_mem_propQCTopology** 是 Mathlib
 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {X Y : Al
gebraicGeometry.Scheme} (f : X ⟶ Y),   P f →     ∀ [AlgebraicGeometry.Surjective
 f] [AlgebraicGeometry.QuasiCompact f],       CategoryTheory.Sieve.generate (Cat
egoryTheory.Presieve.singleton f) ∈         (AlgebraicGeometry.Scheme.propQCTopo
logy P) Y
参数：f : X ⟶ Y；CategoryTheory.Presieve.singleton f；AlgebraicGeometry.Scheme.propQC
Topology P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Precoverage.generate_mem_toGrothendieck`：generate_mem_toG
rothendieck {X : C} {R : Presieve X} (hR : R in J X) : Sieve.generate R in J.toG
rothendieck X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.singleton_mem_propQCPrecoverage`：∀ {P : Cat
egoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {X Y : AlgebraicGeometry.
Scheme} {f : X ⟶ Y},   P f →     ∀ [AlgebraicGeome…
-/
lemma Hom.generate_singleton_mem_propQCTopology {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : P f)
    [Surjective f] [QuasiCompact f] :
    .generate (.singleton f) ∈ propQCTopology P Y := by
  apply Precoverage.generate_mem_toGrothendieck
  exact f.singleton_mem_propQCPrecoverage hf

@[simp, grind .]
/-
**AlgebraicGeometry.Scheme.Cover.mem_propQCTopology** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.Cover`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {S : Alge
braicGeometry.Scheme}   (𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.S
cheme.precoverage P) S)   [AlgebraicGeometry.QuasiCompactCover 𝒰.toPreZeroHyperc
over],   CategoryTheory.Sieve.ofArrows 𝒰.X 𝒰.f ∈ (AlgebraicGeometry.Scheme.propQ
CTopology P) S
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) S
；AlgebraicGeometry.Scheme.propQCTopology P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Precoverage.generate_mem_toGrothendieck`：generate_mem_toG
rothendieck {X : C} {R : Presieve X} (hR : R in J X) : Sieve.generate R in J.toG
rothendieck X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.presieve₀_mem_qcPrecoverage_iff`：presieve₀_mem_
qcPrecoverage_iff {E : PreZeroHypercover.{w} S} : E.presieve₀ in Scheme.qcPrecov
erage S ↔ QuasiCompactCover E
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
-/
lemma Cover.mem_propQCTopology {S : Scheme.{u}} (𝒰 : Cover.{u} (precoverage P) S)
    [QuasiCompactCover 𝒰.1] :
    .ofArrows 𝒰.X 𝒰.f ∈ propQCTopology P S := by
  refine Precoverage.generate_mem_toGrothendieck ⟨?_, 𝒰.mem₀⟩
  rwa [presieve₀_mem_qcPrecoverage_iff]
/-
**AlgebraicGeometry.Scheme.zariskiTopology_le_propQCTopology** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：zariskiTopology_le_propQCTopology [P.IsMultiplicative] [IsZariskiLocalAtSo
urce P] : zariskiTopology <= propQCTopology P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.toGrothendieck_mono`：∀ {C : Type u_3} [inst :
 CategoryTheory.Category.{u_2, u_3} C] {J K : CategoryTheory.Precoverage C},   J
 ≤ K → J.toGrothendieck ≤ K.toGrothe…
· 使用引理 `AlgebraicGeometry.Scheme.zariskiPrecoverage_le_propQCPrecoverage`：zarisk
iPrecoverage_le_propQCPrecoverage [P.ContainsIdentities] [IsZariskiLocalAtSource
 P] : zariskiPrecoverage <= propQCPrecoverage P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
-/
lemma zariskiTopology_le_propQCTopology [P.IsMultiplicative] [IsZariskiLocalAtSource P] :
    zariskiTopology ≤ propQCTopology P :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_propQCPrecoverage

end Property

end AlgebraicGeometry.Scheme

