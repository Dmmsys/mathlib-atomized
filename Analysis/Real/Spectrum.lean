/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Some lemmas on the spectrum and quasispectrum of elements and positivity

-/

public section

namespace SpectrumRestricts

open NNReal ENNReal

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-
**SpectrumRestricts.nnreal_iff** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts`。
形式化陈述：nnreal_iff {a : A} : SpectrumRestricts a ContinuousMap.realToNNReal ↔ fora
ll x in spectrum Real a, 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `SpectrumRestricts.of_subset_range_algebraMap`：of_subset_range_algebraMap
 (hf : f.LeftInverse (algebraMap R S)) (h : spectrum S a subseteq Set.range (alg
ebraMap R S)) : SpectrumRestricts …
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
-/
lemma nnreal_iff {a : A} :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔ ∀ x ∈ spectrum ℝ a, 0 ≤ x := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    exact coe_nonneg x
  · exact .of_subset_range_algebraMap (fun _ ↦ Real.toNNReal_coe) fun x hx ↦ ⟨⟨x, h x hx⟩, rfl⟩
/-
**SpectrumRestricts.nnreal_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestrict
s`。
形式化陈述：nnreal_of_nonneg [PartialOrder A] [NonnegSpectrumClass Real A] {a : A} (ha
 : 0 <= a) : SpectrumRestricts a ContinuousMap.realToNNReal
参数：ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SpectrumRestricts.nnreal_iff`：nnreal_iff {a : A} : SpectrumRestricts a C
ontinuousMap.realToNNReal ↔ forall x in spectrum Real a, 0 <= x
· 使用引理 `spectrum_nonneg_of_nonneg`：spectrum_nonneg_of_nonneg {𝕜 A : Type*} [Comm
Semiring 𝕜] [PartialOrder 𝕜] [Ring A] [PartialOrder A] [Algebra 𝕜 A] [NonnegSpec
trumClass 𝕜 A] …
-/
lemma nnreal_of_nonneg [PartialOrder A] [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    SpectrumRestricts a ContinuousMap.realToNNReal :=
  nnreal_iff.mpr <| spectrum_nonneg_of_nonneg ha
/-
**SpectrumRestricts.nnreal_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts`。
形式化陈述：nnreal_le_iff {a : A} (ha : SpectrumRestricts a ContinuousMap.realToNNReal
) {r : Real>=0} : (forall x in spectrum Real>=0 a, r <= x) ↔ forall x in spectru
m Real a, r <= x
参数：ha : SpectrumRestricts a ContinuousMap.realToNNReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nnreal_le_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, r ≤ x) ↔ ∀ x ∈ spectrum ℝ a, r ≤ x := by
  simp [← ha.algebraMap_image]
/-
**SpectrumRestricts.nnreal_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts`。
形式化陈述：nnreal_lt_iff {a : A} (ha : SpectrumRestricts a ContinuousMap.realToNNReal
) {r : Real>=0} : (forall x in spectrum Real>=0 a, r < x) ↔ forall x in spectrum
 Real a, r < x
参数：ha : SpectrumRestricts a ContinuousMap.realToNNReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma nnreal_lt_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, r < x) ↔ ∀ x ∈ spectrum ℝ a, r < x := by
  simp [← ha.algebraMap_image]
/-
**SpectrumRestricts.le_nnreal_iff** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts`。
形式化陈述：le_nnreal_iff {a : A} (ha : SpectrumRestricts a ContinuousMap.realToNNReal
) {r : Real>=0} : (forall x in spectrum Real>=0 a, x <= r) ↔ forall x in spectru
m Real a, x <= r
参数：ha : SpectrumRestricts a ContinuousMap.realToNNReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_nnreal_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, x ≤ r) ↔ ∀ x ∈ spectrum ℝ a, x ≤ r := by
  simp [← ha.algebraMap_image]
/-
**SpectrumRestricts.lt_nnreal_iff** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts`。
形式化陈述：lt_nnreal_iff {a : A} (ha : SpectrumRestricts a ContinuousMap.realToNNReal
) {r : Real>=0} : (forall x in spectrum Real>=0 a, x < r) ↔ forall x in spectrum
 Real a, x < r
参数：ha : SpectrumRestricts a ContinuousMap.realToNNReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lt_nnreal_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ spectrum ℝ≥0 a, x < r) ↔ ∀ x ∈ spectrum ℝ a, x < r := by
  simp [← ha.algebraMap_image]

end SpectrumRestricts

namespace QuasispectrumRestricts

open NNReal ENNReal
local notation "σₙ" => quasispectrum

variable {A : Type*} [NonUnitalRing A]

/-
**QuasispectrumRestricts.nnreal_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuasispectrumRest
ricts`。
形式化陈述：nnreal_iff [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A 
A] {a : A} : QuasispectrumRestricts a ContinuousMap.realToNNReal ↔ forall x in σ
ₙ Real a, 0 <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quasispectrumRestricts_iff_spectrumRestricts_inr`：quasispectrumRestricts
_iff_spectrumRestricts_inr (S : Type*) {R A : Type*} [Semifield R] [Field S] [No
nUnitalRing A] [Algebra R S] [Module R…
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr'`：quasispectrum_eq_spectrum_in
r' (R S : Type*) {A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra 
R S] [Module S A] [IsScalarTower…
· 使用引理 `SpectrumRestricts.nnreal_iff`：nnreal_iff {a : A} : SpectrumRestricts a C
ontinuousMap.realToNNReal ↔ forall x in spectrum Real a, 0 <= x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nnreal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A} :
    QuasispectrumRestricts a ContinuousMap.realToNNReal ↔ ∀ x ∈ σₙ ℝ a, 0 ≤ x := by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr,
    Unitization.quasispectrum_eq_spectrum_inr' _ ℝ, SpectrumRestricts.nnreal_iff]
/-
**QuasispectrumRestricts.nnreal_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Quasispectr
umRestricts`。
形式化陈述：nnreal_of_nonneg [Module Real A] [IsScalarTower Real A A] [SMulCommClass R
eal A A] [PartialOrder A] [NonnegSpectrumClass Real A] {a : A} (ha : 0 <= a) : Q
uasispectrumRestricts a ContinuousMap.realToNNReal
参数：ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `QuasispectrumRestricts.nnreal_iff`：nnreal_iff [Module Real A] [IsScalarT
ower Real A A] [SMulCommClass Real A A] {a : A} : QuasispectrumRestricts a Conti
nuousMap.realToNNReal ↔…
· 使用定理 `NonnegSpectrumClass.quasispectrum_nonneg_of_nonneg`：∀ {𝕜 : Type u_3} {A 
: Type u_4} {inst : CommSemiring 𝕜} {inst_1 : PartialOrder 𝕜} {inst_2 : NonUnita
lRing A}   {inst_3 : PartialOrder A} {in…
-/
lemma nnreal_of_nonneg [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [PartialOrder A]
    [NonnegSpectrumClass ℝ A] {a : A} (ha : 0 ≤ a) :
    QuasispectrumRestricts a ContinuousMap.realToNNReal :=
  nnreal_iff.mpr <| quasispectrum_nonneg_of_nonneg _ ha
/-
**QuasispectrumRestricts.le_nnreal_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuasispectrumR
estricts`。
形式化陈述：le_nnreal_iff [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real
 A A] {a : A} (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : Re
al>=0} : (forall x in quasispectrum Real>=0 a, x <= r) ↔ forall x in quasispectr
um Real a, x <= r
参数：ha : QuasispectrumRestricts a ContinuousMap.realToNNReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuasispectrumRestricts.algebraMap_image`：algebraMap_image (h : Quasispec
trumRestricts a f) : algebraMap R S '' quasispectrum R a = quasispectrum S a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_nnreal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A}
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ quasispectrum ℝ≥0 a, x ≤ r) ↔ ∀ x ∈ quasispectrum ℝ a, x ≤ r := by
  simp [← ha.algebraMap_image]
/-
**QuasispectrumRestricts.lt_nnreal_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuasispectrumR
estricts`。
形式化陈述：lt_nnreal_iff [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real
 A A] {a : A} (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : Re
al>=0} : (forall x in quasispectrum Real>=0 a, x < r) ↔ forall x in quasispectru
m Real a, x < r
参数：ha : QuasispectrumRestricts a ContinuousMap.realToNNReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuasispectrumRestricts.algebraMap_image`：algebraMap_image (h : Quasispec
trumRestricts a f) : algebraMap R S '' quasispectrum R a = quasispectrum S a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lt_nnreal_iff [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] {a : A}
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ≥0} :
    (∀ x ∈ quasispectrum ℝ≥0 a, x < r) ↔ ∀ x ∈ quasispectrum ℝ a, x < r := by
  simp [← ha.algebraMap_image]

end QuasispectrumRestricts

variable {A : Type*} [Ring A] [PartialOrder A]

open scoped NNReal

/-
**coe_mem_spectrum_real_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_mem_spectrum_real_of_nonneg [Algebra Real A] [NonnegSpectrumClass Real
 A] {a : A} {x : Real>=0} (ha : 0 <= a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用引理 `SpectrumRestricts.nnreal_of_nonneg`：nnreal_of_nonneg [PartialOrder A] [N
onnegSpectrumClass Real A] {a : A} (ha : 0 <= a) : SpectrumRestricts a Continuou
sMap.realToNNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_mem_spectrum_real_of_nonneg [Algebra ℝ A] [NonnegSpectrumClass ℝ A] {a : A} {x : ℝ≥0}
    (ha : 0 ≤ a := by cfc_tac) :
    (x : ℝ) ∈ spectrum ℝ a ↔ x ∈ spectrum ℝ≥0 a := by
  simp [← (SpectrumRestricts.nnreal_of_nonneg ha).algebraMap_image, Set.mem_image,
    NNReal.algebraMap_eq_coe]
