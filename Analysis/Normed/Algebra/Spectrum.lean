/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Analysis.Real.Spectrum
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Normed.Algebra.UnitizationL1
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace
public import Mathlib.Topology.Semicontinuity.Hemicontinuity

/-!
# The spectrum of elements in a complete normed algebra

This file contains the basic theory for the resolvent and spectrum of a Banach algebra.
Theorems specific to *complex* Banach algebras, such as *Gelfand's formula* can be found in
`Mathlib/Analysis/Normed/Algebra/GelfandFormula.lean`.

## Main definitions

* `spectralRadius : ℝ≥0∞`: supremum of `‖k‖₊` for all `k ∈ spectrum 𝕜 a`

## Main statements

* `spectrum.isOpen_resolventSet`: the resolvent set is open.
* `spectrum.isClosed`: the spectrum is closed.
* `spectrum.subset_closedBall_norm`: the spectrum is a subset of closed disk of radius
  equal to the norm.
* `spectrum.isCompact`: the spectrum is compact.
* `spectrum.spectralRadius_le_nnnorm`: the spectral radius is bounded above by the norm.

-/

@[expose] public section

assert_not_exists ProbabilityTheory.cond
assert_not_exists HasFDerivAt

open NormedSpace Topology -- For `NormedSpace.exp`.
open scoped ENNReal NNReal

/-- The *spectral radius* is the supremum of the `nnnorm` (`‖·‖₊`) of elements in the spectrum,
coerced into an element of `ℝ≥0∞`. Note that it is possible for `spectrum 𝕜 a = ∅`. In this
case, `spectralRadius a = 0`. It is also possible that `spectrum 𝕜 a` be unbounded (though
not for Banach algebras, see `spectrum.isBounded`, below).  In this case,
`spectralRadius a = ∞`. -/
@[wikidata Q249748]
/-
**spectralRadius** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：spectralRadius (𝕜 : Type*) {A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜
 A] (a : A) : Real>=0∞
参数：𝕜 : Type*；a : A。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *spectral radius* is the supremum of the `nnnorm` (`‖·‖₊`) of elements in th
e spectrum,
coerced into an element of `ℝ≥0∞`. Note that it is possible for `spectrum 𝕜 a = 
∅`. In this
case, `spectralRadius a = 0`. It is also possible that `spectrum 𝕜 a` be unbound
ed (though
not for Banach algebras, see `spectrum.isBounded`, below).  In this case,
`spectralRadius a = ∞`.
-/
noncomputable def spectralRadius (𝕜 : Type*) {A : Type*} [NormedField 𝕜] [Ring A] [Algebra 𝕜 A]
    (a : A) : ℝ≥0∞ :=
  ⨆ k ∈ spectrum 𝕜 a, ‖k‖₊

variable {𝕜 : Type*} {A : Type*}

namespace spectrum

section SpectrumCompact

open Filter

variable [NormedField 𝕜]

local notation "σ" => spectrum 𝕜
local notation "ρ" => resolventSet 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

section Algebra

variable [Ring A] [Algebra 𝕜 A]

@[simp]
/-
**spectrum.SpectralRadius.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `spectrum.Sp
ectralRadius`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 𝕜] [inst_1 : Ring A] [
inst_2 : Algebra 𝕜 A] [Subsingleton A]   (a : A), spectralRadius 𝕜 a = 0
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem SpectralRadius.of_subsingleton [Subsingleton A] (a : A) :
    spectralRadius 𝕜 a = 0 := by
  simp [spectralRadius]

@[simp]
/-
**spectrum.spectralRadius_zero** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：spectralRadius_zero : spectralRadius 𝕜 (0 : A) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.SpectralRadius.of_subsingleton`：∀ {𝕜 : Type u_1} {A : Type u_2}
 [inst : NormedField 𝕜] [inst_1 : Ring A] [inst_2 : Algebra 𝕜 A] [Subsingleton A
]   (a : A), spectralRadius 𝕜…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `spectrum.zero_eq`：zero_eq [Nontrivial A] : σ (0 : A) = {0}
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
-/
theorem spectralRadius_zero : spectralRadius 𝕜 (0 : A) = 0 := by
  nontriviality A
  simp [spectralRadius]

@[simp]
/-
**spectrum.spectralRadius_one** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：spectralRadius_one [Nontrivial A] : spectralRadius 𝕜 (1 : A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `spectrum.one_eq`：one_eq [Nontrivial A] : σ (1 : A) = {1}
· 使用定理 `iSup_iSup_eq_left`：iSup_iSup_eq_left {b : β} {f : forall x : β, x = b ->
 α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem spectralRadius_one [Nontrivial A] :
    spectralRadius 𝕜 (1 : A) = 1 := by
  simp [spectralRadius]
/-
**spectrum.mem_resolventSet_of_spectralRadius_lt** 是 Mathlib 中的一个定理，位于命名空间 `spec
trum`。
形式化陈述：mem_resolventSet_of_spectralRadius_lt {a : A} {k : 𝕜} (h : spectralRadius 
𝕜 a < ‖k‖₊) : k in ρ a
参数：h : spectralRadius 𝕜 a < ‖k‖₊。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
-/
theorem mem_resolventSet_of_spectralRadius_lt {a : A} {k : 𝕜}
    (h : spectralRadius 𝕜 a < ‖k‖₊) : k ∈ ρ a :=
  Classical.not_not.mp fun hn => h.not_ge <| le_iSup₂ (α := ℝ≥0∞) k hn
/-
**spectrum.spectralRadius_pow_le** 是 Mathlib 中的一个引理，位于命名空间 `spectrum`。
形式化陈述：spectralRadius_pow_le (a : A) (n : Nat) (hn : n != 0) : (spectralRadius 𝕜 
a) ^ n <= spectralRadius 𝕜 (a ^ n)
参数：a : A；n : Nat；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.iSup₂_pow_of_ne_zero`：iSup₂_pow_of_ne_zero {κ : ι -> Sort*} (f :
 (i : ι) -> κ i -> Real>=0∞) {n : Nat} (hn : n != 0) : (⨆ i, ⨆ j, f i j) ^ n = ⨆
 i, ⨆ j, f i j ^ n
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用定理 `spectrum.pow_mem_pow`：pow_mem_pow (a : A) (n : Nat) {k : 𝕜} (hk : k in σ
 a) : k ^ n in σ (a ^ n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nnnorm_pow`：nnnorm_pow (a : α) (n : Nat) : ‖a ^ n‖₊ = ‖a‖₊ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
lemma spectralRadius_pow_le (a : A) (n : ℕ) (hn : n ≠ 0) :
    (spectralRadius 𝕜 a) ^ n ≤ spectralRadius 𝕜 (a ^ n) := by
  simp only [spectralRadius, ENNReal.iSup₂_pow_of_ne_zero _ hn]
  refine iSup₂_le fun x hx ↦ ?_
  apply le_iSup₂_of_le (x ^ n) (spectrum.pow_mem_pow a n hx)
  simp
/-
**spectrum.spectralRadius_pow_le'** 是 Mathlib 中的一个引理，位于命名空间 `spectrum`。
形式化陈述：spectralRadius_pow_le' [Nontrivial A] (a : A) (n : Nat) : (spectralRadius 
𝕜 a) ^ n <= spectralRadius 𝕜 (a ^ n)
参数：a : A；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `spectrum.spectralRadius_one`：spectralRadius_one [Nontrivial A] : spectra
lRadius 𝕜 (1 : A) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `spectrum.spectralRadius_pow_le`：spectralRadius_pow_le (a : A) (n : Nat) 
(hn : n != 0) : (spectralRadius 𝕜 a) ^ n <= spectralRadius 𝕜 (a ^ n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma spectralRadius_pow_le' [Nontrivial A] (a : A) (n : ℕ) :
    (spectralRadius 𝕜 a) ^ n ≤ spectralRadius 𝕜 (a ^ n) := by
  cases n
  · simp
  · exact spectralRadius_pow_le a _ (by simp)

end Algebra

variable [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/-
**spectrum.isOpen_resolventSet** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：isOpen_resolventSet (a : A) : IsOpen (ρ a)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuous_algebraMap`：continuous_algebraMap [ContinuousSMul R A] : Cont
inuous (algebraMap R A)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Units.isOpen`：∀ {R : Type u_1} [inst : NormedRing R] [HasSummableGeomSer
ies R], IsOpen {x | IsUnit x}
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
-/
theorem isOpen_resolventSet (a : A) : IsOpen (ρ a) :=
  Units.isOpen.preimage (by fun_prop)

@[simp]
/-
**spectrum.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 𝕜] [inst_1 : NormedRin
g A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] (a : A), IsClosed (spectru
m 𝕜 a)
参数：a : A；spectrum 𝕜 a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `spectrum.isOpen_resolventSet`：isOpen_resolventSet (a : A) : IsOpen (ρ a)
-/
protected theorem isClosed (a : A) : IsClosed (σ a) :=
  (isOpen_resolventSet a).isClosed_compl
/-
**spectrum.mem_resolventSet_of_norm_lt_mul** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：mem_resolventSet_of_norm_lt_mul {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖
) : k in ρ a
参数：h : ‖a‖ * ‖(1 : A)‖ < ‖k‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `resolventSet.eq_1`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R] [
inst_1 : Ring A] [inst_2 : Algebra R A] (a : A),   resolventSet R a = {r | IsUni
t ((alg…
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `ne_zero_of_norm_ne_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E}, ‖a‖ ≠ 0 → a ≠ 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `norm_algebraMap`：norm_algebraMap (x : 𝕜) : ‖algebraMap 𝕜 𝕜' x‖ = ‖x‖ * ‖
(1 : 𝕜')‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `mul_inv_lt_iff₀'`：mul_inv_lt_iff₀' (hc : 0 < c) : b * c⁻¹ < a ↔ b < c * 
a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
（共 37 条，此处仅展示前 30 条）
-/
theorem mem_resolventSet_of_norm_lt_mul {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖) : k ∈ ρ a := by
  rw [resolventSet, Set.mem_ofPred_eq, Algebra.algebraMap_eq_smul_one]
  nontriviality A
  have hk : k ≠ 0 :=
    ne_zero_of_norm_ne_zero ((mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans_lt h).ne'
  let ku := Units.map ↑ₐ.toMonoidHom (Units.mk0 k hk)
  rw [← inv_inv ‖(1 : A)‖,
    mul_inv_lt_iff₀' (inv_pos.2 <| norm_pos_iff.2 (one_ne_zero : (1 : A) ≠ 0))] at h
  have hku : ‖-a‖ < ‖(↑ku⁻¹ : A)‖⁻¹ := by simpa [ku, norm_algebraMap] using h
  simpa [ku, sub_eq_add_neg, Algebra.algebraMap_eq_smul_one] using (ku.add (-a) hku).isUnit
/-
**spectrum.mem_resolventSet_of_norm_lt** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：mem_resolventSet_of_norm_lt [NormOneClass A] {a : A} {k : 𝕜} (h : ‖a‖ < ‖k
‖) : k in ρ a
参数：h : ‖a‖ < ‖k‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.mem_resolventSet_of_norm_lt_mul`：mem_resolventSet_of_norm_lt_mu
l {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖) : k in ρ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mem_resolventSet_of_norm_lt [NormOneClass A] {a : A} {k : 𝕜} (h : ‖a‖ < ‖k‖) : k ∈ ρ a :=
  mem_resolventSet_of_norm_lt_mul (by rwa [norm_one, mul_one])
/-
**spectrum.norm_le_norm_mul_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：norm_le_norm_mul_of_mem {a : A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖ * ‖(1
 : A)‖
参数：hk : k in σ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `spectrum.mem_resolventSet_of_norm_lt_mul`：mem_resolventSet_of_norm_lt_mu
l {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖) : k in ρ a
-/
theorem norm_le_norm_mul_of_mem {a : A} {k : 𝕜} (hk : k ∈ σ a) : ‖k‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  le_of_not_gt <| mt mem_resolventSet_of_norm_lt_mul hk
/-
**spectrum.norm_le_norm_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：norm_le_norm_of_mem [NormOneClass A] {a : A} {k : 𝕜} (hk : k in σ a) : ‖k‖
 <= ‖a‖
参数：hk : k in σ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `spectrum.mem_resolventSet_of_norm_lt`：mem_resolventSet_of_norm_lt [NormO
neClass A] {a : A} {k : 𝕜} (h : ‖a‖ < ‖k‖) : k in ρ a
-/
theorem norm_le_norm_of_mem [NormOneClass A] {a : A} {k : 𝕜} (hk : k ∈ σ a) : ‖k‖ ≤ ‖a‖ :=
  le_of_not_gt <| mt mem_resolventSet_of_norm_lt hk
/-
**spectrum.subset_closedBall_norm_mul** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：subset_closedBall_norm_mul (a : A) : σ a subseteq Metric.closedBall (0 : 𝕜
) (‖a‖ * ‖(1 : A)‖)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `spectrum.norm_le_norm_mul_of_mem`：norm_le_norm_mul_of_mem {a : A} {k : 𝕜
} (hk : k in σ a) : ‖k‖ <= ‖a‖ * ‖(1 : A)‖
-/
theorem subset_closedBall_norm_mul (a : A) : σ a ⊆ Metric.closedBall (0 : 𝕜) (‖a‖ * ‖(1 : A)‖) :=
  fun k hk => by simp [norm_le_norm_mul_of_mem hk]
/-
**spectrum.subset_closedBall_norm** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：subset_closedBall_norm [NormOneClass A] (a : A) : σ a subseteq Metric.clos
edBall (0 : 𝕜) ‖a‖
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `spectrum.norm_le_norm_of_mem`：norm_le_norm_of_mem [NormOneClass A] {a : 
A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖
-/
theorem subset_closedBall_norm [NormOneClass A] (a : A) : σ a ⊆ Metric.closedBall (0 : 𝕜) ‖a‖ :=
  fun k hk => by simp [norm_le_norm_of_mem hk]

@[simp]
/-
**spectrum.isBounded** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：isBounded (a : A) : Bornology.IsBounded (σ a)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `spectrum.subset_closedBall_norm_mul`：subset_closedBall_norm_mul (a : A) 
: σ a subseteq Metric.closedBall (0 : 𝕜) (‖a‖ * ‖(1 : A)‖)
-/
theorem isBounded (a : A) : Bornology.IsBounded (σ a) :=
  Metric.isBounded_closedBall.subset (subset_closedBall_norm_mul a)

@[simp]
/-
**spectrum.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 𝕜] [inst_1 : NormedRin
g A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] [ProperSpace 𝕜] (a : A), I
sCompact (spectrum 𝕜 a)
参数：a : A；spectrum 𝕜 a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isCompact_of_isClosed_isBounded`：isCompact_of_isClosed_isBounded 
[ProperSpace α] (hc : IsClosed s) (hb : IsBounded s) : IsCompact s
· 使用定理 `spectrum.isClosed`：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 𝕜
] [inst_1 : NormedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] (a : 
A), IsC…
· 使用定理 `spectrum.isBounded`：isBounded (a : A) : Bornology.IsBounded (σ a)
-/
protected theorem isCompact [ProperSpace 𝕜] (a : A) : IsCompact (σ a) :=
  Metric.isCompact_of_isClosed_isBounded (spectrum.isClosed a) (isBounded a)

grind_pattern spectrum.isCompact => IsCompact (spectrum 𝕜 a)
/-
**spectrum.instCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `spectrum`。
形式化陈述：instCompactSpace [ProperSpace 𝕜] (a : A) : CompactSpace (spectrum 𝕜 a)
参数：a : A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `spectrum.isCompact`：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 
𝕜] [inst_1 : NormedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] [Pro
perSpace…
-/
instance instCompactSpace [ProperSpace 𝕜] (a : A) : CompactSpace (spectrum 𝕜 a) :=
  isCompact_iff_compactSpace.mp <| spectrum.isCompact a
/-
**spectrum.instCompactSpaceNNReal** 是 Mathlib 中的一个实例，位于命名空间 `spectrum`。
形式化陈述：instCompactSpaceNNReal {A : Type*} [NormedRing A] [NormedAlgebra Real A] (
a : A) [CompactSpace (spectrum Real a)] : CompactSpace (spectrum Real>=0 a)
参数：a : A；spectrum Real a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `spectrum.preimage_algebraMap`：preimage_algebraMap (S : Type*) {R A : Typ
e*} [CommSemiring R] [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Alge
bra S A] [IsScalar…
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
· 使用引理 `isClosed_nonneg`：isClosed_nonneg : IsClosed {x : α | 0 <= x}
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
instance instCompactSpaceNNReal {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (a : A) [CompactSpace (spectrum ℝ a)] : CompactSpace (spectrum ℝ≥0 a) := by
  rw [← isCompact_iff_compactSpace] at *
  rw [← preimage_algebraMap ℝ]
  exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage <| by assumption

@[simp]
/-
**spectrum.isCompact_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：isCompact_nnreal {A : Type*} [NormedRing A] [NormedAlgebra Real A] (a : A)
 [CompactSpace (spectrum Real a)] : IsCompact (spectrum Real>=0 a)
参数：a : A；spectrum Real a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
-/
theorem isCompact_nnreal {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (a : A) [CompactSpace (spectrum ℝ a)] : IsCompact (spectrum ℝ≥0 a) := by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern isCompact_nnreal => IsCompact (spectrum ℝ≥0 a)

section QuasispectrumCompact

variable {B : Type*} [NonUnitalNormedRing B] [NormedSpace 𝕜 B] [CompleteSpace B]
variable [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B] [ProperSpace 𝕜]

@[simp]
/-
**spectrum._root_.quasispectrum.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.quasispectrum.isCompact (a : B) : IsCompact (quasispectrum 𝕜 a) := by
  rw [Unitization.quasispectrum_eq_spectrum_inr' 𝕜 𝕜,
    ← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv 𝕜).symm (a : Unitization 𝕜 B)]
  exact spectrum.isCompact _

grind_pattern quasispectrum.isCompact => IsCompact (quasispectrum 𝕜 a)
/-
**spectrum._root_.quasispectrum.instCompactSpace** 是 Mathlib 中的一个实例，位于命名空间 `spec
trum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.quasispectrum.instCompactSpace (a : B) :
    CompactSpace (quasispectrum 𝕜 a) :=
  isCompact_iff_compactSpace.mp <| quasispectrum.isCompact a
/-
**spectrum._root_.quasispectrum.instCompactSpaceNNReal** 是 Mathlib 中的一个实例，位于命名空间
 `spectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.quasispectrum.instCompactSpaceNNReal [NormedSpace ℝ B] [IsScalarTower ℝ B B]
    [SMulCommClass ℝ B B] (a : B) [CompactSpace (quasispectrum ℝ a)] :
    CompactSpace (quasispectrum ℝ≥0 a) := by
  rw [← isCompact_iff_compactSpace] at *
  rw [← quasispectrum.preimage_algebraMap ℝ]
  exact isClosed_nonneg.isClosedEmbedding_subtypeVal.isCompact_preimage <| by assumption

omit [CompleteSpace B] in
@[simp]
/-
**spectrum._root_.quasispectrum.isCompact_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `spec
trum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.quasispectrum.isCompact_nnreal [NormedSpace ℝ B] [IsScalarTower ℝ B B]
    [SMulCommClass ℝ B B] (a : B) [CompactSpace (quasispectrum ℝ a)] :
    IsCompact (quasispectrum ℝ≥0 a) := by
  rw [isCompact_iff_compactSpace]
  infer_instance

grind_pattern quasispectrum.isCompact_nnreal => IsCompact (quasispectrum ℝ≥0 a)

end QuasispectrumCompact

section NNReal

open NNReal

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**spectrum.le_nnnorm_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：le_nnnorm_of_mem {a : A} {r : Real>=0} (hr : r in spectrum Real>=0 a) : r 
<= ‖a‖₊
参数：hr : r in spectrum Real>=0 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.le_norm_self`：le_norm_self (r : Real) : r <= ‖r‖
· 使用定理 `spectrum.norm_le_norm_of_mem`：norm_le_norm_of_mem [NormOneClass A] {a : 
A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖
-/
theorem le_nnnorm_of_mem {a : A} {r : ℝ≥0} (hr : r ∈ spectrum ℝ≥0 a) :
    r ≤ ‖a‖₊ := calc
  r ≤ ‖(r : ℝ)‖ := Real.le_norm_self _
  _ ≤ ‖a‖       := norm_le_norm_of_mem hr
/-
**spectrum.coe_le_norm_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：coe_le_norm_of_mem {a : A} {r : Real>=0} (hr : r in spectrum Real>=0 a) : 
r <= ‖a‖
参数：hr : r in spectrum Real>=0 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.coe_mono`：Monotone NNReal.toReal
· 使用定理 `spectrum.le_nnnorm_of_mem`：le_nnnorm_of_mem {a : A} {r : Real>=0} (hr : 
r in spectrum Real>=0 a) : r <= ‖a‖₊
-/
theorem coe_le_norm_of_mem {a : A} {r : ℝ≥0} (hr : r ∈ spectrum ℝ≥0 a) :
    r ≤ ‖a‖ :=
  coe_mono <| le_nnnorm_of_mem hr

end NNReal

/-
**spectrum.spectralRadius_le_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：spectralRadius_le_nnnorm [NormOneClass A] (a : A) : spectralRadius 𝕜 a <= 
‖a‖₊
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectrum.norm_le_norm_of_mem`：norm_le_norm_of_mem [NormOneClass A] {a : 
A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖
-/
theorem spectralRadius_le_nnnorm [NormOneClass A] (a : A) : spectralRadius 𝕜 a ≤ ‖a‖₊ := by
  refine iSup₂_le fun k hk => ?_
  exact mod_cast norm_le_norm_of_mem hk
/-
**spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间
 `spectrum`。
形式化陈述：exists_nnnorm_eq_spectralRadius_of_nonempty [ProperSpace 𝕜] {a : A} (ha : 
(σ a).Nonempty) : exists k in σ a, (‖k‖₊ : Real>=0∞) = spectralRadius 𝕜 a
参数：ha : (σ a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `spectrum.isCompact`：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 
𝕜] [inst_1 : NormedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] [Pro
perSpace…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_nnnorm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Conti
nuous fun a => ‖a‖₊
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem exists_nnnorm_eq_spectralRadius_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty) :
    ∃ k ∈ σ a, (‖k‖₊ : ℝ≥0∞) = spectralRadius 𝕜 a := by
  obtain ⟨k, hk, h⟩ := (spectrum.isCompact a).exists_isMaxOn ha continuous_nnnorm.continuousOn
  exact ⟨k, hk, le_antisymm (le_iSup₂ (α := ℝ≥0∞) k hk) (iSup₂_le <| mod_cast h)⟩
/-
**spectrum.spectralRadius_lt_of_forall_lt_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 
`spectrum`。
形式化陈述：spectralRadius_lt_of_forall_lt_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (
σ a).Nonempty) {r : Real>=0} (hr : forall k in σ a, ‖k‖₊ < r) : spectralRadius 𝕜
 a < r
参数：ha : (σ a).Nonempty；hr : forall k in σ a, ‖k‖₊ < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsCompact.sSup_lt_iff_of_continuous`：IsCompact.sSup_lt_iff_of_continuous
 [ClosedIciTopology α] {f : β -> α} {K : Set β} (hK : IsCompact K) (h0K : K.None
mpty) (hf : ContinuousOn …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `spectrum.isCompact`：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 
𝕜] [inst_1 : NormedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] [Pro
perSpace…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `continuous_enorm`：continuous_enorm : Continuous fun a : E => ‖a‖ₑ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem spectralRadius_lt_of_forall_lt_of_nonempty [ProperSpace 𝕜] {a : A} (ha : (σ a).Nonempty)
    {r : ℝ≥0} (hr : ∀ k ∈ σ a, ‖k‖₊ < r) : spectralRadius 𝕜 a < r :=
  sSup_image.symm.trans_lt <| ((spectrum.isCompact a).sSup_lt_iff_of_continuous ha
    continuous_enorm.continuousOn (r : ℝ≥0∞)).mpr (by simpa using hr)

open ENNReal Polynomial

variable (𝕜)
/-
**spectrum.spectralRadius_le_pow_nnnorm_pow_one_div** 是 Mathlib 中的一个定理，位于命名空间 `s
pectrum`。
形式化陈述：spectralRadius_le_pow_nnnorm_pow_one_div (a : A) (n : Nat) : spectralRadiu
s 𝕜 a <= (‖a ^ (n + 1)‖₊ : Real>=0∞) ^ (1 / (n + 1) : Real) * (‖(1 : A)‖₊ : Real
>=0∞) ^ (1 / (n + 1) : Real)
参数：a : A；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.aeval_monomial`：aeval_monomial {n : Nat} {r : R} : aeval x (m
onomial n r) = algebraMap _ _ r * x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.eval_monomial`：eval_monomial {n a} : (monomial n a).eval x = 
a * x ^ n
· 使用定理 `spectrum.subset_polynomial_aeval`：subset_polynomial_aeval (a : A) (p : 𝕜
[X]) : (eval · p) '' σ a subseteq σ (aeval a p)
· 使用定理 `norm_toNNReal`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E}, ‖
a‖.toNNReal = ‖a‖₊
· 使用定理 `nnnorm_pow`：nnnorm_pow (a : α) (n : Nat) : ‖a ^ n‖₊ = ‖a‖₊ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Real.toNNReal_mul`：toNNReal_mul {p q : Real} (hp : 0 <= p) : Real.toNNRe
al (p * q) = Real.toNNReal p * Real.toNNReal q
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `ENNReal.coe_mono`：coe_mono : Monotone ofNNReal
· 使用定理 `Real.toNNReal_mono`：∀ {r₁ r₂ : ℝ}, r₁ ≤ r₂ → r₁.toNNReal ≤ r₂.toNNReal
· 使用定理 `spectrum.norm_le_norm_mul_of_mem`：norm_le_norm_mul_of_mem {a : A} {k : 𝕜
} (hk : k in σ a) : ‖k‖ <= ‖a‖ * ‖(1 : A)‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Nat.succ_pos'`：succ_pos' : 0 < succ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `ENNReal.pow_rpow_inv_natCast`：pow_rpow_inv_natCast {n : Nat} (hn : n != 
0) (x : Real>=0∞) : (x ^ n) ^ (n⁻¹ : Real) = x
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
（共 45 条，此处仅展示前 30 条）
-/
theorem spectralRadius_le_pow_nnnorm_pow_one_div (a : A) (n : ℕ) :
    spectralRadius 𝕜 a ≤ (‖a ^ (n + 1)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ) *
      (‖(1 : A)‖₊ : ℝ≥0∞) ^ (1 / (n + 1) : ℝ) := by
  refine iSup₂_le fun k hk => ?_
  -- apply easy direction of the spectral mapping theorem for polynomials
  have pow_mem : k ^ (n + 1) ∈ σ (a ^ (n + 1)) := by
    simpa only [one_mul, Algebra.algebraMap_eq_smul_one, one_smul, aeval_monomial, one_mul,
      eval_monomial] using subset_polynomial_aeval a (@monomial 𝕜 _ (n + 1) (1 : 𝕜)) ⟨k, hk, rfl⟩
  -- power of the norm is bounded by norm of the power
  have nnnorm_pow_le : (↑(‖k‖₊ ^ (n + 1)) : ℝ≥0∞) ≤ ‖a ^ (n + 1)‖₊ * ‖(1 : A)‖₊ := by
    simpa only [Real.toNNReal_mul (norm_nonneg _), norm_toNNReal, nnnorm_pow k (n + 1),
      ENNReal.coe_mul] using coe_mono (Real.toNNReal_mono (norm_le_norm_mul_of_mem pow_mem))
  -- take (n + 1)ᵗʰ roots and clean up the left-hand side
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := mod_cast Nat.succ_pos'
  convert monotone_rpow_of_nonneg (one_div_pos.mpr hn).le nnnorm_pow_le
  all_goals dsimp
  · rw [one_div, pow_rpow_inv_natCast]
    positivity
  rw [Nat.cast_succ, ENNReal.coe_mul_rpow]
/-
**spectrum.spectralRadius_le_liminf_pow_nnnorm_pow_one_div** 是 Mathlib 中的一个定理，位于
命名空间 `spectrum`。
形式化陈述：spectralRadius_le_liminf_pow_nnnorm_pow_one_div (a : A) : spectralRadius 𝕜
 a <= atTop.liminf fun n : Nat => (‖a ^ n‖₊ : Real>=0∞) ^ (1 / n : Real)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.le_of_forall_lt_one_mul_le`：le_of_forall_lt_one_mul_le {x y : Re
al>=0∞} (h : forall a < 1, a * x <= y) : x <= y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Filter.liminf_eq_iSup_iInf_of_nat'`：liminf_eq_iSup_iInf_of_nat' {u : Nat
 -> α} : liminf u atTop = ⨆ n : Nat, ⨅ i : Nat, u (i + n)
· 使用定理 `ENNReal.mul_le_iff_le_inv`：mul_le_iff_le_inv {a b r : Real>=0∞} (hr₀ : r
 != 0) (hr₁ : r != ∞) : r * a <= b ↔ a <= r⁻¹ * b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `ENNReal.iSup_mul`：iSup_mul (f : ι -> Real>=0∞) (a : Real>=0∞) : (⨆ i, f 
i) * a = ⨆ i, f i * a
· 使用引理 `ENNReal.iInf_mul`：iInf_mul [Nonempty ι] (hinfty : a = ∞ -> ⨅ i, f i = 0 
-> exists i, f i = 0) : (⨅ i, f i) * a = ⨅ i, f i * a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
（共 51 条，此处仅展示前 30 条）
-/
theorem spectralRadius_le_liminf_pow_nnnorm_pow_one_div (a : A) :
    spectralRadius 𝕜 a ≤ atTop.liminf fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) := by
  refine ENNReal.le_of_forall_lt_one_mul_le fun ε hε => ?_
  by_cases h : ε = 0
  · simp [h]
  simp only [ENNReal.mul_le_iff_le_inv h (hε.trans_le le_top).ne, mul_comm ε⁻¹,
    liminf_eq_iSup_iInf_of_nat', ENNReal.iSup_mul]
  conv_rhs => arg 1; intro i; rw [ENNReal.iInf_mul (by simp [h])]
  rw [← ENNReal.inv_lt_inv, inv_one] at hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ENNReal.eventually_pow_one_div_le (ENNReal.coe_ne_top : ↑‖(1 : A)‖₊ ≠ ∞) hε)
  refine le_trans ?_ (le_iSup _ (N + 1))
  refine le_iInf fun n => ?_
  simp only [← add_assoc]
  refine (spectralRadius_le_pow_nnnorm_pow_one_div 𝕜 a (n + N)).trans ?_
  norm_cast
  grw [hN (n + N + 1) (by lia)]

end SpectrumCompact

section resolvent

open Filter Asymptotics Bornology Topology

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "ρ" => resolventSet 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

/-
**spectrum.eventually_isUnit_resolvent** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：eventually_isUnit_resolvent (a : A) : forallᶠ z in cobounded 𝕜, IsUnit (re
solvent a z)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.cobounded_of_norm`：∀ {E : Type u_2} [inst : SeminormedAd
dGroup E] {ι : Sort u_5} {p : ι → Prop} {s : ι → Set ℝ},   Filter.atTop.HasBasis
 p s → (Bornology.cobou…
· 使用引理 `Filter.atTop_basis_Ioi`：atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@
atTop α _).HasBasis (fun _ => True) Ioi
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `trivial`：True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `spectrum.isUnit_resolvent`：isUnit_resolvent {r : R} {a : A} : r in resol
ventSet R a ↔ IsUnit (resolvent a r)
· 使用定理 `spectrum.mem_resolventSet_of_norm_lt_mul`：mem_resolventSet_of_norm_lt_mu
l {a : A} {k : 𝕜} (h : ‖a‖ * ‖(1 : A)‖ < ‖k‖) : k in ρ a
-/
theorem eventually_isUnit_resolvent (a : A) : ∀ᶠ z in cobounded 𝕜, IsUnit (resolvent a z) := by
  rw [atTop_basis_Ioi.cobounded_of_norm.eventually_iff]
  exact ⟨‖a‖ * ‖(1 : A)‖, trivial, fun _ ↦ isUnit_resolvent.mp ∘ mem_resolventSet_of_norm_lt_mul⟩
/-
**spectrum.resolvent_isBigO_inv** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：resolvent_isBigO_inv (a : A) : resolvent a =O[cobounded 𝕜] Inv.inv
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `NormedRing.inverse_one_sub_norm`：inverse_one_sub_norm : (fun t : R => in
verse (1 - t)) =O[𝓝 0] (fun _t => 1 : R -> Real)
· 使用定理 `instHasSummableGeomSeriesOfCompleteSpace`：∀ {R : Type u_4} [inst : Norme
dRing R] [CompleteSpace R], HasSummableGeomSeries R
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Filter.Tendsto.smul_const`：Filter.Tendsto.smul_const {f : α -> M} {l : F
ilter α} {c : M} (hf : Tendsto f l (𝓝 c)) (a : X) : Tendsto (fun x => f x • a) l
 (𝓝 (c • a))
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Filter.tendsto_inv₀_cobounded`：tendsto_inv₀_cobounded : Tendsto Inv.inv 
(cobounded α) (𝓝 0)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Bornology.isBounded_singleton`：isBounded_singleton : IsBounded ({x} : Se
t α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `spectrum.units_smul_resolvent_self`：units_smul_resolvent_self {r : Rˣ} {
a : A} : r • resolvent a (r : R) = resolvent (r⁻¹ • a) (1 : R)
（共 37 条，此处仅展示前 30 条）
-/
theorem resolvent_isBigO_inv (a : A) : resolvent a =O[cobounded 𝕜] Inv.inv :=
  have h : (fun z ↦ resolvent (z⁻¹ • a) (1 : 𝕜)) =O[cobounded 𝕜] (fun _ ↦ (1 : ℝ)) := by
    simpa [Function.comp_def, resolvent] using
      (NormedRing.inverse_one_sub_norm (R := A)).comp_tendsto
        (by simpa using (tendsto_inv₀_cobounded (α := 𝕜)).smul_const a)
  calc
    resolvent a =ᶠ[cobounded 𝕜] fun z ↦ z⁻¹ • resolvent (z⁻¹ • a) (1 : 𝕜) := by
      filter_upwards [isBounded_singleton (x := 0)] with z hz
      lift z to 𝕜ˣ using Ne.isUnit hz
      simpa [Units.smul_def] using congr(z⁻¹ • $(units_smul_resolvent_self (r := z) (a := a)))
    _ =O[cobounded 𝕜] (· ⁻¹) := .of_norm_right <| by
      simpa using (isBigO_refl (· ⁻¹) (cobounded 𝕜)).norm_right.smul h
/-
**spectrum.resolvent_tendsto_cobounded** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：resolvent_tendsto_cobounded (a : A) : Tendsto (resolvent a) (cobounded 𝕜) 
(𝓝 0)
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_tendsto`：∀ {α : Type u_1} {E'' : Type u_9} {F''
 : Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F''] 
  {f'' : α → E''} {g''…
· 使用定理 `spectrum.resolvent_isBigO_inv`：resolvent_isBigO_inv (a : A) : resolvent 
a =O[cobounded 𝕜] Inv.inv
· 使用定理 `Filter.tendsto_inv₀_cobounded`：tendsto_inv₀_cobounded : Tendsto Inv.inv 
(cobounded α) (𝓝 0)
-/
theorem resolvent_tendsto_cobounded (a : A) : Tendsto (resolvent a) (cobounded 𝕜) (𝓝 0) :=
  resolvent_isBigO_inv a |>.trans_tendsto tendsto_inv₀_cobounded

end resolvent

section OneSubSMul

open ContinuousMultilinearMap ENNReal FormalMultilinearSeries

open scoped NNReal ENNReal

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

variable (𝕜) in
/-- In a Banach algebra `A` over a nontrivially normed field `𝕜`, for any `a : A` the
power series with coefficients `a ^ n` represents the function `(1 - z • a)⁻¹` in a disk of
radius `‖a‖₊⁻¹`. -/
/-
**spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul** 是 Mathlib 中的一个定理，位于命名空间 
`spectrum`。
形式化陈述：hasFPowerSeriesOnBall_inverse_one_sub_smul [HasSummableGeomSeries A] (a : 
A) : HasFPowerSeriesOnBall (fun z : 𝕜 => Ring.inverse (1 - z • a)) (fun n => Con
tinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (a ^ n)) 0 ‖a‖₊⁻¹
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ENNReal.le_of_forall_nnreal_lt`：le_of_forall_nnreal_lt {x y : Real>=0∞} 
(h : forall r : Real>=0, ↑r < x -> ↑r <= y) : x <= y
· 使用定理 `FormalMultilinearSeries.le_radius_of_bound_nnreal`：le_radius_of_bound_nn
real (C : Real>=0) {r : Real>=0} (h : forall n : Nat, ‖p n‖₊ * r ^ n <= C) : (r 
: Real>=0∞) <= p.radius
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_toNNReal`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E}, ‖
a‖.toNNReal = ‖a‖₊
· 使用定理 `ContinuousMultilinearMap.norm_mkPiRing`：norm_mkPiRing (z : G) : ‖Continu
ousMultilinearMap.mkPiRing 𝕜 ι z‖ = ‖z‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `nnnorm_pow_le'`：∀ {α : Type u_2} [inst : SeminormedRing α] (a : α) {n : 
ℕ}, 0 < n → ‖a ^ n‖₊ ≤ ‖a‖₊ ^ n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_le_one'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder M] [M
ulLeftMono M] {a : M}, a ≤ 1 → ∀ (n : ℕ), a ^ n ≤ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NNReal.lt_inv_iff_mul_lt`：lt_inv_iff_mul_lt {r p : Real>=0} (h : p != 0)
 : r < p⁻¹ ↔ r * p < 1
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
In a Banach algebra `A` over a nontrivially normed field `𝕜`, for any `a : A` th
e
power series with coefficients `a ^ n` represents the function `(1 - z • a)⁻¹` i
n a disk of
radius `‖a‖₊⁻¹`.
-/
theorem hasFPowerSeriesOnBall_inverse_one_sub_smul [HasSummableGeomSeries A] (a : A) :
    HasFPowerSeriesOnBall (fun z : 𝕜 => Ring.inverse (1 - z • a))
      (fun n => ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) (a ^ n)) 0 ‖a‖₊⁻¹ :=
  { r_le := by
      refine le_of_forall_nnreal_lt fun r hr =>
        le_radius_of_bound_nnreal _ (max 1 ‖(1 : A)‖₊) fun n => ?_
      rw [← norm_toNNReal, norm_mkPiRing, norm_toNNReal]
      rcases n with - | n
      · simp
      · grw [nnnorm_pow_le' a n.succ_pos, ← le_max_left]
        by_cases h : ‖a‖₊ = 0
        · simp [h, pow_succ']
        · rw [← coe_inv h, coe_lt_coe, NNReal.lt_inv_iff_mul_lt h] at hr
          simpa only [← mul_pow, mul_comm] using! pow_le_one' hr.le n.succ
    r_pos := ENNReal.inv_pos.mpr coe_ne_top
    hasSum := fun {y} hy => by
      have norm_lt : ‖y • a‖ < 1 := by
        by_cases h : ‖a‖₊ = 0
        · simp only [nnnorm_eq_zero.mp h, norm_zero, zero_lt_one, smul_zero]
        · have nnnorm_lt : ‖y‖₊ < ‖a‖₊⁻¹ := by
            simpa only [← coe_inv h, mem_ball_zero_iff, Metric.eball_coe] using! hy
          rwa [← coe_nnnorm, ← Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_one, nnnorm_smul,
            ← NNReal.lt_inv_iff_mul_lt h]
      simpa [← smul_pow, (summable_geometric_of_norm_lt_one norm_lt).hasSum_iff] using!
        (NormedRing.inverse_one_sub _ norm_lt).symm }
/-
**spectrum.isUnit_one_sub_smul_of_lt_inv_radius** 是 Mathlib 中的一个定理，位于命名空间 `spect
rum`。
形式化陈述：isUnit_one_sub_smul_of_lt_inv_radius {a : A} {z : 𝕜} (h : ↑‖z‖₊ < (spectra
lRadius 𝕜 a)⁻¹) : IsUnit (1 - z • a)
参数：h : ↑‖z‖₊ < (spectralRadius 𝕜 a)⁻¹。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `spectrum.mem_resolventSet_iff`：mem_resolventSet_iff {r : R} {a : A} : r 
in resolventSet R a ↔ IsUnit (↑ₐ r - a)
· 使用定理 `spectrum.mem_resolventSet_of_spectralRadius_lt`：mem_resolventSet_of_spec
tralRadius_lt {a : A} {k : 𝕜} (h : spectralRadius 𝕜 a < ‖k‖₊) : k in ρ a
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `nnnorm_inv`：nnnorm_inv (a : α) : ‖a⁻¹‖₊ = ‖a‖₊⁻¹
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nnnorm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 
‖a‖₊ ≠ 0 ↔ a ≠ 0
· 使用定理 `Units.val_mk0`：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
· 使用定理 `ENNReal.lt_inv_iff_lt_inv`：lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `IsUnit.smul_sub_iff_sub_inv_smul`：IsUnit.smul_sub_iff_sub_inv_smul [Grou
p G] [Monoid R] [AddGroup R] [DistribMulAction G R] [IsScalarTower G R R] [SMulC
ommClass G R R] (r : G…
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem isUnit_one_sub_smul_of_lt_inv_radius {a : A} {z : 𝕜} (h : ↑‖z‖₊ < (spectralRadius 𝕜 a)⁻¹) :
    IsUnit (1 - z • a) := by
  by_cases hz : z = 0
  · simp only [hz, isUnit_one, sub_zero, zero_smul]
  · let u := Units.mk0 z hz
    suffices hu : IsUnit (u⁻¹ • (1 : A) - a) by
      rwa [IsUnit.smul_sub_iff_sub_inv_smul, inv_inv u] at hu
    rw [Units.smul_def, ← Algebra.algebraMap_eq_smul_one, ← mem_resolventSet_iff]
    refine mem_resolventSet_of_spectralRadius_lt ?_
    rwa [Units.val_inv_eq_inv_val, nnnorm_inv,
      coe_inv (nnnorm_ne_zero_iff.mpr (Units.val_mk0 hz ▸ hz : (u : 𝕜) ≠ 0)), lt_inv_iff_lt_inv]

end OneSubSMul


section ExpMapping

local notation "↑ₐ" => algebraMap 𝕜 A

/-- For `𝕜 = ℝ` or `𝕜 = ℂ`, `exp` maps the spectrum of `a` into the spectrum of `exp a`. -/
/-
**spectrum.exp_mem_exp** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：exp_mem_exp [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A
] (a : A) {z : 𝕜} (hz : z in spectrum 𝕜 a) : exp z in spectrum 𝕜 (exp a)
参数：a : A；hz : z in spectrum 𝕜 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.algebraMap_exp_comm`：algebraMap_exp_comm [CompleteSpace 𝕂] (
x : 𝕂) : algebraMap 𝕂 𝔸 (exp x) = exp (algebraMap 𝕂 𝔸 x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.exp_add_of_commute`：exp_add_of_commute {x y : 𝔸} (hxy : Comm
ute x y) : exp (x + y) = exp x * exp y
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Summable.of_norm_bounded_eventually`：Summable.of_norm_bounded_eventually
 {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i in cofinite, ‖f i
‖ <= g i) : Summable f
· 使用定理 `Real.summable_pow_div_factorial`：Real.summable_pow_div_factorial (x : Re
al) : Summable (fun n => x ^ n / n ! : Nat -> Real)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_cofinite_ne`：eventually_cofinite_ne (x : α) : forallᶠ 
a in cofinite, a != x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `RCLike.norm_natCast`：norm_natCast (n : Nat) : ‖(n : K)‖ = n
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `div_le_div₀`：div_le_div₀ (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb 
: d <= b) : a / b <= c / d
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
For `𝕜 = ℝ` or `𝕜 = ℂ`, `exp` maps the spectrum of `a` into the spectrum of `exp
 a`.
-/
theorem exp_mem_exp [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]
    (a : A) {z : 𝕜} (hz : z ∈ spectrum 𝕜 a) : exp z ∈ spectrum 𝕜 (exp a) := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ 𝕜 A
  have hexpmul : exp a = exp (a - ↑ₐ z) * ↑ₐ (exp z) := by
    rw [algebraMap_exp_comm z, ← exp_add_of_commute (Algebra.commutes z (a - ↑ₐ z)).symm,
      sub_add_cancel]
  let b := ∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n
  have hb : Summable fun n : ℕ => ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ n := by
    refine .of_norm_bounded_eventually (Real.summable_pow_div_factorial ‖a - ↑ₐ z‖) ?_
    filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    rw [norm_smul, mul_comm, norm_inv, RCLike.norm_natCast, ← div_eq_mul_inv]
    gcongr
    · exact norm_pow_le' _ (pos_iff_ne_zero.mpr hn)
    · exact n.le_succ
  have h₀ : (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = (a - ↑ₐ z) * b := by
    simpa only [mul_smul_comm, pow_succ'] using hb.tsum_mul_left (a - ↑ₐ z)
  have h₁ : (∑' n : ℕ, ((n + 1).factorial⁻¹ : 𝕜) • (a - ↑ₐ z) ^ (n + 1)) = b * (a - ↑ₐ z) := by
    simpa only [pow_succ, Algebra.smul_mul_assoc] using hb.tsum_mul_right (a - ↑ₐ z)
  have h₃ : exp (a - ↑ₐ z) = 1 + (a - ↑ₐ z) * b := by
    rw [exp_eq_tsum 𝕜]
    convert! (expSeries_summable' (𝕂 := 𝕜) (a - ↑ₐ z)).tsum_eq_zero_add
    · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul]
    · exact h₀.symm
  rw [spectrum.mem_iff, IsUnit.sub_iff, ← one_mul (↑ₐ (exp z)), hexpmul, ← _root_.sub_mul,
    Commute.isUnit_mul_iff (Algebra.commutes (exp z) (exp (a - ↑ₐ z) - 1)).symm,
    sub_eq_iff_eq_add'.mpr h₃, Commute.isUnit_mul_iff (h₀ ▸ h₁ : (a - ↑ₐ z) * b = b * (a - ↑ₐ z))]
  exact not_and_of_not_left _ (not_and_of_not_left _ ((not_iff_not.mpr IsUnit.sub_iff).mp hz))

end ExpMapping

end spectrum

namespace AlgHom

section NormedField

variable {F : Type*} [NormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A

/-
**AlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜] :
    ContinuousLinearMapClass F 𝕜 A 𝕜 :=
  { AlgHomClass.linearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ ‖(1 : A)‖ fun a =>
        mul_comm ‖a‖ ‖(1 : A)‖ ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ _) }

/-- An algebra homomorphism into the base field, as a continuous linear map (since it is
automatically bounded). -/
/-
**AlgHom.toContinuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：toContinuousLinearMap (φ : A ->ₐ[𝕜] 𝕜) : StrongDual 𝕜 A
参数：φ : A ->ₐ[𝕜] 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra homomorphism into the base field, as a continuous linear map (since i
t is
automatically bounded).
-/
def toContinuousLinearMap (φ : A →ₐ[𝕜] 𝕜) : StrongDual 𝕜 A :=
  { φ.toLinearMap with }

@[simp]
/-
**AlgHom.coe_toContinuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_toContinuousLinearMap (φ : A ->ₐ[𝕜] 𝕜) : ⇑φ.toContinuousLinearMap = φ
参数：φ : A ->ₐ[𝕜] 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toContinuousLinearMap (φ : A →ₐ[𝕜] 𝕜) : ⇑φ.toContinuousLinearMap = φ :=
  rfl
/-
**AlgHom.norm_apply_le_self_mul_norm_one** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：norm_apply_le_self_mul_norm_one [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜] (f :
 F) (a : A) : ‖f a‖ <= ‖a‖ * ‖(1 : A)‖
参数：f : F；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.norm_le_norm_mul_of_mem`：norm_le_norm_mul_of_mem {a : A} {k : 𝕜
} (hk : k in σ a) : ‖k‖ <= ‖a‖ * ‖(1 : A)‖
· 使用定理 `AlgHom.apply_mem_spectrum`：apply_mem_spectrum [Nontrivial R] (φ : F) (a 
: A) : φ a in σ a
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem norm_apply_le_self_mul_norm_one [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜] (f : F) (a : A) :
    ‖f a‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum f _)
/-
**AlgHom.norm_apply_le_self** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：norm_apply_le_self [NormOneClass A] [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜] 
(f : F) (a : A) : ‖f a‖ <= ‖a‖
参数：f : F；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.norm_le_norm_of_mem`：norm_le_norm_of_mem [NormOneClass A] {a : 
A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖
· 使用定理 `AlgHom.apply_mem_spectrum`：apply_mem_spectrum [Nontrivial R] (φ : F) (a 
: A) : φ a in σ a
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
theorem norm_apply_le_self [NormOneClass A] [FunLike F A 𝕜] [AlgHomClass F 𝕜 A 𝕜]
    (f : F) (a : A) : ‖f a‖ ≤ ‖a‖ :=
  spectrum.norm_le_norm_of_mem (apply_mem_spectrum f _)

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

local notation "↑ₐ" => algebraMap 𝕜 A

@[simp]
/-
**AlgHom.toContinuousLinearMap_norm** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toContinuousLinearMap_norm [NormOneClass A] (φ : A ->ₐ[𝕜] 𝕜) : ‖φ.toContin
uousLinearMap‖ = 1
参数：φ : A ->ₐ[𝕜] 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.opNorm_eq_of_bounds`：opNorm_eq_of_bounds {φ : E ->SL
[σ₁₂] F} {M : Real} (M_nonneg : 0 <= M) (h_above : forall x, ‖φ x‖ <= M * ‖x‖) (
h_below : forall N >= 0, (for…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `spectrum.norm_le_norm_of_mem`：norm_le_norm_of_mem [NormOneClass A] {a : 
A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖
· 使用定理 `AlgHom.apply_mem_spectrum`：apply_mem_spectrum [Nontrivial R] (φ : F) (a 
: A) : φ a in σ a
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem toContinuousLinearMap_norm [NormOneClass A] (φ : A →ₐ[𝕜] 𝕜) :
    ‖φ.toContinuousLinearMap‖ = 1 :=
  ContinuousLinearMap.opNorm_eq_of_bounds zero_le_one
    (fun a => (one_mul ‖a‖).symm ▸ spectrum.norm_le_norm_of_mem (apply_mem_spectrum φ _))
    fun _ _ h => by simpa only [coe_toContinuousLinearMap, map_one, norm_one, mul_one] using h 1

end NontriviallyNormedField

end AlgHom

namespace WeakDual

namespace CharacterSpace

variable [NontriviallyNormedField 𝕜] [NormedRing A] [CompleteSpace A]
variable [NormedAlgebra 𝕜 A]

/-- The equivalence between characters and algebra homomorphisms into the base field. -/
/-
**WeakDual.CharacterSpace.equivAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual.Charac
terSpace`。
形式化陈述：equivAlgHom : characterSpace 𝕜 A ≃ (A ->ₐ[𝕜] 𝕜) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between characters and algebra homomorphisms into the base field
.
-/
noncomputable def equivAlgHom : characterSpace 𝕜 A ≃ (A →ₐ[𝕜] 𝕜) where
  toFun := toAlgHom
  invFun f :=
    { val := f.toContinuousLinearMap
      property := by rw [eq_set_map_one_map_mul]; exact ⟨map_one f, map_mul f⟩ }

@[simp]
/-
**WeakDual.CharacterSpace.equivAlgHom_coe** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual.Ch
aracterSpace`。
形式化陈述：equivAlgHom_coe (f : characterSpace 𝕜 A) : ⇑(equivAlgHom f) = f
参数：f : characterSpace 𝕜 A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
theorem equivAlgHom_coe (f : characterSpace 𝕜 A) : ⇑(equivAlgHom f) = f :=
  rfl

@[simp]
/-
**WeakDual.CharacterSpace.equivAlgHom_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `WeakDu
al.CharacterSpace`。
形式化陈述：equivAlgHom_symm_coe (f : A ->ₐ[𝕜] 𝕜) : ⇑(equivAlgHom.symm f) = f
参数：f : A ->ₐ[𝕜] 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem equivAlgHom_symm_coe (f : A →ₐ[𝕜] 𝕜) : ⇑(equivAlgHom.symm f) = f :=
  rfl

end CharacterSpace

end WeakDual

section BoundarySpectrum

local notation "σ" => spectrum

variable {𝕜 A SA : Type*} [NormedRing A] [CompleteSpace A] [SetLike SA A] [SubringClass SA A]

open Topology Filter Set

section NormedField

variable [NormedField 𝕜] [NormedAlgebra 𝕜 A] [instSMulMem : SMulMemClass SA 𝕜 A]
variable (S : SA) [hS : IsClosed (S : Set A)] (x : S)

set_option backward.isDefEq.respectTransparency.types false in
open SubalgebraClass in
include instSMulMem in
/-- Let `S` be a closed subalgebra of a Banach algebra `A`. If `a : S` is invertible in `A`,
and for all `x : S` sufficiently close to `a` within some filter `l`, `x` is invertible in `S`,
then `a` is invertible in `S` as well. -/
/-
**_root_.Subalgebra.isUnit_of_isUnit_val_of_eventually** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：_root_.Subalgebra.isUnit_of_isUnit_val_of_eventually {l : Filter S} {a : S
} (ha : IsUnit (a : A)) (hla : l <= 𝓝 a) (hl : forallᶠ x in l, IsUnit x) (hl' : 
l.NeBot) : IsUnit a
参数：ha : IsUnit (a : A)；hla : l <= 𝓝 a；hl : forallᶠ x in l, IsUnit x；hl' : l.NeBo
t。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `S` be a closed subalgebra of a Banach algebra `A`. If `a : S` is invertible
 in `A`,
and for all `x : S` sufficiently close to `a` within some filter `l`, `x` is inv
ertible in `S`,
then `a` is invertible in `S` as well.
-/
lemma _root_.Subalgebra.isUnit_of_isUnit_val_of_eventually {l : Filter S} {a : S}
    (ha : IsUnit (a : A)) (hla : l ≤ 𝓝 a) (hl : ∀ᶠ x in l, IsUnit x) (hl' : l.NeBot) :
    IsUnit a := by
  have hla₂ : Tendsto Ring.inverse (map (val S) l) (𝓝 (↑ha.unit⁻¹ : A)) := by
    rw [← Ring.inverse_unit]
    exact (NormedRing.inverse_continuousAt _).tendsto.comp <|
      continuousAt_subtype_val.tendsto.comp <| map_mono hla
  suffices mem : (↑ha.unit⁻¹ : A) ∈ S by
    refine ⟨⟨a, ⟨(↑ha.unit⁻¹ : A), mem⟩, ?_, ?_⟩, rfl⟩
    all_goals ext; simp
  apply hS.mem_of_tendsto hla₂
  rw [Filter.eventually_map]
  apply hl.mono fun x hx ↦ ?_
  suffices Ring.inverse (val S x) = (val S ↑hx.unit⁻¹) from this ▸ Subtype.property _
  rw [← (hx.map (val S)).unit_spec, Ring.inverse_unit (hx.map (val S)).unit, val]
  apply Units.mul_eq_one_iff_inv_eq.mp
  simpa [-IsUnit.mul_val_inv] using congr(($hx.mul_val_inv : A))

/-- If `S : Subalgebra 𝕜 A` is a closed subalgebra of a Banach algebra `A`, then for any
`x : S`, the boundary of the spectrum of `x` relative to `S` is a subset of the spectrum of
`↑x : A` relative to `A`. -/
/-
**_root_.Subalgebra.frontier_spectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：_root_.Subalgebra.frontier_spectrum : frontier (σ 𝕜 x) subseteq σ 𝕜 (x : A
)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S : Subalgebra 𝕜 A` is a closed subalgebra of a Banach algebra `A`, then for
 any
`x : S`, the boundary of the spectrum of `x` relative to `S` is a subset of the 
spectrum of
`↑x : A` relative to `A`.
-/
lemma _root_.Subalgebra.frontier_spectrum : frontier (σ 𝕜 x) ⊆ σ 𝕜 (x : A) := by
  have : CompleteSpace S := hS.completeSpace_coe
  intro μ hμ
  by_contra h
  rw [spectrum.notMem_iff] at h
  rw [← frontier_compl, (spectrum.isClosed _).isOpen_compl.frontier_eq, Set.mem_sdiff] at hμ
  obtain ⟨hμ₁, hμ₂⟩ := hμ
  rw [mem_closure_iff_clusterPt] at hμ₁
  apply hμ₂
  rw [mem_compl_iff, spectrum.notMem_iff]
  refine Subalgebra.isUnit_of_isUnit_val_of_eventually S h ?_ ?_ <| .map hμ₁ (algebraMap 𝕜 S · - x)
  · calc
      _ ≤ map _ (𝓝 μ) := map_mono (by simp)
      _ ≤ _ := by rw [← Filter.Tendsto, ← ContinuousAt]; fun_prop
  · rw [eventually_map]
    apply Eventually.filter_mono inf_le_right
    simp [spectrum.notMem_iff]

/-- If `S` is a closed subalgebra of a Banach algebra `A`, then for any `x : S`, the boundary of
the spectrum of `x` relative to `S` is a subset of the boundary of the spectrum of `↑x : A`
relative to `A`. -/
/-
**Subalgebra.frontier_subset_frontier** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subalgebra.frontier_subset_frontier : frontier (σ 𝕜 x) subseteq frontier (
σ 𝕜 (x : A))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `frontier_eq_closure_inter_closure`：frontier_eq_closure_inter_closure : f
rontier s = closure s inter closure sᶜ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `spectrum.isClosed`：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 𝕜
] [inst_1 : NormedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] (a : 
A), IsC…
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Subalgebra.frontier_spectrum`：∀ {𝕜 : Type u_3} {A : Type u_4} {SA : Type
 u_5} [inst : NormedRing A] [CompleteSpace A] [inst_2 : SetLike SA A]   [inst_3 
: SubringClass SA …
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `compl_le_compl`：compl_le_compl (h : a <= b) : bᶜ <= aᶜ
· 使用定理 `spectrum.subset_subalgebra`：subset_subalgebra {S R A : Type*} [CommSemir
ing R] [Ring A] [Algebra R A] [SetLike S A] [SubringClass S A] [SMulMemClass S R
 A] {s : S} (a :…

--- 原说明 ---
If `S` is a closed subalgebra of a Banach algebra `A`, then for any `x : S`, the
 boundary of
the spectrum of `x` relative to `S` is a subset of the boundary of the spectrum 
of `↑x : A`
relative to `A`.
-/
lemma Subalgebra.frontier_subset_frontier :
    frontier (σ 𝕜 x) ⊆ frontier (σ 𝕜 (x : A)) := by
  rw [frontier_eq_closure_inter_closure (s := σ 𝕜 (x : A)),
    (spectrum.isClosed (x : A)).closure_eq]
  apply subset_inter (frontier_spectrum S x)
  rw [frontier_eq_closure_inter_closure]
  grw [inter_subset_right, spectrum.subset_subalgebra]

open Set Notation

/-- If `S` is a closed subalgebra of a Banach algebra `A`, then for any `x : S`, the spectrum of `x`
is the spectrum of `↑x : A` along with the connected components of the complement of the spectrum of
`↑x : A` which contain an element of the spectrum of `x : S`. -/
/-
**Subalgebra.spectrum_sUnion_connectedComponentIn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subalgebra.spectrum_sUnion_connectedComponentIn : σ 𝕜 x = σ 𝕜 (x : A) unio
n (⋃ z in (σ 𝕜 x \ σ 𝕜 (x : A)), connectedComponentIn (σ 𝕜 (x : A))ᶜ z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `spectrum.isClosed`：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : NormedField 𝕜
] [inst_1 : NormedRing A] [inst_2 : NormedAlgebra 𝕜 A]   [CompleteSpace A] (a : 
A), IsC…
· 使用定理 `closure_eq_interior_union_frontier`：closure_eq_interior_union_frontier (
s : Set X) : closure s = interior s union frontier s
· 使用定理 `Set.union_sdiff_distrib`：union_sdiff_distrib {s t u : Set α} : (s union 
t) \ u = s \ u union t \ u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.sdiff_eq_empty`：sdiff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s subsete
q t
· 使用定理 `Subalgebra.frontier_spectrum`：∀ {𝕜 : Type u_3} {A : Type u_4} {SA : Type
 u_5} [inst : NormedRing A] [CompleteSpace A] [inst_2 : SetLike SA A]   [inst_3 
: SubringClass SA …
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用引理 `isClopen_preimage_val`：isClopen_preimage_val {X : Type*} [TopologicalSpa
ce X] {u v : Set X} (hu : IsOpen u) (huv : Disjoint (frontier u) v) : IsClopen (
v ↓inter u)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `frontier_inter_subset`：frontier_inter_subset (s t : Set X) : frontier (s
 inter t) subseteq frontier s inter closure t union closure s inter frontier t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `frontier_compl`：frontier_compl (s : Set X) : frontier sᶜ = frontier s
· 使用引理 `Subalgebra.frontier_subset_frontier`：Subalgebra.frontier_subset_frontier
 : frontier (σ 𝕜 x) subseteq frontier (σ 𝕜 (x : A))
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `Disjoint.frontier_left`：Disjoint.frontier_left (ht : IsOpen t) (hd : Dis
joint s t) : Disjoint (frontier s) t
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用引理 `IsClopen.biUnion_connectedComponentIn`：IsClopen.biUnion_connectedCompone
ntIn {X : Type*} [TopologicalSpace X] {u v : Set X} (hu : IsClopen (v ↓inter u))
 (huv₁ : u subseteq v) : u …
· 使用定理 `Set.sdiff_subset_compl`：sdiff_subset_compl (s t : Set α) : s \ t subsete
q tᶜ
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `S` is a closed subalgebra of a Banach algebra `A`, then for any `x : S`, the
 spectrum of `x`
is the spectrum of `↑x : A` along with the connected components of the complemen
t of the spectrum of
`↑x : A` which contain an element of the spectrum of `x : S`.
-/
lemma Subalgebra.spectrum_sUnion_connectedComponentIn :
    σ 𝕜 x = σ 𝕜 (x : A) ∪ (⋃ z ∈ (σ 𝕜 x \ σ 𝕜 (x : A)), connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  suffices IsClopen ((σ 𝕜 (x : A))ᶜ ↓∩ (σ 𝕜 x \ σ 𝕜 (x : A))) by
    rw [← this.biUnion_connectedComponentIn (sdiff_subset_compl _ _),
      union_sdiff_cancel (spectrum.subset_subalgebra x)]
  have : CompleteSpace S := hS.completeSpace_coe
  have h_open : IsOpen (σ 𝕜 x \ σ 𝕜 (x : A)) := by
    rw [← (spectrum.isClosed (𝕜 := 𝕜) x).closure_eq, closure_eq_interior_union_frontier,
      union_sdiff_distrib, sdiff_eq_empty.mpr (frontier_spectrum S x),
      sdiff_eq_compl_inter, union_empty]
    exact (spectrum.isClosed _).isOpen_compl.inter isOpen_interior
  apply isClopen_preimage_val h_open
  suffices h_frontier : frontier (σ 𝕜 x \ σ 𝕜 (x : A)) ⊆ frontier (σ 𝕜 (x : A)) from
    disjoint_of_subset_left h_frontier <| disjoint_compl_right.frontier_left
      (spectrum.isClosed _).isOpen_compl
  grw [sdiff_eq_compl_inter, frontier_inter_subset, inter_subset_left, inter_subset_right,
    frontier_compl, frontier_subset_frontier, union_self]

/-- Let `S` be a closed subalgebra of a Banach algebra `A`, and let `x : S`. If `z` is in the
spectrum of `x`, then the connected component of `z` in the complement of the spectrum of `↑x : A`
is bounded (or else `z` actually belongs to the spectrum of `↑x : A`). -/
/-
**Subalgebra.spectrum_isBounded_connectedComponentIn** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：Subalgebra.spectrum_isBounded_connectedComponentIn {z : 𝕜} (hz : z in σ 𝕜 
x) : Bornology.IsBounded (connectedComponentIn (σ 𝕜 (x : A))ᶜ z)
参数：hz : z in σ 𝕜 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `connectedComponentIn_eq_empty`：connectedComponentIn_eq_empty {F : Set α}
 {x : α} (h : x ∉ F) : connectedComponentIn F x = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用引理 `Subalgebra.spectrum_sUnion_connectedComponentIn`：Subalgebra.spectrum_sUn
ion_connectedComponentIn : σ 𝕜 x = σ 𝕜 (x : A) union (⋃ z in (σ 𝕜 x \ σ 𝕜 (x : A
)), connectedComponentIn (σ 𝕜 (x : A)…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_biUnion_of_mem`：subset_biUnion_of_mem {s : Set α} {u : α -> S
et β} {x : α} (xs : x in s) : u x subseteq ⋃ x in s, u x
· 使用定理 `Set.mem_sdiff_of_mem`：mem_sdiff_of_mem {s t : Set α} {x : α} (h1 : x in 
s) (h2 : x ∉ t) : x in s \ t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `spectrum.isBounded`：isBounded (a : A) : Bornology.IsBounded (σ a)

--- 原说明 ---
Let `S` be a closed subalgebra of a Banach algebra `A`, and let `x : S`. If `z` 
is in the
spectrum of `x`, then the connected component of `z` in the complement of the sp
ectrum of `↑x : A`
is bounded (or else `z` actually belongs to the spectrum of `↑x : A`).
-/
lemma Subalgebra.spectrum_isBounded_connectedComponentIn {z : 𝕜} (hz : z ∈ σ 𝕜 x) :
    Bornology.IsBounded (connectedComponentIn (σ 𝕜 (x : A))ᶜ z) := by
  by_cases hz' : z ∈ σ 𝕜 (x : A)
  · simp [connectedComponentIn_eq_empty (show z ∉ (σ 𝕜 (x : A))ᶜ from not_not.mpr hz')]
  · have : CompleteSpace S := hS.completeSpace_coe
    suffices connectedComponentIn (σ 𝕜 (x : A))ᶜ z ⊆ σ 𝕜 x from spectrum.isBounded x |>.subset this
    rw [spectrum_sUnion_connectedComponentIn S]
    exact subset_biUnion_of_mem (mem_sdiff_of_mem hz hz') |>.trans subset_union_right

end NormedField

variable [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 A] [SMulMemClass SA 𝕜 A]
variable (S : SA) [hS : IsClosed (S : Set A)] (x : S)

/-- Let `S` be a closed subalgebra of a Banach algebra `A`. If for `x : S` the complement of the
spectrum of `↑x : A` is connected, then `spectrum 𝕜 x = spectrum 𝕜 (x : A)`. -/
/-
**Subalgebra.spectrum_eq_of_isPreconnected_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Subalgebra.spectrum_eq_of_isPreconnected_compl (h : IsPreconnected (σ 𝕜 (x
 : A))ᶜ) : σ 𝕜 x = σ 𝕜 (x : A)
参数：h : IsPreconnected (σ 𝕜 (x : A))ᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `NormedSpace.unbounded_univ`：∀ (𝕜 : Type u_1) (E : Type u_3) [inst : Nont
riviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E] [NormedSpace 𝕜 E]   [Nont
rivial E], ¬Born…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Bornology.IsBounded.union`：∀ {α : Type u_2} {x : Bornology α} {s t : Set
 α},   Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s ∪ 
t)
· 使用定理 `spectrum.isBounded`：isBounded (a : A) : Bornology.IsBounded (σ a)
· 使用引理 `Subalgebra.spectrum_isBounded_connectedComponentIn`：Subalgebra.spectrum_
isBounded_connectedComponentIn {z : 𝕜} (hz : z in σ 𝕜 x) : Bornology.IsBounded (
connectedComponentIn (σ 𝕜 (x : A))ᶜ z)
· 使用定理 `IsPreconnected.connectedComponentIn`：IsPreconnected.connectedComponentIn
 {x : α} {F : Set α} (h : IsPreconnected F) (hx : x in F) : connectedComponentIn
 F x = F
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用引理 `Subalgebra.spectrum_sUnion_connectedComponentIn`：Subalgebra.spectrum_sUn
ion_connectedComponentIn : σ 𝕜 x = σ 𝕜 (x : A) union (⋃ z in (σ 𝕜 x \ σ 𝕜 (x : A
)), connectedComponentIn (σ 𝕜 (x : A)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Let `S` be a closed subalgebra of a Banach algebra `A`. If for `x : S` the compl
ement of the
spectrum of `↑x : A` is connected, then `spectrum 𝕜 x = spectrum 𝕜 (x : A)`.
-/
lemma Subalgebra.spectrum_eq_of_isPreconnected_compl (h : IsPreconnected (σ 𝕜 (x : A))ᶜ) :
    σ 𝕜 x = σ 𝕜 (x : A) := by
  suffices σ 𝕜 x \ σ 𝕜 (x : A) = ∅ by
    rw [spectrum_sUnion_connectedComponentIn, this]
    simp
  refine eq_empty_of_forall_notMem fun z hz ↦ NormedSpace.unbounded_univ 𝕜 𝕜 ?_
  obtain ⟨hz, hz'⟩ := mem_sdiff _ |>.mp hz
  have := (spectrum.isBounded (x : A)).union <|
    h.connectedComponentIn hz' ▸ spectrum_isBounded_connectedComponentIn S x hz
  simpa

end BoundarySpectrum

namespace SpectrumRestricts

open NNReal ENNReal

/-- If `𝕜₁` is a normed field contained as subfield of a larger normed field `𝕜₂`, and if `a : A`
is an element whose `𝕜₂` spectrum restricts to `𝕜₁`, then the spectral radii over each scalar
field coincide. -/
/-
**SpectrumRestricts.spectralRadius_eq** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestric
ts`。
形式化陈述：spectralRadius_eq {𝕜₁ 𝕜₂ A : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂] [Nor
medRing A] [NormedAlgebra 𝕜₁ A] [NormedAlgebra 𝕜₂ A] [NormedAlgebra 𝕜₁ 𝕜₂] [IsSc
alarTower 𝕜₁ 𝕜₂ A] {f : 𝕜₂ -> 𝕜₁} {a : A} (h : SpectrumRestricts a f) : spectral
Radius 𝕜₁ a = spectralRadius 𝕜₂ a
参数：h : SpectrumRestricts a f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectralRadius.eq_1`：∀ (𝕜 : Type u_1) {A : Type u_2} [inst : NormedField
 𝕜] [inst_1 : Ring A] [inst_2 : Algebra 𝕜 A] (a : A),   spectralRadius 𝕜 a = ⨆ k
 ∈ spectr…
· 使用定理 `Isometry.nnnorm_map_of_map_zero`：∀ {E : Type u_2} {F : Type u_3} [inst :
 SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F] {f : E → F},   Isometry f
 → f 0 = 0 → ∀ (x : E…
· 使用定理 `algebraMap_isometry`：algebraMap_isometry [NormOneClass 𝕜'] : Isometry (a
lgebraMap 𝕜 𝕜')
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `spectrum.algebraMap_mem_iff`：algebraMap_mem_iff (S : Type*) {R A : Type*
} [CommSemiring R] [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Algebr
a S A] [IsScalarT…
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a

--- 原说明 ---
If `𝕜₁` is a normed field contained as subfield of a larger normed field `𝕜₂`, a
nd if `a : A`
is an element whose `𝕜₂` spectrum restricts to `𝕜₁`, then the spectral radii ove
r each scalar
field coincide.
-/
lemma spectralRadius_eq {𝕜₁ 𝕜₂ A : Type*} [NormedField 𝕜₁] [NormedField 𝕜₂]
    [NormedRing A] [NormedAlgebra 𝕜₁ A] [NormedAlgebra 𝕜₂ A] [NormedAlgebra 𝕜₁ 𝕜₂]
    [IsScalarTower 𝕜₁ 𝕜₂ A] {f : 𝕜₂ → 𝕜₁} {a : A} (h : SpectrumRestricts a f) :
    spectralRadius 𝕜₁ a = spectralRadius 𝕜₂ a := by
  rw [spectralRadius, spectralRadius]
  have := algebraMap_isometry 𝕜₁ 𝕜₂ |>.nnnorm_map_of_map_zero (map_zero _)
  apply le_antisymm
  all_goals apply iSup₂_le fun x hx ↦ ?_
  · refine congr_arg ((↑) : ℝ≥0 → ℝ≥0∞) (this x) |>.symm.trans_le <| le_iSup₂ (α := ℝ≥0∞) _ ?_
    exact (spectrum.algebraMap_mem_iff _).mpr hx
  · have ⟨y, hy, hy'⟩ := h.algebraMap_image.symm ▸ hx
    subst hy'
    exact this y ▸ le_iSup₂ (α := ℝ≥0∞) y hy

variable {A : Type*} [Ring A]
/-
**SpectrumRestricts.nnreal_iff_spectralRadius_le** 是 Mathlib 中的一个引理，位于命名空间 `Spec
trumRestricts`。
形式化陈述：nnreal_iff_spectralRadius_le [Algebra Real A] {a : A} {t : Real>=0} (ht : 
spectralRadius Real a <= t) : SpectrumRestricts a ContinuousMap.realToNNReal ↔ s
pectralRadius Real (algebraMap Real A t - a) <= t
参数：ht : spectralRadius Real a <= t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   |a| ≤ b ↔ -b ≤ a ∧ a ≤ b
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用引理 `SpectrumRestricts.nnreal_iff`：nnreal_iff {a : A} : SpectrumRestricts a C
ontinuousMap.realToNNReal ↔ forall x in spectrum Real a, 0 <= x
· 使用定理 `iSup₂_le`：iSup₂_le {f : forall i, κ i -> α} (h : forall i j, f i j <= a)
 : ⨆ (i) (j), f i j <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.singleton_sub`：∀ {α : Type u_2} [inst : Sub α] {t : Set α} {a : α}, 
{a} - t = (fun x1 x2 => x1 - x2) a '' t
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `spectrum.singleton_sub_eq`：singleton_sub_eq (a : A) (r : R) : {r} - σ a 
= σ (↑ₐ r - a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `NNReal.coe_sub`：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NNReal.nnnorm_eq`：∀ (x : NNReal), ‖↑x‖₊ = x
· 使用定理 `ENNReal.coe_sub`：∀ {r p : NNReal}, ↑(r - p) = ↑r - ↑p
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_exists`：iSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ x, f x 
= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 61 条，此处仅展示前 30 条）
-/
lemma nnreal_iff_spectralRadius_le [Algebra ℝ A] {a : A} {t : ℝ≥0} (ht : spectralRadius ℝ a ≤ t) :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔
      spectralRadius ℝ (algebraMap ℝ A t - a) ≤ t := by
  have : spectrum ℝ a ⊆ Set.Icc (-t) t := by
    intro x hx
    rw [Set.mem_Icc, ← abs_le, ← Real.norm_eq_abs, ← coe_nnnorm, NNReal.coe_le_coe,
      ← ENNReal.coe_le_coe]
    exact le_iSup₂ (α := ℝ≥0∞) x hx |>.trans ht
  rw [nnreal_iff]
  refine ⟨fun h ↦ iSup₂_le fun x hx ↦ ?_, fun h ↦ ?_⟩
  · rw [← spectrum.singleton_sub_eq] at hx
    obtain ⟨y, hy, rfl⟩ : ∃ y ∈ spectrum ℝ a, ↑t - y = x := by simpa using hx
    obtain ⟨hty, hyt⟩ := Set.mem_Icc.mp <| this hy
    lift y to ℝ≥0 using h y hy
    rw [← NNReal.coe_sub (by exact_mod_cast hyt)]
    simp
  · replace h : ∀ x ∈ spectrum ℝ a, ‖t - x‖₊ ≤ t := by
      simpa [spectralRadius, iSup₂_le_iff, ← spectrum.singleton_sub_eq] using h
    peel h with x hx h_le
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_le] at h_le
    linarith [h_le.2]
/-
**SpectrumRestricts._root_.NNReal.spectralRadius_mem_spectrum** 是 Mathlib 中的一个引理
，位于命名空间 `SpectrumRestricts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NNReal.spectralRadius_mem_spectrum {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] {a : A} (ha : (spectrum ℝ a).Nonempty)
    (ha' : SpectrumRestricts a ContinuousMap.realToNNReal) :
    (spectralRadius ℝ a).toNNReal ∈ spectrum ℝ≥0 a := by
  obtain ⟨x, hx₁, hx₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ha
  rw [← hx₂, ENNReal.toNNReal_coe, ← spectrum.algebraMap_mem_iff ℝ, NNReal.algebraMap_eq_coe]
  have : 0 ≤ x := ha'.rightInvOn hx₁ ▸ NNReal.zero_le_coe
  convert! hx₁
  simpa
/-
**SpectrumRestricts._root_.Real.spectralRadius_mem_spectrum** 是 Mathlib 中的一个引理，位
于命名空间 `SpectrumRestricts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Real.spectralRadius_mem_spectrum {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] {a : A} (ha : (spectrum ℝ a).Nonempty)
    (ha' : SpectrumRestricts a ContinuousMap.realToNNReal) :
    (spectralRadius ℝ a).toReal ∈ spectrum ℝ a :=
  NNReal.spectralRadius_mem_spectrum ha ha'
/-
**SpectrumRestricts._root_.Real.spectralRadius_mem_spectrum_or** 是 Mathlib 中的一个引
理，位于命名空间 `SpectrumRestricts`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Real.spectralRadius_mem_spectrum_or {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] {a : A} (ha : (spectrum ℝ a).Nonempty) :
    (spectralRadius ℝ a).toReal ∈ spectrum ℝ a ∨ -(spectralRadius ℝ a).toReal ∈ spectrum ℝ a := by
  obtain ⟨x, hx₁, hx₂⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty ha
  simp only [← hx₂, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs]
  exact abs_choice x |>.imp (fun h ↦ by rwa [h]) (fun h ↦ by simpa [h])

end SpectrumRestricts

namespace QuasispectrumRestricts

open NNReal ENNReal
local notation "σₙ" => quasispectrum

/-
**QuasispectrumRestricts.compactSpace** 是 Mathlib 中的一个引理，位于命名空间 `QuasispectrumRe
stricts`。
形式化陈述：compactSpace {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Al
gebra R S] [Module R A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
 [IsScalarTower R S A] [TopologicalSpace R] [TopologicalSpace S] {a : A} (f : C(
S, R)) (h : QuasispectrumRestricts a f) [h_cpct : CompactSpace (σₙ S a)] : Compa
ctSpace (σₙ R a)
参数：f : C(S, R)；h : QuasispectrumRestricts a f；σₙ S a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `QuasispectrumRestricts.image`：image (h : QuasispectrumRestricts a f) : f
 '' quasispectrum S a = quasispectrum R a
-/
lemma compactSpace {R S A : Type*} [Semifield R] [Field S] [NonUnitalRing A]
    [Algebra R S] [Module R A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A]
    [IsScalarTower R S A] [TopologicalSpace R] [TopologicalSpace S] {a : A} (f : C(S, R))
    (h : QuasispectrumRestricts a f) [h_cpct : CompactSpace (σₙ S a)] :
    CompactSpace (σₙ R a) := by
  rw [← isCompact_iff_compactSpace] at h_cpct ⊢
  exact h.image ▸ h_cpct.image (map_continuous f)

end QuasispectrumRestricts

section UpperHemicontinuous

open Filter Set Topology

variable (𝕜 A)

/-
**upperHemicontinuous_spectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_spectrum [NormedField 𝕜] [ProperSpace 𝕜] [NormedRing A
] [NormedAlgebra 𝕜 A] [CompleteSpace A] : UpperHemicontinuous (spectrum 𝕜 : A ->
 Set 𝕜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `upperHemicontinuous_iff`：upperHemicontinuous_iff {f : α -> Set β} : Uppe
rHemicontinuous f ↔ forall x, UpperHemicontinuousAt f x
· 使用引理 `UpperHemicontinuousAt.of_sequences`：UpperHemicontinuousAt.of_sequences {
x₀ : α} [(𝓝 x₀).IsCountablyGenerated] {K : Set β} (hK : IsSeqCompact K) (hf : fo
rallᶠ x in 𝓝 x₀, f x sub…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IsCompact.isSeqCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Fi
rstCountableTopology X] {s : Set X}, IsCompact s → IsSeqCompact s
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `spectrum.subset_closedBall_norm_mul`：subset_closedBall_norm_mul (a : A) 
: σ a subseteq Metric.closedBall (0 : 𝕜) (‖a‖ * ‖(1 : A)‖)
· 使用定理 `Metric.closedBall_subset_closedBall`：closedBall_subset_closedBall (h : ε
₁ <= ε₂) : closedBall x ε₁ subseteq closedBall x ε₂
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_le_norm_add_norm_sub'`：∀ {E : Type u_5} [inst : SeminormedAddGroup 
E] (u v : E), ‖u‖ ≤ ‖v‖ + ‖u - v‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
（共 42 条，此处仅展示前 30 条）
-/
lemma upperHemicontinuous_spectrum [NormedField 𝕜] [ProperSpace 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] :
    UpperHemicontinuous (spectrum 𝕜 : A → Set 𝕜) := by
  /- It suffices to use the sequential characterization of upper hemicontinuity.
  Suppose that `a : ℕ → A` converges to `a₀`, `x : ℕ → 𝕜` converges to `x₀`, and for all `n`,
  `x n ∈ spectrum 𝕜 (a n)`. -/
  rw [upperHemicontinuous_iff]
  refine fun a₀ ↦ .of_sequences
    (isCompact_closedBall 0 ((‖a₀‖ + 1) * ‖(1 : A)‖)).isSeqCompact ?_ <|
    fun a ha x hx_mem x₀ hx ↦ ?_
  /- We must show that `spectrum 𝕜 (a n)` is eventually contained in some fixed compact set
  (we've chosen `closedBall 0 ((‖a₀‖ + 1) * ‖(1 : A)‖)`). This follows since the spectrum of any
  `b` is bounded `‖b‖ * ‖1‖` and `a` converges to `a₀`.  -/
  · filter_upwards [Metric.closedBall_mem_nhds a₀ zero_lt_one] with a ha
    apply spectrum.subset_closedBall_norm_mul a |>.trans <| Metric.closedBall_subset_closedBall ?_
    gcongr
    apply norm_le_norm_add_norm_sub' a a₀ |>.trans
    gcongr
    simpa [dist_eq_norm] using ha
  /- Finally, `x₀ ∈ spectrum 𝕜 a₀` since `algebraMap 𝕜 A x₀ - a₀` is not invertible, being itself
  the limit of the non-invertible elements `algebraMap 𝕜 A (x n) - (a n)`. -/
  · exact nonunits.isClosed.mem_of_tendsto
      (continuous_algebraMap 𝕜 A |>.tendsto x₀ |>.comp hx |>.sub ha) <| .of_forall hx_mem

/-- The map `a ↦ spectrum ℝ≥0 a` is upper hemicontinuous. -/
/-
**upperHemicontinuous_spectrum_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_spectrum_nnreal [NormedRing A] [NormedAlgebra Real A] 
[CompleteSpace A] : UpperHemicontinuous (spectrum Real>=0 : A -> Set Real>=0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.isClosedEmbedding_coe`：NNReal.isClosedEmbedding_coe : Topology.Is
ClosedEmbedding NNReal.toReal
· 使用引理 `UpperHemicontinuous.isInducing_comp`：UpperHemicontinuous.isInducing_comp
 (hf : UpperHemicontinuous f) (hi : IsInducing i) (h_cl : IsClosed (range i)) : 
UpperHemicontinuous (fun …
· 使用引理 `upperHemicontinuous_spectrum`：upperHemicontinuous_spectrum [NormedField 
𝕜] [ProperSpace 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] : UpperH
emicontinuous (spe…
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ

--- 原说明 ---
The map `a ↦ spectrum ℝ≥0 a` is upper hemicontinuous.
-/
theorem upperHemicontinuous_spectrum_nnreal [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    UpperHemicontinuous (spectrum ℝ≥0 : A → Set ℝ≥0) := by
  obtain ⟨⟨h₁, -⟩, h₂⟩ : IsClosedEmbedding ((↑) : ℝ≥0 → ℝ) := NNReal.isClosedEmbedding_coe
  exact upperHemicontinuous_spectrum ℝ A |>.isInducing_comp h₁ h₂

open WithLp in
/-- The map `a ↦ quasispectrum 𝕜 a` is upper hemicontinuous. -/
/-
**upperHemicontinuous_quasispectrum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_quasispectrum [NontriviallyNormedField 𝕜] [ProperSpace
 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTow
er 𝕜 A A] [CompleteSpace A] : UpperHemicontinuous (quasispectrum 𝕜 : A -> Set 𝕜)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr`：quasispectrum_eq_spectrum_inr
 (R : Type*) {A : Type*} [CommRing R] [NonUnitalRing A] [Module R A] [IsScalarTo
wer R A A] [SMulCommClass R A A…
· 使用定理 `AlgEquiv.spectrum_eq`：AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiri
ng R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [AlgEquivC
lass F R A…
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `UpperHemicontinuous.comp`：UpperHemicontinuous.comp (hf : UpperHemicontin
uous f) (hg : Continuous g) : UpperHemicontinuous (f ∘ g)
· 使用引理 `upperHemicontinuous_spectrum`：upperHemicontinuous_spectrum [NormedField 
𝕜] [ProperSpace 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] : UpperH
emicontinuous (spe…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用引理 `WithLp.unitization_isometry_inr`：unitization_isometry_inr : Isometry fun
 x : A => toLp 1 (x : Unitization 𝕜 A)

--- 原说明 ---
The map `a ↦ quasispectrum 𝕜 a` is upper hemicontinuous.
-/
theorem upperHemicontinuous_quasispectrum [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
    [CompleteSpace A] :
    UpperHemicontinuous (quasispectrum 𝕜 : A → Set 𝕜) := by
  convert!
    upperHemicontinuous_spectrum 𝕜 (WithLp 1 (Unitization 𝕜 A)) |>.comp
      unitization_isometry_inr.continuous
  ext1 a
  rw [Unitization.quasispectrum_eq_spectrum_inr,
    ← AlgEquiv.spectrum_eq (unitizationAlgEquiv 𝕜 (𝕜 := 𝕜) (A := A) |>.symm)]
  congr

/-- The map `a ↦ quasispectrum ℝ≥0 a` is upper hemicontinuous. -/
/-
**upperHemicontinuous_quasispectrum_nnreal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_quasispectrum_nnreal [NonUnitalNormedRing A] [NormedSp
ace Real A] [SMulCommClass Real A A] [IsScalarTower Real A A] [CompleteSpace A] 
: UpperHemicontinuous (quasispectrum Real>=0 : A -> Set Real>=0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.isClosedEmbedding_coe`：NNReal.isClosedEmbedding_coe : Topology.Is
ClosedEmbedding NNReal.toReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `quasispectrum.preimage_algebraMap`：quasispectrum.preimage_algebraMap (S 
: Type*) {R A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra R S] [
Module S A] [IsScalarTo…
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用引理 `UpperHemicontinuous.isInducing_comp`：UpperHemicontinuous.isInducing_comp
 (hf : UpperHemicontinuous f) (hi : IsInducing i) (h_cl : IsClosed (range i)) : 
UpperHemicontinuous (fun …
· 使用定理 `upperHemicontinuous_quasispectrum`：upperHemicontinuous_quasispectrum [No
ntriviallyNormedField 𝕜] [ProperSpace 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 
A] [SMulCommClass 𝕜 A A…
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ

--- 原说明 ---
The map `a ↦ quasispectrum ℝ≥0 a` is upper hemicontinuous.
-/
theorem upperHemicontinuous_quasispectrum_nnreal [NonUnitalNormedRing A]
    [NormedSpace ℝ A] [SMulCommClass ℝ A A] [IsScalarTower ℝ A A] [CompleteSpace A] :
    UpperHemicontinuous (quasispectrum ℝ≥0 : A → Set ℝ≥0) := by
  obtain ⟨⟨h₁, -⟩, h₂⟩ := NNReal.isClosedEmbedding_coe
  simpa [← NNReal.algebraMap_eq_coe] using
    upperHemicontinuous_quasispectrum ℝ A |>.isInducing_comp h₁ h₂

end UpperHemicontinuous

