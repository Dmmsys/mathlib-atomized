/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum

/-!
# Fourier theory on `ZMod N`

Basic definitions and properties of the discrete Fourier transform for functions on `ZMod N`
(taking values in an arbitrary `ℂ`-vector space).

### Main definitions and results

* `ZMod.dft`: the Fourier transform, with respect to the standard additive character
  `ZMod.stdAddChar` (mapping `j mod N` to `exp (2 * π * I * j / N)`). The notation `𝓕`, scoped in
  namespace `ZMod`, is available for this.
* `ZMod.dft_dft`: the Fourier inversion formula.
* `DirichletCharacter.fourierTransform_eq_inv_mul_gaussSum`: the discrete Fourier transform of a
  primitive Dirichlet character `χ` is a Gauss sum times `χ⁻¹`.
-/

@[expose] public section

open MeasureTheory Finset AddChar ZMod

namespace ZMod

variable {N : ℕ} [NeZero N] {E : Type*} [AddCommGroup E] [Module ℂ E]

section private_defs
/-
It doesn't _quite_ work to define the Fourier transform as a `LinearEquiv` in one go, because that
leads to annoying repetition between the proof fields. So we set up a private definition first,
prove a minimal set of lemmas about it, and then define the `LinearEquiv` using that.

**Do not add more lemmas about `auxDFT`**: it should be invisible to end-users.
-/

set_option backward.privateInPublic true in
/--
The discrete Fourier transform on `ℤ / N ℤ` (with the counting measure). This definition is
private because it is superseded by the bundled `LinearEquiv` version.
-/
/-
**ZMod.auxDFT** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete Fourier transform on `ℤ / N ℤ` (with the counting measure). This de
finition is
private because it is superseded by the bundled `LinearEquiv` version.
-/
private noncomputable def auxDFT (Φ : ZMod N → E) (k : ZMod N) : E :=
  ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j
/-
**ZMod.auxDFT_neg** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma auxDFT_neg (Φ : ZMod N → E) : auxDFT (fun j ↦ Φ (-j)) = fun k ↦ auxDFT Φ (-k) := by
  ext1 k; simpa only [auxDFT] using
    Fintype.sum_equiv (Equiv.neg _) _ _ (fun j ↦ by rw [Equiv.neg_apply, neg_mul_neg])

/-- Fourier inversion formula, discrete case. -/
/-
**ZMod.auxDFT_auxDFT** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fourier inversion formula, discrete case.
-/
private lemma auxDFT_auxDFT (Φ : ZMod N → E) : auxDFT (auxDFT Φ) = fun j ↦ (N : ℂ) • Φ (-j) := by
  ext1 j
  simp only [auxDFT, mul_comm _ j, smul_sum, ← smul_assoc, smul_eq_mul, ← map_add_eq_mul, ←
    neg_add, ← add_mul]
  rw [sum_comm]
  simp only [← sum_smul, ← neg_mul]
  have h1 (t : ZMod N) : ∑ i, stdAddChar (t * i) = if t = 0 then ↑N else 0 := by
    split_ifs with h
    · simp only [h, zero_mul, map_zero_eq_one, sum_const, card_univ, card,
        nsmul_eq_mul, mul_one]
    · exact sum_eq_zero_of_ne_one (isPrimitive_stdAddChar N h)
  have h2 (x j : ZMod N) : -(j + x) = 0 ↔ x = -j := by
    rw [neg_add, add_comm, add_eq_zero_iff_neg_eq, neg_neg]
  simp only [h1, h2, ite_smul, zero_smul, sum_ite_eq', mem_univ, ite_true]
/-
**ZMod.auxDFT_smul** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma auxDFT_smul (c : ℂ) (Φ : ZMod N → E) :
    auxDFT (c • Φ) = c • auxDFT Φ := by
  ext; simp only [Pi.smul_def, auxDFT, smul_sum, smul_comm c]

end private_defs

section defs

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
The discrete Fourier transform on `ℤ / N ℤ` (with the counting measure), bundled as a linear
equivalence. Denoted as `𝓕` within the `ZMod` namespace.
-/
/-
**ZMod.dft** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：{N : ℕ} →   [NeZero N] → {E : Type u_1} → [inst : AddCommGroup E] → [inst_
1 : _root_.Module ℂ E] → (ZMod N → E) ≃ₗ[ℂ] ZMod N → E
参数：ZMod N → E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete Fourier transform on `ℤ / N ℤ` (with the counting measure), bundled
 as a linear
equivalence. Denoted as `𝓕` within the `ZMod` namespace.
-/
noncomputable def dft : (ZMod N → E) ≃ₗ[ℂ] (ZMod N → E) where
  toFun := auxDFT
  map_add' Φ₁ Φ₂ := by
    ext; simp only [auxDFT, Pi.add_def, smul_add, sum_add_distrib]
  map_smul' c Φ := by
    ext; simp only [auxDFT, Pi.smul_apply, RingHom.id_apply, smul_sum, smul_comm c]
  invFun Φ k := (N : ℂ)⁻¹ • auxDFT Φ (-k)
  left_inv Φ := by
    simp only [auxDFT_auxDFT, neg_neg, ← mul_smul, inv_mul_cancel₀ (NeZero.ne _), one_smul]
  right_inv Φ := by
    ext1 j
    simp only [← Pi.smul_def, auxDFT_smul, auxDFT_neg, auxDFT_auxDFT, neg_neg, ← mul_smul,
      inv_mul_cancel₀ (NeZero.ne _), one_smul]

@[inherit_doc] scoped notation "𝓕" => dft

/-- The inverse Fourier transform on `ZMod N`. -/
scoped notation "𝓕⁻" => LinearEquiv.symm dft

/-
**ZMod.dft_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] (Φ : ZMod N → E)   (k : ZMod N), ZMod.dft Φ k = ∑ j, ZMo
d.stdAddChar (-(j * k)) • Φ j
参数：Φ : ZMod N → E；k : ZMod N；-(j * k)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dft_apply (Φ : ZMod N → E) (k : ZMod N) :
    𝓕 Φ k = ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j :=
  rfl
/-
**ZMod.dft_def** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] (Φ : ZMod N → E),   ZMod.dft Φ = fun k => ∑ j, ZMod.stdA
ddChar (-(j * k)) • Φ j
参数：Φ : ZMod N → E；-(j * k)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dft_def (Φ : ZMod N → E) :
    𝓕 Φ = fun k ↦ ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j :=
  rfl
/-
**ZMod.invDFT_apply** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] (Ψ : ZMod N → E)   (k : ZMod N), ZMod.dft.symm Ψ k = (↑N
)⁻¹ • ∑ j, ZMod.stdAddChar (j * k) • Ψ j
参数：Ψ : ZMod N → E；k : ZMod N；↑N；j * k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma invDFT_apply (Ψ : ZMod N → E) (k : ZMod N) :
    𝓕⁻ Ψ k = (N : ℂ)⁻¹ • ∑ j : ZMod N, stdAddChar (j * k) • Ψ j := by
  simp only [dft, LinearEquiv.coe_symm_mk, auxDFT, mul_neg, neg_neg]
/-
**ZMod.invDFT_def** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] (Ψ : ZMod N → E),   ZMod.dft.symm Ψ = fun k => (↑N)⁻¹ • 
∑ j, ZMod.stdAddChar (j * k) • Ψ j
参数：Ψ : ZMod N → E；↑N；j * k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ZMod.invDFT_apply`：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : 
AddCommGroup E] [inst_2 : _root_.Module ℂ E] (Ψ : ZMod N → E)   (k : ZMod N), ZM
od.dft.…
-/
lemma invDFT_def (Ψ : ZMod N → E) :
    𝓕⁻ Ψ = fun k ↦ (N : ℂ)⁻¹ • ∑ j : ZMod N, stdAddChar (j * k) • Ψ j :=
  funext <| invDFT_apply Ψ
/-
**ZMod.invDFT_apply'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] (Ψ : ZMod N → E)   (k : ZMod N), ZMod.dft.symm Ψ k = (↑N
)⁻¹ • ZMod.dft Ψ (-k)
参数：Ψ : ZMod N → E；k : ZMod N；↑N；-k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma invDFT_apply' (Ψ : ZMod N → E) (k : ZMod N) : 𝓕⁻ Ψ k = (N : ℂ)⁻¹ • 𝓕 Ψ (-k) :=
  rfl
/-
**ZMod.invDFT_def'** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] (Ψ : ZMod N → E),   ZMod.dft.symm Ψ = fun k => (↑N)⁻¹ • 
ZMod.dft Ψ (-k)
参数：Ψ : ZMod N → E；↑N；-k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma invDFT_def' (Ψ : ZMod N → E) : 𝓕⁻ Ψ = fun k ↦ (N : ℂ)⁻¹ • 𝓕 Ψ (-k) :=
  rfl
/-
**ZMod.dft_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] (Φ : ZMod N → E),   ZMod.dft Φ 0 = ∑ j, Φ j
参数：Φ : ZMod N → E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dft_apply_zero (Φ : ZMod N → E) : 𝓕 Φ 0 = ∑ j, Φ j := by
  simp only [dft_apply, mul_zero, neg_zero, map_zero_eq_one, one_smul]

/--
The discrete Fourier transform agrees with the general one (assuming the target space is a complete
normed space).
-/
/-
**ZMod.dft_eq_fourier** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
 [inst_2 : NormedSpace ℂ E] [CompleteSpace E]   (Φ : ZMod N → E) (k : ZMod N), Z
Mod.dft Φ k = Fourier.fourierIntegral ZMod.toCircle MeasureTheory.Measure.count 
Φ k
参数：Φ : ZMod N → E；k : ZMod N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_countable`：integral_countable [Countable X] (hf :
 Integrable f μ) : ∫ x, f x ∂μ = ∑' x, μ.real {x} • f x
· 使用定理 `MeasureTheory.Integrable.of_finite`：∀ {α : Type u_1} {β : Type u_2} {m :
 MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β] 
  [Finite α] [Measurable…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasureTheory.Measure.count.isFiniteMeasure`：∀ {α : Type u_1} [inst : Me
asurableSpace α] [Finite α], MeasureTheory.IsFiniteMeasure MeasureTheory.Measure
.count
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.count_real_singleton`：∀ {α : Type u_1} [inst : MeasurableS
pace α] [MeasurableSingletonClass α] (a : α),   MeasureTheory.Measure.count.real
 {a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The discrete Fourier transform agrees with the general one (assuming the target 
space is a complete
normed space).
-/
lemma dft_eq_fourier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (Φ : ZMod N → E) (k : ZMod N) :
    𝓕 Φ k = Fourier.fourierIntegral toCircle Measure.count Φ k := by
  simp only [dft_apply, stdAddChar_apply, Fourier.fourierIntegral_def, Circle.smul_def,
    integral_countable <| .of_finite .., count_real_singleton, one_smul, tsum_fintype]

end defs

section arith
/-!
## Compatibility with scalar multiplication

These lemmas are more general than `LinearEquiv.map_mul` etc, since they allow any scalars that
commute with the `ℂ`-action, rather than just `ℂ` itself.
-/

/-
**ZMod.dft_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] {R : Type u_2}   [inst_3 : DistribSMul R E] [SMulCommCla
ss R ℂ E] (r : R) (Φ : ZMod N → E), ZMod.dft (r • Φ) = r • ZMod.dft Φ
参数：r : R；Φ : ZMod N → E；r • Φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
## Compatibility with scalar multiplication

These lemmas are more general than `LinearEquiv.map_mul` etc, since they allow a
ny scalars that
commute with the `ℂ`-action, rather than just `ℂ` itself.
-/
lemma dft_const_smul {R : Type*} [DistribSMul R E] [SMulCommClass R ℂ E] (r : R) (Φ : ZMod N → E) :
    𝓕 (r • Φ) = r • 𝓕 Φ := by
  simp only [Pi.smul_def, dft_def, smul_sum, smul_comm]
/-
**ZMod.dft_smul_const** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] {R : Type u_2}   [inst_3 : Ring R] [inst_4 : _root_.Modu
le ℂ R] [inst_5 : _root_.Module R E] [IsScalarTower ℂ R E] (Φ : ZMod N → R)   (e
 : E), (ZMod.dft fun j => Φ j • e) = fun k => ZMod.dft Φ k • e
参数：Φ : ZMod N → R；e : E；ZMod.dft fun j => Φ j • e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dft_smul_const {R : Type*} [Ring R] [Module ℂ R] [Module R E] [IsScalarTower ℂ R E]
    (Φ : ZMod N → R) (e : E) :
    𝓕 (fun j ↦ Φ j • e) = fun k ↦ 𝓕 Φ k • e := by
  simp only [dft_def, sum_smul, smul_assoc]
/-
**ZMod.dft_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {R : Type u_2} [inst_1 : Ring R] [inst_2 : Alg
ebra ℂ R] (r : R) (Φ : ZMod N → R),   (ZMod.dft fun j => r * Φ j) = fun k => r *
 ZMod.dft Φ k
参数：r : R；Φ : ZMod N → R；ZMod.dft fun j => r * Φ j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.dft_const_smul`：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 
: AddCommGroup E] [inst_2 : _root_.Module ℂ E] {R : Type u_2}   [inst_3 : Distri
bSMul R E…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma dft_const_mul {R : Type*} [Ring R] [Algebra ℂ R] (r : R) (Φ : ZMod N → R) :
    𝓕 (fun j ↦ r * Φ j) = fun k ↦ r * 𝓕 Φ k :=
  dft_const_smul r Φ
/-
**ZMod.dft_mul_const** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {R : Type u_2} [inst_1 : Ring R] [inst_2 : Alg
ebra ℂ R] (Φ : ZMod N → R) (r : R),   (ZMod.dft fun j => Φ j * r) = fun k => ZMo
d.dft Φ k * r
参数：Φ : ZMod N → R；r : R；ZMod.dft fun j => Φ j * r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.dft_smul_const`：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 
: AddCommGroup E] [inst_2 : _root_.Module ℂ E] {R : Type u_2}   [inst_3 : Ring R
] [inst_4…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma dft_mul_const {R : Type*} [Ring R] [Algebra ℂ R] (Φ : ZMod N → R) (r : R) :
    𝓕 (fun j ↦ Φ j * r) = fun k ↦ 𝓕 Φ k * r :=
  dft_smul_const Φ r

end arith

section inversion

/-
**ZMod.dft_comp_neg** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] (Φ : ZMod N → E),   (ZMod.dft fun j => Φ (-j)) = fun k =
> ZMod.dft Φ (-k)
参数：Φ : ZMod N → E；ZMod.dft fun j => Φ (-j)；-k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Fourier.ZMod.0.ZMod.auxDFT_neg`：∀ {N : ℕ} [ins
t : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst_2 : _root_.Module ℂ
 E] (Φ : ZMod N → E),   (ZMod.auxDFT✝ fun j =>…
-/
lemma dft_comp_neg (Φ : ZMod N → E) : 𝓕 (fun j ↦ Φ (-j)) = fun k ↦ 𝓕 Φ (-k) :=
  auxDFT_neg ..

/-- Fourier inversion formula, discrete case. -/
/-
**ZMod.dft_dft** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] (Φ : ZMod N → E),   ZMod.dft (ZMod.dft Φ) = fun j => ↑N 
• Φ (-j)
参数：Φ : ZMod N → E；ZMod.dft Φ；-j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Fourier.ZMod.0.ZMod.auxDFT_auxDFT`：∀ {N : ℕ} [
inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst_2 : _root_.Modul
e ℂ E] (Φ : ZMod N → E),   ZMod.auxDFT✝ (ZMod.aux…

--- 原说明 ---
Fourier inversion formula, discrete case.
-/
lemma dft_dft (Φ : ZMod N → E) : 𝓕 (𝓕 Φ) = fun j ↦ (N : ℂ) • Φ (-j) :=
  auxDFT_auxDFT ..

end inversion

/-
**ZMod.dft_comp_unitMul** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCommGroup E] [inst
_2 : _root_.Module ℂ E] (Φ : ZMod N → E)   (u : (ZMod N)ˣ) (k : ZMod N), ZMod.df
t (fun j => Φ (↑u * j)) k = ZMod.dft Φ (↑u⁻¹ * k)
参数：Φ : ZMod N → E；u : (ZMod N)ˣ；k : ZMod N；fun j => Φ (↑u * j)；↑u⁻¹ * k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.sum_equiv`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst 
: Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (f : 
ι → M) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Units.mulLeft_apply`：∀ {M : Type u_3} [inst : Monoid M] (u : Mˣ), ⇑u.mul
Left = fun x => ↑u * x
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dft_comp_unitMul (Φ : ZMod N → E) (u : (ZMod N)ˣ) (k : ZMod N) :
    𝓕 (fun j ↦ Φ (u.val * j)) k = 𝓕 Φ (u⁻¹.val * k) := by
  refine Fintype.sum_equiv u.mulLeft _ _ fun x ↦ ?_
  simp only [mul_comm u.val, u.mulLeft_apply, ← mul_assoc, u.mul_inv_cancel_right]

section signs

/-- The discrete Fourier transform of `Φ` is even if and only if `Φ` itself is. -/
/-
**ZMod.dft_even_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {Φ : ZMod N → ℂ}, Function.Even (ZMod.dft Φ) ↔
 Function.Even Φ
参数：ZMod.dft Φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `ZMod.dft_comp_neg`：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : 
AddCommGroup E] [inst_2 : _root_.Module ℂ E] (Φ : ZMod N → E),   (ZMod.dft fun j
 => Φ (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ZMod.dft_dft`：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCo
mmGroup E] [inst_2 : _root_.Module ℂ E] (Φ : ZMod N → E),   ZMod.dft (ZMod.dft Φ
) …
· 使用定理 `smul_right_inj`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m₁ m₂ : M} [Modul
e.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M

--- 原说明 ---
The discrete Fourier transform of `Φ` is even if and only if `Φ` itself is.
-/
lemma dft_even_iff {Φ : ZMod N → ℂ} : (𝓕 Φ).Even ↔ Φ.Even := by
  have h {f : ZMod N → ℂ} (hf : f.Even) : (𝓕 f).Even := by
    simp only [Function.Even, ← congr_fun (dft_comp_neg f), funext hf, implies_true]
  refine ⟨fun hΦ x ↦ ?_, h⟩
  simpa only [neg_neg, smul_right_inj (NeZero.ne (N : ℂ)), dft_dft] using h hΦ (-x)

/-- The discrete Fourier transform of `Φ` is odd if and only if `Φ` itself is. -/
/-
**ZMod.dft_odd_iff** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {Φ : ZMod N → ℂ}, Function.Odd (ZMod.dft Φ) ↔ 
Function.Odd Φ
参数：ZMod.dft Φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `ZMod.dft_comp_neg`：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : 
AddCommGroup E] [inst_2 : _root_.Module ℂ E] (Φ : ZMod N → E),   (ZMod.dft fun j
 => Φ (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `ZMod.dft_dft`：∀ {N : ℕ} [inst : NeZero N] {E : Type u_1} [inst_1 : AddCo
mmGroup E] [inst_2 : _root_.Module ℂ E] (Φ : ZMod N → E),   ZMod.dft (ZMod.dft Φ
) …
· 使用定理 `smul_right_inj`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m₁ m₂ : M} [Modul
e.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M

--- 原说明 ---
The discrete Fourier transform of `Φ` is odd if and only if `Φ` itself is.
-/
lemma dft_odd_iff {Φ : ZMod N → ℂ} : (𝓕 Φ).Odd ↔ Φ.Odd := by
  have h {f : ZMod N → ℂ} (hf : f.Odd) : (𝓕 f).Odd := by
    simp only [Function.Odd, ← congr_fun (dft_comp_neg f), funext hf, ← Pi.neg_apply, map_neg,
      implies_true]
  refine ⟨fun hΦ x ↦ ?_, h⟩
  simpa only [neg_neg, dft_dft, ← smul_neg, smul_right_inj (NeZero.ne (N : ℂ))] using h hΦ (-x)

end signs

end ZMod

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-
**DirichletCharacter.fourierTransform_eq_gaussSum_mulShift** 是 Mathlib 中的一个定理，位于
命名空间 `DirichletCharacter`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] (χ : DirichletCharacter ℂ N) (k : ZMod N),   Z
Mod.dft (⇑χ) k = gaussSum χ (ZMod.stdAddChar.mulShift (-k))
参数：χ : DirichletCharacter ℂ N；k : ZMod N；⇑χ；ZMod.stdAddChar.mulShift (-k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddChar.mulShift_apply`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : CommMonoid M] {ψ : AddChar R M} {r x : R},   (ψ.mulShift r) x = ψ (r *
 x)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `ZMod.stdAddChar_apply`：stdAddChar_apply (j : ZMod N) : stdAddChar j = ↑(
toCircle j)
-/
lemma fourierTransform_eq_gaussSum_mulShift (χ : DirichletCharacter ℂ N) (k : ZMod N) :
    𝓕 χ k = gaussSum χ (stdAddChar.mulShift (-k)) := by
  simp only [dft_apply, smul_eq_mul]
  congr 1 with j
  rw [mulShift_apply, mul_comm j, neg_mul, stdAddChar_apply, mul_comm (χ _)]

/-- For a primitive Dirichlet character `χ`, the Fourier transform of `χ` is a constant multiple
of `χ⁻¹` (and the constant is essentially the Gauss sum). -/
/-
**DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum** 是 Mathli
b 中的一个定理，位于命名空间 `DirichletCharacter.IsPrimitive`。
形式化陈述：∀ {N : ℕ} [inst : NeZero N] {χ : DirichletCharacter ℂ N},   χ.IsPrimitive 
→ ∀ (k : ZMod N), ZMod.dft (⇑χ) k = χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar
参数：k : ZMod N；⇑χ；-k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirichletCharacter.fourierTransform_eq_gaussSum_mulShift`：∀ {N : ℕ} [ins
t : NeZero N] (χ : DirichletCharacter ℂ N) (k : ZMod N),   ZMod.dft (⇑χ) k = gau
ssSum χ (ZMod.stdAddChar.mulShift (-k))
· 使用引理 `gaussSum_mulShift_of_isPrimitive`：gaussSum_mulShift_of_isPrimitive [IsDo
main R] {χ : DirichletCharacter R N} (hχ : IsPrimitive χ) (a : ZMod N) : gaussSu
m χ (e.mulShift a) = χ…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
For a primitive Dirichlet character `χ`, the Fourier transform of `χ` is a const
ant multiple
of `χ⁻¹` (and the constant is essentially the Gauss sum).
-/
lemma IsPrimitive.fourierTransform_eq_inv_mul_gaussSum {χ : DirichletCharacter ℂ N}
    (hχ : IsPrimitive χ) (k : ZMod N) :
    𝓕 χ k = χ⁻¹ (-k) * gaussSum χ stdAddChar := by
  rw [fourierTransform_eq_gaussSum_mulShift, gaussSum_mulShift_of_isPrimitive _ hχ]

end DirichletCharacter

