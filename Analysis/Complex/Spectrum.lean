/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Analysis.Complex.Basic

/-!
# Some lemmas on the spectrum and quasispectrum of elements and positivity on `ℂ`
-/

public section

namespace SpectrumRestricts
variable {A : Type*} [Ring A]

/-
**SpectrumRestricts.real_iff** 是 Mathlib 中的一个引理，位于命名空间 `SpectrumRestricts`。
形式化陈述：real_iff [Algebra Complex A] {a : A} : SpectrumRestricts a Complex.reCLM ↔
 forall x in spectrum Complex a, x = x.re
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.LeftInvOn.eq_1`：∀ {α : Type u} {β : Type v} (g : β → α) (f : α → β) 
(s : Set α), Set.LeftInvOn g f s = ∀ ⦃x : α⦄, x ∈ s → g (f x) = x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma real_iff [Algebra ℂ A] {a : A} :
    SpectrumRestricts a Complex.reCLM ↔ ∀ x ∈ spectrum ℂ a, x = x.re := by
  simp [spectrumRestricts_iff, Set.LeftInvOn, Function.LeftInverse, eq_comm]

end SpectrumRestricts

namespace QuasispectrumRestricts
local notation "σₙ" => quasispectrum
variable {A : Type*} [NonUnitalRing A]

/-
**QuasispectrumRestricts.real_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuasispectrumRestri
cts`。
形式化陈述：real_iff [Module Complex A] [IsScalarTower Complex A A] [SMulCommClass Com
plex A A] {a : A} : QuasispectrumRestricts a Complex.reCLM ↔ forall x in σₙ Comp
lex a, x = x.re
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `quasispectrumRestricts_iff_spectrumRestricts_inr`：quasispectrumRestricts
_iff_spectrumRestricts_inr (S : Type*) {R A : Type*} [Semifield R] [Field S] [No
nUnitalRing A] [Algebra R S] [Module R…
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr'`：quasispectrum_eq_spectrum_in
r' (R S : Type*) {A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra 
R S] [Module S A] [IsScalarTower…
· 使用引理 `SpectrumRestricts.real_iff`：real_iff [Algebra Complex A] {a : A} : Spect
rumRestricts a Complex.reCLM ↔ forall x in spectrum Complex a, x = x.re
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma real_iff [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] {a : A} :
    QuasispectrumRestricts a Complex.reCLM ↔ ∀ x ∈ σₙ ℂ a, x = x.re := by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr,
    Unitization.quasispectrum_eq_spectrum_inr' _ ℂ, SpectrumRestricts.real_iff]

end QuasispectrumRestricts

