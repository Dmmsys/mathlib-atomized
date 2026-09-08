/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Finiteness.FinitePresentationLocal

/-!

# The meta properties of finitely-presented ring homomorphisms.

The main result is `RingHom.finitePresentation_isLocal`.

-/

public section

open scoped Pointwise TensorProduct

namespace RingHom

/-- Being finitely-presented is stable under composition. -/
/-
**RingHom.finitePresentation_stableUnderComposition** 是 Mathlib 中的一个定理，位于命名空间 `R
ingHom`。
形式化陈述：finitePresentation_stableUnderComposition : StableUnderComposition @Finite
Presentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FinitePresentation.comp`：comp {g : B ->+* C} {f : A ->+* B} (hg 
: g.FinitePresentation) (hf : f.FinitePresentation) : (g.comp f).FinitePresentat
ion

--- 原说明 ---
Being finitely-presented is stable under composition.
-/
theorem finitePresentation_stableUnderComposition : StableUnderComposition @FinitePresentation := by
  introv R hf hg
  exact hg.comp hf

/-- Being finitely-presented respects isomorphisms. -/
/-
**RingHom.finitePresentation_respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：finitePresentation_respectsIso : RingHom.RespectsIso @RingHom.FinitePresen
tation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用定理 `RingHom.finitePresentation_stableUnderComposition`：finitePresentation_st
ableUnderComposition : StableUnderComposition @FinitePresentation
· 使用定理 `RingHom.FinitePresentation.of_surjective`：of_surjective (f : A ->+* B) (
hf : Surjective f) (hker : (RingHom.ker f).FG) : f.FinitePresentation
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.ker_coe_equiv`：ker_coe_equiv (f : R ≃+* S) : ker (f : R ->+* S) 
= ⊥
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG

--- 原说明 ---
Being finitely-presented respects isomorphisms.
-/
theorem finitePresentation_respectsIso : RingHom.RespectsIso @RingHom.FinitePresentation :=
  finitePresentation_stableUnderComposition.respectsIso
    fun e ↦ .of_surjective _ e.surjective <| by simpa using! Submodule.fg_bot

/-- Being finitely-presented is stable under base change. -/
/-
**RingHom.finitePresentation_isStableUnderBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `
RingHom`。
形式化陈述：finitePresentation_isStableUnderBaseChange : IsStableUnderBaseChange @Fini
tePresentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用定理 `RingHom.finitePresentation_respectsIso`：finitePresentation_respectsIso :
 RingHom.RespectsIso @RingHom.FinitePresentation
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Being finitely-presented is stable under base change.
-/
theorem finitePresentation_isStableUnderBaseChange :
    IsStableUnderBaseChange @FinitePresentation := by
  apply IsStableUnderBaseChange.mk
  · exact finitePresentation_respectsIso
  · simp only [finitePresentation_algebraMap]
    intros
    infer_instance

/-- Being finitely-presented is preserved by localizations. -/
/-
**RingHom.finitePresentation_localizationPreserves** 是 Mathlib 中的一个定理，位于命名空间 `Ri
ngHom`。
形式化陈述：finitePresentation_localizationPreserves : LocalizationPreserves @FinitePr
esentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用定理 `RingHom.finitePresentation_isStableUnderBaseChange`：finitePresentation_i
sStableUnderBaseChange : IsStableUnderBaseChange @FinitePresentation

--- 原说明 ---
Being finitely-presented is preserved by localizations.
-/
theorem finitePresentation_localizationPreserves : LocalizationPreserves @FinitePresentation :=
  finitePresentation_isStableUnderBaseChange.localizationPreserves

/-- If `R` is a ring, then `Rᵣ` is `R`-finitely-presented for any `r : R`. -/
/-
**RingHom.finitePresentation_holdsForLocalizationAway** 是 Mathlib 中的一个定理，位于命名空间 
`RingHom`。
形式化陈述：finitePresentation_holdsForLocalizationAway : HoldsForLocalizationAway @Fi
nitePresentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.finitePresentation_algebraMap`：finitePresentation_algebraMap [Al
gebra A B] : (algebraMap A B).FinitePresentation ↔ Algebra.FinitePresentation A 
B
· 使用定理 `IsLocalization.Away.finitePresentation`：IsLocalization.Away.finitePresen
tation (r : R) {S} [CommRing S] [Algebra R S] [IsLocalization.Away r S] : Algebr
a.FinitePresentation R S

--- 原说明 ---
If `R` is a ring, then `Rᵣ` is `R`-finitely-presented for any `r : R`.
-/
theorem finitePresentation_holdsForLocalizationAway :
    HoldsForLocalizationAway @FinitePresentation := by
  introv R _
  rw [finitePresentation_algebraMap]
  exact IsLocalization.Away.finitePresentation r

/-- Finite-presentation can be checked on a standard covering of the target. -/
/-
**RingHom.finitePresentation_ofLocalizationSpanTarget** 是 Mathlib 中的一个定理，位于命名空间 
`RingHom`。
形式化陈述：finitePresentation_ofLocalizationSpanTarget : OfLocalizationSpanTarget @Fi
nitePresentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `IsScalarTower.Algebra.ext`：∀ {S : Type u} {A : Type v} [inst : CommSemir
ing S] [inst_1 : Semiring A] (h1 h2 : Algebra S A),   (∀ (r : S) (x : A),       
(have I := h1; …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用引理 `Algebra.FinitePresentation.of_span_eq_top_target`：of_span_eq_top_target 
(s : Set S) (hs : Ideal.span (s : Set S) = ⊤) (h : forall i in s, Algebra.Finite
Presentation R (Localization.Away i)) …

--- 原说明 ---
Finite-presentation can be checked on a standard covering of the target.
-/
theorem finitePresentation_ofLocalizationSpanTarget :
    OfLocalizationSpanTarget @FinitePresentation := by
  introv R hs H
  algebraize [f]
  replace H : ∀ r ∈ s, Algebra.FinitePresentation R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FinitePresentation] at H; convert! H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FinitePresentation.of_span_eq_top_target s hs H

/-- Being finitely-presented is a local property of rings. -/
/-
**RingHom.finitePresentation_isLocal** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：finitePresentation_isLocal : PropertyIsLocal @FinitePresentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用定理 `RingHom.finitePresentation_localizationPreserves`：finitePresentation_loc
alizationPreserves : LocalizationPreserves @FinitePresentation
· 使用定理 `RingHom.finitePresentation_ofLocalizationSpanTarget`：finitePresentation_
ofLocalizationSpanTarget : OfLocalizationSpanTarget @FinitePresentation
· 使用定理 `RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`：RingHom.OfLocalizat
ionSpanTarget.ofLocalizationSpan (hP : RingHom.OfLocalizationSpanTarget @P) (hP'
 : RingHom.StableUnderCompositionWithLoca…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAwa
y`：RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway (hP
c : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizati…
· 使用定理 `RingHom.finitePresentation_stableUnderComposition`：finitePresentation_st
ableUnderComposition : StableUnderComposition @FinitePresentation
· 使用定理 `RingHom.finitePresentation_holdsForLocalizationAway`：finitePresentation_
holdsForLocalizationAway : HoldsForLocalizationAway @FinitePresentation
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Being finitely-presented is a local property of rings.
-/
theorem finitePresentation_isLocal : PropertyIsLocal @FinitePresentation :=
  ⟨finitePresentation_localizationPreserves.away,
    finitePresentation_ofLocalizationSpanTarget,
    finitePresentation_ofLocalizationSpanTarget.ofLocalizationSpan
      (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finitePresentation_holdsForLocalizationAway).left,
    (finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finitePresentation_holdsForLocalizationAway).right⟩

end RingHom

