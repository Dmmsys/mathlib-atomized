/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Meta properties of bijective ring homomorphisms

We show some meta properties of bijective ring homomorphisms.

## Implementation details

We don't define a `RingHom.Bijective` predicate, but use `fun f ↦ Function.Bijective f` as
the ring hom property.
-/

public section

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S]

namespace RingHom.Bijective

/-
**RingHom.Bijective.containsIdentities** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Biject
ive`。
形式化陈述：containsIdentities : ContainsIdentities (fun f => Function.Bijective f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
lemma containsIdentities : ContainsIdentities (fun f ↦ Function.Bijective f) :=
  fun _ _ ↦ Function.bijective_id
/-
**RingHom.Bijective.stableUnderComposition** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Bi
jective`。
形式化陈述：stableUnderComposition : StableUnderComposition (fun f => Function.Bijecti
ve f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.comp`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} {g 
: β → φ} {f : α → β},   Function.Bijective g → Function.Bijective f → Function.B
ijective (g ∘…
-/
lemma stableUnderComposition : StableUnderComposition (fun f ↦ Function.Bijective f) :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf
/-
**RingHom.Bijective.respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Bijective`。
形式化陈述：respectsIso : RespectsIso (fun f => Function.Bijective f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用引理 `RingHom.Bijective.stableUnderComposition`：stableUnderComposition : Stabl
eUnderComposition (fun f => Function.Bijective f)
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
lemma respectsIso : RespectsIso (fun f ↦ Function.Bijective f) :=
  RingHom.Bijective.stableUnderComposition.respectsIso fun e ↦ e.bijective
/-
**RingHom.Bijective.isStableUnderBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.B
ijective`。
形式化陈述：isStableUnderBaseChange : IsStableUnderBaseChange (fun f => Function.Bijec
tive f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用引理 `RingHom.Bijective.respectsIso`：respectsIso : RespectsIso (fun f => Funct
ion.Bijective f)
· 使用引理 `Algebra.TensorProduct.includeLeft_bijective`：includeLeft_bijective (h : 
Function.Bijective (algebraMap R B)) : Function.Bijective (includeLeft : A ->ₐ[S
] A otimes[R] B)
-/
lemma isStableUnderBaseChange : IsStableUnderBaseChange (fun f ↦ Function.Bijective f) :=
  .mk respectsIso fun R _ _ _ _ _ _ _ hf ↦
    Algebra.TensorProduct.includeLeft_bijective (S := R) hf
/-
**RingHom.Bijective.ofLocalizationSpan** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Biject
ive`。
形式化陈述：ofLocalizationSpan : OfLocalizationSpan (fun f => Function.Bijective f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `bijective_of_isLocalization_of_span_eq_top`：bijective_of_isLocalization_
of_span_eq_top (h : forall r : s, Function.Bijective (IsLocalization.Away.map (R
ᵣ r) (Sᵣ r) f r.1)) : Function.B…
-/
lemma ofLocalizationSpan : OfLocalizationSpan (fun f ↦ Function.Bijective f) :=
  fun _ _ _ _ f s hs hf ↦ bijective_of_isLocalization_of_span_eq_top (s := s) hs
    (fun r ↦ Localization.Away r.val) (fun r ↦ Localization.Away (f r.val)) f hf

end RingHom.Bijective

