/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.FiniteTypeLocal
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.RingHom.Finite

/-!

# The meta properties of finite-type ring homomorphisms.

## Main results

Let `R` be a commutative ring, `S` is an `R`-algebra, `M` be a submonoid of `R`.

* `finiteType_localizationPreserves` : If `S` is a finite type `R`-algebra, then `S' = M⁻¹S` is a
  finite type `R' = M⁻¹R`-algebra.
* `finiteType_ofLocalizationSpan` : `S` is a finite type `R`-algebra if there exists
  a set `{ r }` that spans `R` such that `Sᵣ` is a finite type `Rᵣ`-algebra.
* `RingHom.finiteType_isLocal`: `RingHom.FiniteType` is a local property.

-/

public section

namespace RingHom

open scoped Pointwise TensorProduct

universe u

variable {R S : Type*} [CommRing R] [CommRing S] (M : Submonoid R) (f : R →+* S)
variable (R' S' : Type*) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

/-
**RingHom.finiteType_stableUnderComposition** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：finiteType_stableUnderComposition : StableUnderComposition @FiniteType
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FiniteType.comp`：comp {g : B ->+* C} {f : A ->+* B} (hg : g.Fini
teType) (hf : f.FiniteType) : (g.comp f).FiniteType
-/
theorem finiteType_stableUnderComposition : StableUnderComposition @FiniteType := by
  introv R hf hg
  exact hg.comp hf
/-
**RingHom.finiteType_respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：finiteType_respectsIso : RingHom.RespectsIso @RingHom.FiniteType
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用定理 `RingHom.finiteType_stableUnderComposition`：finiteType_stableUnderComposi
tion : StableUnderComposition @FiniteType
· 使用定理 `Algebra.FiniteType.equiv`：equiv (hRA : FiniteType R A) (e : A ≃ₐ[R] B) :
 FiniteType R B
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem finiteType_respectsIso : RingHom.RespectsIso @RingHom.FiniteType := by
  refine finiteType_stableUnderComposition.respectsIso (fun {R S} _ _ e ↦ ?_)
  algebraize [e.toRingHom]
  apply Algebra.FiniteType.equiv (inferInstanceAs <| Algebra.FiniteType R R) <|
    .ofRingEquiv (congrFun rfl)
/-
**RingHom.finiteType_isStableUnderBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`
。
形式化陈述：finiteType_isStableUnderBaseChange : IsStableUnderBaseChange @FiniteType
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用定理 `RingHom.finiteType_respectsIso`：finiteType_respectsIso : RingHom.Respect
sIso @RingHom.FiniteType
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `RingHom.finiteType_algebraMap`：finiteType_algebraMap [Algebra A B] : (al
gebraMap A B).FiniteType ↔ Algebra.FiniteType A B
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem finiteType_isStableUnderBaseChange : IsStableUnderBaseChange @FiniteType := by
  apply IsStableUnderBaseChange.mk
  · exact finiteType_respectsIso
  · introv h
    rw [finiteType_algebraMap] at h
    apply finiteType_algebraMap.mpr
    infer_instance

/-- If `S` is a finite type `R`-algebra, then `S' = M⁻¹S` is a finite type `R' = M⁻¹R`-algebra. -/
/-
**RingHom.finiteType_localizationPreserves** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：finiteType_localizationPreserves : RingHom.LocalizationPreserves @RingHom.
FiniteType
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用定理 `RingHom.finiteType_isStableUnderBaseChange`：finiteType_isStableUnderBase
Change : IsStableUnderBaseChange @FiniteType

--- 原说明 ---
If `S` is a finite type `R`-algebra, then `S' = M⁻¹S` is a finite type `R' = M⁻¹
R`-algebra.
-/
theorem finiteType_localizationPreserves : RingHom.LocalizationPreserves @RingHom.FiniteType :=
  finiteType_isStableUnderBaseChange.localizationPreserves
/-
**RingHom.localization_away_map_finiteType** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：localization_away_map_finiteType (R S R' S' : Type u) [CommRing R] [CommRi
ng S] [CommRing R'] [CommRing S'] [Algebra R R'] (f : R ->+* S) [Algebra S S'] (
r : R) [IsLocalization.Away r R'] [IsLocalization.Away (f r) S'] (hf : f.FiniteT
ype) : (IsLocalization.Away.map R' S' f r).FiniteType
参数：R S R' S' : Type u；f : R ->+* S；r : R；f r；hf : f.FiniteType。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用定理 `RingHom.finiteType_localizationPreserves`：finiteType_localizationPreserv
es : RingHom.LocalizationPreserves @RingHom.FiniteType
-/
theorem localization_away_map_finiteType (R S R' S' : Type u) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R R'] (f : R →+* S) [Algebra S S']
    (r : R) [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'] (hf : f.FiniteType) :
    (IsLocalization.Away.map R' S' f r).FiniteType :=
  finiteType_localizationPreserves.away _ r _ _ hf
/-
**RingHom.finiteType_ofLocalizationSpan** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：finiteType_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.Finite
Type
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.OfLocalizationSpan.mk`：RingHom.OfLocalizationSpan.mk (hP : RingH
om.RespectsIso P) (H : forall {R S : Type u} [CommRing R] [CommRing S] [Algebra 
R S] (s : Set R), I…
· 使用定理 `RingHom.finiteType_respectsIso`：finiteType_respectsIso : RingHom.Respect
sIso @RingHom.FiniteType
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Algebra.FiniteType.of_span_eq_top_source`：Algebra.FiniteType.of_span_eq_
top_source (s : Set R) (hs : Ideal.span (s : Set R) = ⊤) (h : forall i in s, Alg
ebra.FiniteType (Localization.…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem finiteType_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.FiniteType := by
  refine OfLocalizationSpan.mk _ finiteType_respectsIso (fun s hs h ↦ ?_)
  simp_rw [finiteType_algebraMap] at h ⊢
  exact Algebra.FiniteType.of_span_eq_top_source s hs h
/-
**RingHom.finiteType_holdsForLocalizationAway** 是 Mathlib 中的一个定理，位于命名空间 `RingHom
`。
形式化陈述：finiteType_holdsForLocalizationAway : HoldsForLocalizationAway @FiniteType
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.finiteType_algebraMap`：finiteType_algebraMap [Algebra A B] : (al
gebraMap A B).FiniteType ↔ Algebra.FiniteType A B
· 使用定理 `IsLocalization.finiteType_of_monoid_fg`：finiteType_of_monoid_fg [Monoid.
FG M] : Algebra.FiniteType R S
-/
theorem finiteType_holdsForLocalizationAway : HoldsForLocalizationAway @FiniteType := by
  introv R _
  rw [finiteType_algebraMap]
  exact IsLocalization.finiteType_of_monoid_fg (Submonoid.powers r) S
/-
**RingHom.finiteType_ofLocalizationSpanTarget** 是 Mathlib 中的一个定理，位于命名空间 `RingHom
`。
形式化陈述：finiteType_ofLocalizationSpanTarget : OfLocalizationSpanTarget @FiniteType
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
· 使用引理 `Algebra.FiniteType.of_span_eq_top_target`：Algebra.FiniteType.of_span_eq_
top_target (s : Set S) (hs : Ideal.span (s : Set S) = ⊤) (h : forall x in s, Alg
ebra.FiniteType R (Localizatio…
-/
theorem finiteType_ofLocalizationSpanTarget : OfLocalizationSpanTarget @FiniteType := by
  introv R hs H
  algebraize [f]
  replace H : ∀ r ∈ s, Algebra.FiniteType R (Localization.Away (r : S)) := by
    intro r hr; simp_rw [RingHom.FiniteType] at H; convert! H ⟨r, hr⟩; ext
    simp_rw [Algebra.smul_def]; rfl
  exact Algebra.FiniteType.of_span_eq_top_target s hs H
/-
**RingHom.finiteType_isLocal** 是 Mathlib 中的一个定理，位于命名空间 `RingHom`。
形式化陈述：finiteType_isLocal : PropertyIsLocal @FiniteType
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用定理 `RingHom.finiteType_localizationPreserves`：finiteType_localizationPreserv
es : RingHom.LocalizationPreserves @RingHom.FiniteType
· 使用定理 `RingHom.finiteType_ofLocalizationSpanTarget`：finiteType_ofLocalizationSp
anTarget : OfLocalizationSpanTarget @FiniteType
· 使用定理 `RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`：RingHom.OfLocalizat
ionSpanTarget.ofLocalizationSpan (hP : RingHom.OfLocalizationSpanTarget @P) (hP'
 : RingHom.StableUnderCompositionWithLoca…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAwa
y`：RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway (hP
c : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizati…
· 使用定理 `RingHom.finiteType_stableUnderComposition`：finiteType_stableUnderComposi
tion : StableUnderComposition @FiniteType
· 使用定理 `RingHom.finiteType_holdsForLocalizationAway`：finiteType_holdsForLocaliza
tionAway : HoldsForLocalizationAway @FiniteType
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem finiteType_isLocal : PropertyIsLocal @FiniteType :=
  ⟨finiteType_localizationPreserves.away,
    finiteType_ofLocalizationSpanTarget,
    finiteType_ofLocalizationSpanTarget.ofLocalizationSpan
      (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
        finiteType_holdsForLocalizationAway).left,
    (finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      finiteType_holdsForLocalizationAway).right⟩

end RingHom

