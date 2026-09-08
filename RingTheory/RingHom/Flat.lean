/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Flat ring homomorphisms

In this file we define flat ring homomorphisms and show their meta properties.

-/

@[expose] public section

universe u₁ u₂ u v

open TensorProduct

/-- A ring homomorphism `f : R →+* S` is flat if `S` is flat as an `R` module. -/
@[algebraize Module.Flat]
/-
**RingHom.Flat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R ->
+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f : R →+* S` is flat if `S` is flat as an `R` module.
-/
def RingHom.Flat {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Module.Flat R S
/-
**RingHom.flat_algebraMap_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.flat_algebraMap_iff {R S : Type*} [CommRing R] [CommRing S] [Algeb
ra R S] : (algebraMap R S).Flat ↔ Module.Flat R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.Flat.eq_1`：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst
_1 : CommRing S] (f : R →+* S), f.Flat = Module.Flat R S
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma RingHom.flat_algebraMap_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).Flat ↔ Module.Flat R S := by
  rw [RingHom.Flat, toAlgebra_algebraMap]

namespace RingHom.Flat

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

variable (R) in
/-- The identity of a ring is flat. -/
/-
**RingHom.Flat.id** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：id : RingHom.Flat (RingHom.id R)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity of a ring is flat.
-/
lemma id : RingHom.Flat (RingHom.id R) :=
  Module.Flat.self

/-- Composition of flat ring homomorphisms is flat. -/
/-
**RingHom.Flat.comp** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg : g.Flat) : Flat (g.c
omp f)
参数：hf : f.Flat；hg : g.Flat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Module.Flat.trans`：trans [Flat R S] [Flat S M] : Flat R M

--- 原说明 ---
Composition of flat ring homomorphisms is flat.
-/
lemma comp {f : R →+* S} {g : S →+* T} (hf : f.Flat) (hg : g.Flat) : Flat (g.comp f) := by
  algebraize [f, g, (g.comp f)]
  exact Module.Flat.trans R S T

/-- Bijective ring maps are flat. -/
/-
**RingHom.Flat.of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：of_bijective {f : R ->+* S} (hf : Function.Bijective f) : Flat f
参数：hf : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…

--- 原说明 ---
Bijective ring maps are flat.
-/
lemma of_bijective {f : R →+* S} (hf : Function.Bijective f) : Flat f := by
  algebraize [f]
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap R S) hf).symm
/-
**RingHom.Flat.containsIdentities** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：containsIdentities : ContainsIdentities Flat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.Flat.id`：id : RingHom.Flat (RingHom.id R)
-/
lemma containsIdentities : ContainsIdentities Flat := id
/-
**RingHom.Flat.stableUnderComposition** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：stableUnderComposition : StableUnderComposition Flat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.Flat.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg 
: g.Flat) : Flat (g.comp f)
-/
lemma stableUnderComposition : StableUnderComposition Flat := by
  introv R hf hg
  exact hf.comp hg
/-
**RingHom.Flat.respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：respectsIso : RespectsIso Flat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用引理 `RingHom.Flat.stableUnderComposition`：stableUnderComposition : StableUnde
rComposition Flat
· 使用引理 `RingHom.Flat.of_bijective`：of_bijective {f : R ->+* S} (hf : Function.Bi
jective f) : Flat f
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
lemma respectsIso : RespectsIso Flat := by
  apply stableUnderComposition.respectsIso
  introv
  exact of_bijective e.bijective
/-
**RingHom.Flat.isStableUnderBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：isStableUnderBaseChange : IsStableUnderBaseChange Flat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用引理 `RingHom.Flat.respectsIso`：respectsIso : RespectsIso Flat
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.flat_algebraMap_iff`：RingHom.flat_algebraMap_iff {R S : Type*} [
CommRing R] [CommRing S] [Algebra R S] : (algebraMap R S).Flat ↔ Module.Flat R S
-/
lemma isStableUnderBaseChange : IsStableUnderBaseChange Flat := by
  apply IsStableUnderBaseChange.mk respectsIso
  introv h
  rw [flat_algebraMap_iff] at h ⊢
  infer_instance
/-
**RingHom.Flat.holdsForLocalizationAway** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`
。
形式化陈述：holdsForLocalizationAway : HoldsForLocalizationAway Flat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RingHom.flat_algebraMap_iff`：RingHom.flat_algebraMap_iff {R S : Type*} [
CommRing R] [CommRing S] [Algebra R S] : (algebraMap R S).Flat ↔ Module.Flat R S
· 使用定理 `IsLocalization.flat`：IsLocalization.flat : Module.Flat R S
-/
lemma holdsForLocalizationAway : HoldsForLocalizationAway Flat := by
  introv R h
  exact flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers r))
/-
**RingHom.Flat.ofLocalizationSpanTarget** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`
。
形式化陈述：ofLocalizationSpanTarget : OfLocalizationSpanTarget Flat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.flat_of_isLocalized_span`：flat_of_isLocalized_span (H : forall r 
: s, Module.Flat R (Mₛ r)) : Module.Flat R M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Module.ext`：∀ {R : Type u} {M : Type v} {inst : Semiring R} {inst_1 : Ad
dCommMonoid M} {x y : _root_.Module R M},   SMul.smul = SMul.smul → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
lemma ofLocalizationSpanTarget : OfLocalizationSpanTarget Flat := by
  introv R hsp h
  algebraize_only [f]
  refine Module.flat_of_isLocalized_span _ _ s hsp _
    (fun r ↦ Algebra.linearMap S <| Localization.Away r.1) ?_
  dsimp only [RingHom.Flat] at h
  convert! h; ext
  apply Algebra.smul_def

/-- Flat is a local property of ring homomorphisms. -/
/-
**RingHom.Flat.propertyIsLocal** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：propertyIsLocal : PropertyIsLocal Flat where localizationAwayPreserves
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用引理 `RingHom.Flat.isStableUnderBaseChange`：isStableUnderBaseChange : IsStable
UnderBaseChange Flat
· 使用引理 `RingHom.Flat.ofLocalizationSpanTarget`：ofLocalizationSpanTarget : OfLoca
lizationSpanTarget Flat
· 使用定理 `RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`：RingHom.OfLocalizat
ionSpanTarget.ofLocalizationSpan (hP : RingHom.OfLocalizationSpanTarget @P) (hP'
 : RingHom.StableUnderCompositionWithLoca…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAwa
y`：RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway (hP
c : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizati…
· 使用引理 `RingHom.Flat.stableUnderComposition`：stableUnderComposition : StableUnde
rComposition Flat
· 使用引理 `RingHom.Flat.holdsForLocalizationAway`：holdsForLocalizationAway : HoldsF
orLocalizationAway Flat
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Flat is a local property of ring homomorphisms.
-/
lemma propertyIsLocal : PropertyIsLocal Flat where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right
/-
**RingHom.Flat.ofLocalizationPrime** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：ofLocalizationPrime : OfLocalizationPrime Flat
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.Flat.eq_1`：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst
_1 : CommRing S] (f : R →+* S), f.Flat = Module.Flat R S
· 使用定理 `Module.flat_of_isLocalized_maximal`：flat_of_isLocalized_maximal (H : for
all (P : Ideal S) [P.IsMaximal], Flat R (Mₚ P)) : Module.Flat R M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
· 使用定理 `Module.Flat.trans`：trans [Flat R S] [Flat S M] : Flat R M
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
-/
lemma ofLocalizationPrime : OfLocalizationPrime Flat := by
  introv R h
  algebraize_only [f]
  rw [RingHom.Flat]
  apply Module.flat_of_isLocalized_maximal S S (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap S _)
  intro P _
  algebraize_only [Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  replace h : Module.Flat (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) := h ..
  exact Module.Flat.trans R (Localization.AtPrime <| Ideal.comap f P) (Localization.AtPrime P)
/-
**RingHom.Flat.localRingHom** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：localRingHom {f : R ->+* S} (hf : f.Flat) (P : Ideal S) [P.IsPrime] (Q : I
deal R) [Q.IsPrime] (hQP : Q = Ideal.comap f P) : (Localization.localRingHom Q P
 f hQP).Flat
参数：hf : f.Flat；P : Ideal S；Q : Ideal R；hQP : Q = Ideal.comap f P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.Flat.eq_1`：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst
_1 : CommRing S] (f : R →+* S), f.Flat = Module.Flat R S
· 使用定理 `Module.flat_iff_of_isLocalization`：flat_iff_of_isLocalization : Flat S M
 ↔ Flat R M
· 使用定理 `Module.Flat.trans`：trans [Flat R S] [Flat S M] : Flat R M
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
-/
lemma localRingHom {f : R →+* S} (hf : f.Flat)
    (P : Ideal S) [P.IsPrime] (Q : Ideal R) [Q.IsPrime] (hQP : Q = Ideal.comap f P) :
    (Localization.localRingHom Q P f hQP).Flat := by
  subst hQP
  algebraize [f, Localization.localRingHom (Ideal.comap f P) P f rfl]
  have : IsScalarTower R (Localization.AtPrime (Ideal.comap f P)) (Localization.AtPrime P) :=
    .of_algebraMap_eq fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  rw [RingHom.Flat, Module.flat_iff_of_isLocalization
    (S := (Localization.AtPrime (Ideal.comap f P))) (p := (Ideal.comap f P).primeCompl)]
  exact Module.Flat.trans R S (Localization.AtPrime P)

open PrimeSpectrum

/-- `Spec S → Spec R` is generalizing if `R →+* S` is flat. -/
/-
**RingHom.Flat.generalizingMap_comap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：generalizingMap_comap {f : R ->+* S} (hf : f.Flat) : GeneralizingMap (coma
p f)
参数：hf : f.Flat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`：iff_general
izingMap_primeSpectrumComap : Algebra.HasGoingDown R S ↔ GeneralizingMap (PrimeS
pectrum.comap (algebraMap R S))

--- 原说明 ---
`Spec S → Spec R` is generalizing if `R →+* S` is flat.
-/
lemma generalizingMap_comap {f : R →+* S} (hf : f.Flat) : GeneralizingMap (comap f) := by
  algebraize [f]
  change GeneralizingMap (comap (algebraMap R S))
  rw [← Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap]
  infer_instance
/-
**RingHom.Flat.of_isField** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：of_isField (hR : IsField R) (f : R ->+* S) : f.Flat
参数：hR : IsField R；f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用引理 `RingHom.flat_algebraMap_iff`：RingHom.flat_algebraMap_iff {R S : Type*} [
CommRing R] [CommRing S] [Algebra R S] : (algebraMap R S).Flat ↔ Module.Flat R S
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
lemma of_isField (hR : IsField R) (f : R →+* S) : f.Flat := by
  let := f.toAlgebra
  let := hR.toField
  rw [← f.algebraMap_toAlgebra, RingHom.flat_algebraMap_iff]
  infer_instance

section

variable [Algebra R S]
variable (A : Type*) {B C D : Type*} [CommRing A] [Algebra R A] [Algebra S A]
  [IsScalarTower R S A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C] [Algebra S C]
  [IsScalarTower R S C] [CommRing D] [Algebra R D]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-
**RingHom.Flat.lTensor** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：lTensor {f : B ->ₐ[R] D} (hf : f.Flat) : (Algebra.TensorProduct.lTensor (S
参数：hf : f.Flat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClass`：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [inst_3 : Al
gebra R…
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `AlgEquiv.map_mul'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.map_add'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor`：∀ (R : Type u_1) [
inst : CommSemiring R] (A : Type u_8) [inst_1 : CommRing A] [inst_2 : Algebra R 
A] (C : Type u_11)   [inst_3 : CommRing C]…
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N
-/
lemma lTensor {f : B →ₐ[R] D} (hf : f.Flat) :
    (Algebra.TensorProduct.lTensor (S := S) A f).Flat := by
  algebraize [f.toRingHom, (Algebra.TensorProduct.lTensor (S := A) A f).toRingHom]
  let e : A ⊗[R] D ≃ₐ[A ⊗[R] B] (A ⊗[R] B) ⊗[B] D :=
    { __ := (Algebra.IsPushout.cancelBaseChangeAlg _ _ _ _ _).symm,
      commutes' x := congr($(Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor R B D A) x) }
  exact .of_linearEquiv e.toLinearEquiv

variable {A} in
/-
**RingHom.Flat.tensorProductMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：tensorProductMap {f : A ->ₐ[S] C} {g : B ->ₐ[R] D} (hf : f.Flat) (hg : g.F
lat) : (Algebra.TensorProduct.map f g).Flat
参数：hf : f.Flat；hg : g.Flat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.TensorProduct.map_comp_includeLeft`：map_comp_includeLeft (f : A 
->ₐ[S] C) (g : B ->ₐ[R] D) : (map f g).comp includeLeft = includeLeft.comp f
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.TensorProduct.map_restrictScalars_comp_includeRight`：map_restric
tScalars_comp_includeRight (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) : ((map f g).restri
ctScalars R).comp includeRight = includeRight.com…
· 使用引理 `RingHom.Flat.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg 
: g.Flat) : Flat (g.comp f)
· 使用引理 `RingHom.Flat.lTensor`：lTensor {f : B ->ₐ[R] D} (hf : f.Flat) : (Algebra.
TensorProduct.lTensor (S
· 使用引理 `RingHom.Flat.of_bijective`：of_bijective {f : R ->+* S} (hf : Function.Bi
jective f) : Flat f
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
lemma tensorProductMap {f : A →ₐ[S] C} {g : B →ₐ[R] D} (hf : f.Flat) (hg : g.Flat) :
    (Algebra.TensorProduct.map f g).Flat := by
  have heq : Algebra.TensorProduct.map f g =
      (Algebra.TensorProduct.map f (.id R D)).comp (Algebra.TensorProduct.map (.id _ _) g) := by
    ext <;> simp
  rw [heq]
  refine RingHom.Flat.comp ?_ ?_
  · exact hg.lTensor _
  · have : (Algebra.TensorProduct.map f (AlgHom.id R D)).restrictScalars R =
        (Algebra.TensorProduct.comm _ _ _).toAlgHom.comp
          ((Algebra.TensorProduct.lTensor _ (f.restrictScalars R)).comp
            (Algebra.TensorProduct.comm _ _ _).toAlgHom) := by
      ext <;> simp
    change ((Algebra.TensorProduct.map f (AlgHom.id R D)).restrictScalars R).Flat
    rw [this]
    refine RingHom.Flat.comp ?_ (.of_bijective <| AlgEquiv.bijective _)
    change RingHom.Flat (RingHom.comp (Algebra.TensorProduct.lTensor D
      (AlgHom.restrictScalars R f)).toRingHom _)
    exact RingHom.Flat.comp (.of_bijective <| (TensorProduct.comm R A D).bijective) (lTensor D hf)

end

/-
**RingHom.Flat.comp_iff_of_bijective_left** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Fla
t`。
形式化陈述：comp_iff_of_bijective_left {f : R ->+* S} {g : S ->+* T} (hg : Function.Bi
jective g) : (g.comp f).Flat ↔ f.Flat
参数：hg : Function.Bijective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RingHom.Flat.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg 
: g.Flat) : Flat (g.comp f)
· 使用引理 `RingHom.Flat.of_bijective`：of_bijective {f : R ->+* S} (hf : Function.Bi
jective f) : Flat f
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
lemma comp_iff_of_bijective_left {f : R →+* S} {g : S →+* T} (hg : Function.Bijective g) :
    (g.comp f).Flat ↔ f.Flat := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ .comp hf (.of_bijective hg)⟩
  let e := RingEquiv.ofBijective g hg
  have : f = e.symm.toRingHom.comp (e.toRingHom.comp f) := by ext; simp
  rw [this]
  exact .comp hf (.of_bijective e.symm.bijective)
/-
**RingHom.Flat.comp_iff_of_bijective_right** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Fl
at`。
形式化陈述：comp_iff_of_bijective_right {f : R ->+* S} {g : T ->+* R} (hg : Function.B
ijective g) : (f.comp g).Flat ↔ f.Flat
参数：hg : Function.Bijective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RingHom.Flat.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg 
: g.Flat) : Flat (g.comp f)
· 使用引理 `RingHom.Flat.of_bijective`：of_bijective {f : R ->+* S} (hf : Function.Bi
jective f) : Flat f
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
lemma comp_iff_of_bijective_right {f : R →+* S} {g : T →+* R} (hg : Function.Bijective g) :
    (f.comp g).Flat ↔ f.Flat := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ .comp (.of_bijective hg) hf⟩
  let e := RingEquiv.ofBijective g hg
  have : f = (f.comp e.toRingHom).comp e.symm.toRingHom := by ext; simp
  rw [this]
  exact .comp (.of_bijective e.symm.bijective) hf

@[simp]
/-
**RingHom.Flat.ulift_iff** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Flat`。
形式化陈述：ulift_iff {f : R ->+* S} : (ulift.{u₁, u₂} f).Flat ↔ f.Flat
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RingHom.comp_ulift_eq`：RingHom.comp_ulift_eq (f : R ->+* S) : ULift.ring
Equiv.toRingHom.comp ((ulift.{u₁, u₂} f).comp ULift.ringEquiv.symm.toRingHom) = 
f
· 使用引理 `RingHom.Flat.comp_iff_of_bijective_left`：comp_iff_of_bijective_left {f :
 R ->+* S} {g : S ->+* T} (hg : Function.Bijective g) : (g.comp f).Flat ↔ f.Flat
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用引理 `RingHom.Flat.comp_iff_of_bijective_right`：comp_iff_of_bijective_right {f
 : R ->+* S} {g : T ->+* R} (hg : Function.Bijective g) : (f.comp g).Flat ↔ f.Fl
at
· 使用引理 `RingHom.Flat.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg 
: g.Flat) : Flat (g.comp f)
· 使用引理 `RingHom.Flat.of_bijective`：of_bijective {f : R ->+* S} (hf : Function.Bi
jective f) : Flat f
-/
lemma ulift_iff {f : R →+* S} : (ulift.{u₁, u₂} f).Flat ↔ f.Flat := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · rwa [← comp_ulift_eq.{u₁, u₂} f, comp_iff_of_bijective_left (Equiv.bijective _),
      comp_iff_of_bijective_right (Equiv.bijective _)]
  · exact .comp (.comp (.of_bijective <| Equiv.bijective _) hf)
      (.of_bijective <| Equiv.bijective _)

end RingHom.Flat

section

open CategoryTheory Limits

variable {R S T : CommRingCat} (f : R ⟶ S) (g : R ⟶ T)

/-
**CommRingCat.inr_injective_of_flat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommRingCat.inr_injective_of_flat (hf : Function.Injective f) (hg : g.hom.
Flat) : Function.Injective (pushout.inr f g)
参数：hf : Function.Injective f；hg : g.hom.Flat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用引理 `CommRingCat.isPushout_tensorProduct`：isPushout_tensorProduct (R A B : Ty
pe u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] : IsPus
hout (ofHom <| algebraMap…
· 使用定理 `CategoryTheory.IsPushout.inr_isoPushout_hom`：inr_isoPushout_hom (h : IsP
ushout f g inl inr) [HasPushout f g] : inr ≫ h.isoPushout.hom = pushout.inr _ _
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `Algebra.TensorProduct.includeRight_injective`：includeRight_injective [Mo
dule.Flat R B] (ha : Function.Injective (algebraMap R A)) : Function.Injective (
includeRight : B ->ₐ[R] A otimes[R…
-/
lemma CommRingCat.inr_injective_of_flat
    (hf : Function.Injective f) (hg : g.hom.Flat) : Function.Injective (pushout.inr f g) := by
  algebraize [f.hom, g.hom]
  have : _ = pushout.inr f g := (CommRingCat.isPushout_tensorProduct R S T).inr_isoPushout_hom
  rw [← this]
  exact (CommRingCat.isPushout_tensorProduct R S T).isoPushout.commRingCatIsoToRingEquiv
    |>.injective.comp (Algebra.TensorProduct.includeRight_injective (B := T) hf)
/-
**CommRingCat.inl_injective_of_flat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CommRingCat.inl_injective_of_flat (hf : f.hom.Flat) (hg : Function.Injecti
ve g) : Function.Injective (pushout.inl f g)
参数：hf : f.hom.Flat；hg : Function.Injective g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用引理 `CommRingCat.isPushout_tensorProduct`：isPushout_tensorProduct (R A B : Ty
pe u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] : IsPus
hout (ofHom <| algebraMap…
· 使用定理 `CategoryTheory.IsPushout.inl_isoPushout_hom`：inl_isoPushout_hom (h : IsP
ushout f g inl inr) [HasPushout f g] : inl ≫ h.isoPushout.hom = pushout.inl _ _
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `Algebra.TensorProduct.includeLeft_injective`：includeLeft_injective [Modu
le.Flat R A] (hb : Function.Injective (algebraMap R B)) : Function.Injective (in
cludeLeft : A ->ₐ[S] A otimes[R] …
-/
lemma CommRingCat.inl_injective_of_flat
    (hf : f.hom.Flat) (hg : Function.Injective g) : Function.Injective (pushout.inl f g) := by
  algebraize [f.hom, g.hom]
  have : _ = pushout.inl f g := (CommRingCat.isPushout_tensorProduct R S T).inl_isoPushout_hom
  rw [← this]
  exact (CommRingCat.isPushout_tensorProduct R S T).isoPushout.commRingCatIsoToRingEquiv
    |>.injective.comp (Algebra.TensorProduct.includeLeft_injective (S := R) (A := S) hg)

end

open CategoryTheory

namespace CommRingCat

/-- The morphism property of flat ring maps. -/
/-
**CommRingCat.flat** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：flat : MorphismProperty CommRingCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism property of flat ring maps.
-/
def flat : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty fun f ↦ f.Flat

@[simp]
/-
**CommRingCat.flat_iff** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：flat_iff {R S : CommRingCat.{u}} (f : R ⟶ S) : flat f ↔ f.hom.Flat
参数：f : R ⟶ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma flat_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    flat f ↔ f.hom.Flat := .rfl
/-
**CommRingCat.flat_ofHom_iff** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat`。
形式化陈述：flat_ofHom_iff {R S : Type u} [CommRing R] [CommRing S] (f : R ->+* S) : f
lat (ofHom f) ↔ f.Flat
参数：f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma flat_ofHom_iff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    flat (ofHom f) ↔ f.Flat := .rfl
/-
**CommRingCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommRingCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : flat.IsStableUnderCobaseChange := by
  rw [flat, RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.Flat.isStableUnderBaseChange

end CommRingCat

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/-- If `S ⊗[R] S → S` is flat, then also `T ⊗[R] A → T ⊗[S] A` is flat. -/
-- TODO: If necessary, generalize the universes here by composing with suitable `ULift`
-- isomorphisms.
/-
**RingHom.Flat.mapOfCompatibleSMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.Flat.mapOfCompatibleSMul {R S : Type u} (T A : Type u) [CommRing R
] [CommRing S] [CommRing T] [CommRing A] [Algebra R S] [Algebra R T] [Algebra S 
T] [IsScalarTower R S T] [Algebra R A] [Algebra S A] [IsScalarTower R S A] (h : 
(Algebra.TensorProduct.lmul' (S
参数：T A : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CommRingCat.flat_ofHom_iff`：flat_ofHom_iff {R S : Type u} [CommRing R] [
CommRing S] (f : R ->+* S) : flat (ofHom f) ↔ f.Flat
· 使用定理 `CategoryTheory.MorphismProperty.of_isPushout`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self :
 P.IsStableUnderCobaseChange] {A A…
· 使用定理 `CommRingCat.instIsStableUnderCobaseChangeFlat`：CommRingCat.flat.IsStable
UnderCobaseChange
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用引理 `CategoryTheory.IsPushout.of_iso`：of_iso (h : IsPushout f g inl inr) {Z' 
X' Y' P' : C} {f' : Z' ⟶ X'} {g' : Z' ⟶ Y'} {inl' : X' ⟶ P'} {inr' : Y' ⟶ P'} (e
₁ : Z ≅ Z') (e₂ : X ≅…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
· 使用定理 `CategoryTheory.Limits.instHasPushoutComp`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) (g' : Z ⟶ W)   
[inst_1 : CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.isPushout_map_codiagonal`：isPushout_map_codiagonal
 {S T : C} (f : T ⟶ X) (g : T ⟶ Y) (i : S ⟶ T) : IsPushout (pushout.map i i (i ≫
 f) (i ≫ g) f g (𝟙 _) (by simp) (by …
· 使用引理 `CommRingCat.isPushout_tensorProduct`：isPushout_tensorProduct (R A B : Ty
pe u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] : IsPus
hout (ofHom <| algebraMap…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pushout.hom_ext`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Category
Theory.Limits.HasPushout f …
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `CategoryTheory.Limits.pushout.congrHom_hom`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] {X Y Z : C} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : X ⟶ Z} (h₁ : f
₁ = f₂)   (h₂ : g₁ = g₂) [inst_1…
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc_assoc`：∀ {J : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{
v, u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.mk_ι_app`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z} {W : C} (inl 
: Y ⟶ W)   (inr : Z ⟶ W) (eq : Cat…
（共 50 条，此处仅展示前 30 条）
-/
lemma RingHom.Flat.mapOfCompatibleSMul {R S : Type u} (T A : Type u)
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    (h : (Algebra.TensorProduct.lmul' (S := S) R).Flat) :
    (Algebra.TensorProduct.mapOfCompatibleSMul S R T T A).Flat := by
  rw [← CommRingCat.flat_ofHom_iff] at h ⊢
  apply MorphismProperty.of_isPushout _ h
  · exact CommRingCat.ofHom
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S T)
      (IsScalarTower.toAlgHom R S A)).toRingHom
  · exact CommRingCat.ofHom
      (RingHom.comp (Algebra.TensorProduct.includeLeft (S := R)).toRingHom (algebraMap S T))
  · refine .of_iso
      (isPushout_map_codiagonal (CommRingCat.ofHom <| algebraMap S T)
        (CommRingCat.ofHom <| algebraMap S A) (CommRingCat.ofHom <| algebraMap R S))
      ?_ ?_ (.refl _) ?_ ?_ ?_ ?_ ?_
    · exact (CommRingCat.isPushout_tensorProduct R S S).isoPushout.symm
    · exact pushout.congrHom (by simp [IsScalarTower.algebraMap_eq R S T])
          (by simp [IsScalarTower.algebraMap_eq R S A]) ≪≫
        (CommRingCat.isPushout_tensorProduct R T A).isoPushout.symm
    · exact (CommRingCat.isPushout_tensorProduct S T A).isoPushout.symm
    all_goals ext <;> simp
