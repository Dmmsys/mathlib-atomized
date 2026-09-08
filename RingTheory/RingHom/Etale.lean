/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Unramified
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.Flat

/-!
# Étale ring homomorphisms

We show the meta properties of étale morphisms.
-/

@[expose] public section

universe u

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring hom `R →+* S` is étale, if `S` is an étale `R`-algebra. -/
@[algebraize RingHom.Etale.toAlgebra]
/-
**RingHom.Etale** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：Etale {R S : Type*} [CommRing R] [CommRing S] (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring hom `R →+* S` is étale, if `S` is an étale `R`-algebra.
-/
def Etale {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.Etale R S _ _ f.toAlgebra

/-- Helper lemma for the `algebraize` tactic -/
/-
**RingHom.Etale.toAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Etale`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S}, f.Etale → Algebra.Etale R S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper lemma for the `algebraize` tactic
-/
lemma Etale.toAlgebra {f : R →+* S} (hf : Etale f) :
    @Algebra.Etale R S _ _ f.toAlgebra := hf

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
/-
**RingHom.etale_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：etale_algebraMap [Algebra R S] : (algebraMap R S).Etale ↔ Algebra.Etale R 
S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.Etale.eq_1`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing R] 
[inst_1 : CommRing S] (f : R →+* S), f.Etale = Algebra.Etale R S
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma etale_algebraMap [Algebra R S] : (algebraMap R S).Etale ↔ Algebra.Etale R S := by
  rw [RingHom.Etale, toAlgebra_algebraMap]
/-
**RingHom.etale_iff_formallyUnramified_and_smooth** 是 Mathlib 中的一个引理，位于命名空间 `Rin
gHom`。
形式化陈述：etale_iff_formallyUnramified_and_smooth : f.Etale ↔ f.FormallyUnramified ∧
 f.Smooth
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
· 使用定理 `Algebra.Etale.instSmooth`：∀ {R : Type u} {A : Type v} [inst : CommRing R
] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebra.Sm
ooth R A
· 使用定理 `Algebra.Etale.finitePresentation`：∀ {R : Type u} {A : Type v} {inst : Co
mmRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A
],   Algebra.FinitePre…
· 使用定理 `Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth`：of_forma
llyUnramified_and_formallySmooth [FormallyUnramified R A] [FormallySmooth R A] :
 FormallyEtale R A
· 使用定理 `Algebra.Smooth.finitePresentation`：∀ {R : Type u_4} {inst : CommRing R} 
{A : Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smoo
th R A], Algebra.Finite…
-/
lemma etale_iff_formallyUnramified_and_smooth : f.Etale ↔ f.FormallyUnramified ∧ f.Smooth := by
  algebraize [f]
  simp only [Etale, Smooth, FormallyUnramified]
  exact ⟨fun h ↦ ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨h1, h2⟩ ↦ ⟨.of_formallyUnramified_and_formallySmooth, inferInstance⟩⟩
/-
**RingHom.Etale.eq_formallyUnramified_and_smooth** 是 Mathlib 中的一个定理，位于命名空间 `Ring
Hom.Etale`。
形式化陈述：@RingHom.Etale = fun R S x x_1 f => f.FormallyUnramified ∧ f.Smooth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.etale_iff_formallyUnramified_and_smooth`：etale_iff_formallyUnram
ified_and_smooth : f.Etale ↔ f.FormallyUnramified ∧ f.Smooth
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Etale.eq_formallyUnramified_and_smooth :
    @Etale = fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.FormallyUnramified ∧ f.Smooth := by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]
/-
**RingHom.Etale.formallyUnramified** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Etale`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing R] [inst_1 : CommRing S] 
(f : R →+* S), f.Etale → f.FormallyUnramified
参数：f : R →+* S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.etale_iff_formallyUnramified_and_smooth`：etale_iff_formallyUnram
ified_and_smooth : f.Etale ↔ f.FormallyUnramified ∧ f.Smooth
-/
lemma Etale.formallyUnramified (hf : f.Etale) : f.FormallyUnramified := by
  rw [etale_iff_formallyUnramified_and_smooth] at hf
  exact hf.1
/-
**RingHom.Etale.of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Etale`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S}, Function.Bijective ⇑f → f.Etale
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.etale_iff_formallyUnramified_and_smooth`：etale_iff_formallyUnram
ified_and_smooth : f.Etale ↔ f.FormallyUnramified ∧ f.Smooth
· 使用引理 `RingHom.FormallyUnramified.of_surjective`：of_surjective {f : R ->+* S} (
hf : Function.Surjective f) : f.FormallyUnramified
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `RingHom.Smooth.of_bijective`：of_bijective {f : R ->+* S} (hf : Function.
Bijective f) : f.Smooth
-/
lemma Etale.of_bijective {f : R →+* S} (hf : Function.Bijective f) : f.Etale := by
  rw [etale_iff_formallyUnramified_and_smooth]
  exact ⟨.of_surjective hf.2, .of_bijective hf⟩
/-
**RingHom.Etale.containsIdentities** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Etale`。
形式化陈述：RingHom.ContainsIdentities fun {R S} [CommRing R] [CommRing S] => RingHom.
Etale
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.Etale.of_bijective`：∀ {R : Type u_3} {S : Type u_4} [inst : Comm
Ring R] [inst_1 : CommRing S] {f : R →+* S}, Function.Bijective ⇑f → f.Etale
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
lemma Etale.containsIdentities : ContainsIdentities Etale :=
  fun _ _ ↦ .of_bijective Function.bijective_id
/-
**RingHom.Etale.isStableUnderBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Etale
`。
形式化陈述：RingHom.IsStableUnderBaseChange fun {R S} [CommRing R] [CommRing S] => Rin
gHom.Etale
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.Etale.eq_formallyUnramified_and_smooth`：@RingHom.Etale = fun R S
 x x_1 f => f.FormallyUnramified ∧ f.Smooth
· 使用定理 `RingHom.IsStableUnderBaseChange.and`：∀ {P Q : {R S : Type u} → [inst : C
ommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.IsStableUnder
BaseChange fun {R S} [Com…
· 使用引理 `RingHom.FormallyUnramified.isStableUnderBaseChange`：isStableUnderBaseCha
nge : IsStableUnderBaseChange FormallyUnramified
· 使用引理 `RingHom.Smooth.isStableUnderBaseChange`：isStableUnderBaseChange : IsStab
leUnderBaseChange Smooth
-/
lemma Etale.isStableUnderBaseChange : IsStableUnderBaseChange Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.isStableUnderBaseChange.and Smooth.isStableUnderBaseChange
/-
**RingHom.Etale.propertyIsLocal** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Etale`。
形式化陈述：RingHom.PropertyIsLocal fun {R S} [CommRing R] [CommRing S] => RingHom.Eta
le
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.Etale.eq_formallyUnramified_and_smooth`：@RingHom.Etale = fun R S
 x x_1 f => f.FormallyUnramified ∧ f.Smooth
· 使用引理 `RingHom.PropertyIsLocal.and`：RingHom.PropertyIsLocal.and (hP : PropertyI
sLocal P) (hQ : PropertyIsLocal Q) : PropertyIsLocal (fun f => P f ∧ Q f) where 
localizationAwayP…
· 使用引理 `RingHom.FormallyUnramified.propertyIsLocal`：propertyIsLocal : PropertyIs
Local FormallyUnramified
· 使用引理 `RingHom.Smooth.propertyIsLocal`：propertyIsLocal : PropertyIsLocal Smooth
 where localizationAwayPreserves
-/
lemma Etale.propertyIsLocal : PropertyIsLocal Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.propertyIsLocal.and Smooth.propertyIsLocal
/-
**RingHom.Etale.respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Etale`。
形式化陈述：RingHom.RespectsIso fun {R S} [CommRing R] [CommRing S] => RingHom.Etale
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用定理 `RingHom.Etale.propertyIsLocal`：RingHom.PropertyIsLocal fun {R S} [CommRi
ng R] [CommRing S] => RingHom.Etale
-/
lemma Etale.respectsIso : RespectsIso Etale :=
  propertyIsLocal.respectsIso
/-
**RingHom.Etale.ofLocalizationSpanTarget** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Etal
e`。
形式化陈述：RingHom.OfLocalizationSpanTarget fun {R S} [CommRing R] [CommRing S] => Ri
ngHom.Etale
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.PropertyIsLocal.ofLocalizationSpanTarget`：∀ {P : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.Pro
pertyIsLocal P → RingHom.OfLocalizatio…
· 使用定理 `RingHom.Etale.propertyIsLocal`：RingHom.PropertyIsLocal fun {R S} [CommRi
ng R] [CommRing S] => RingHom.Etale
-/
lemma Etale.ofLocalizationSpanTarget : OfLocalizationSpanTarget Etale :=
  propertyIsLocal.ofLocalizationSpanTarget
/-
**RingHom.Etale.ofLocalizationSpan** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Etale`。
形式化陈述：RingHom.OfLocalizationSpan fun {R S} [CommRing R] [CommRing S] => RingHom.
Etale
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.PropertyIsLocal.ofLocalizationSpan`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.PropertyI
sLocal P → RingHom.OfLocalizatio…
· 使用定理 `RingHom.Etale.propertyIsLocal`：RingHom.PropertyIsLocal fun {R S} [CommRi
ng R] [CommRing S] => RingHom.Etale
-/
lemma Etale.ofLocalizationSpan : OfLocalizationSpan Etale :=
  propertyIsLocal.ofLocalizationSpan
/-
**RingHom.Etale.stableUnderComposition** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Etale`
。
形式化陈述：RingHom.StableUnderComposition fun {R S} [CommRing R] [CommRing S] => Ring
Hom.Etale
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.Etale.eq_formallyUnramified_and_smooth`：@RingHom.Etale = fun R S
 x x_1 f => f.FormallyUnramified ∧ f.Smooth
· 使用定理 `RingHom.StableUnderComposition.and`：∀ {P Q : {R S : Type u} → [inst : Co
mmRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.StableUnderCom
position fun {R S} [Comm…
· 使用引理 `RingHom.FormallyUnramified.stableUnderComposition`：stableUnderCompositio
n : StableUnderComposition FormallyUnramified
· 使用引理 `RingHom.Smooth.stableUnderComposition`：stableUnderComposition : StableUn
derComposition Smooth
-/
lemma Etale.stableUnderComposition : StableUnderComposition Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.stableUnderComposition.and Smooth.stableUnderComposition
/-
**RingHom.Etale.iff_flat_and_formallyUnramified** 是 Mathlib 中的一个定理，位于命名空间 `RingH
om.Etale`。
形式化陈述：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S},   f.Etale ↔ f.Flat ∧ f.FormallyUnramified ∧ f.FinitePresentation
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Smooth.flat`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R]
 [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Smooth R A],   Module.Fla
t R A
· 使用定理 `Algebra.Etale.instSmooth`：∀ {R : Type u} {A : Type v} [inst : CommRing R
] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebra.Sm
ooth R A
· 使用定理 `Algebra.Unramified.formallyUnramified`：∀ {R : Type u_1} {inst : CommRing
 R} {A : Type u_2} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebr
a.Unramified R A], Algebra.…
· 使用定理 `Algebra.Etale.instUnramified`：∀ {R : Type u} {A : Type v} [inst : CommRi
ng R] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebr
a.Unramified R A
· 使用定理 `Algebra.Etale.finitePresentation`：∀ {R : Type u} {A : Type v} {inst : Co
mmRing R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A
],   Algebra.FinitePre…
· 使用定理 `Algebra.Etale.of_formallyUnramified_of_flat`：∀ {R : Type u_4} {S : Type 
u_5} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.FinitePresentation R S] [Module.…
-/
lemma Etale.iff_flat_and_formallyUnramified {f : R →+* S} :
    f.Etale ↔ f.Flat ∧ f.FormallyUnramified ∧ f.FinitePresentation := by
  algebraize [f]
  simp_rw [← f.algebraMap_toAlgebra, RingHom.etale_algebraMap, RingHom.flat_algebraMap_iff,
    RingHom.formallyUnramified_algebraMap, RingHom.finitePresentation_algebraMap]
  refine ⟨fun h ↦ ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨_, _, _⟩ ↦ .of_formallyUnramified_of_flat⟩

end RingHom

