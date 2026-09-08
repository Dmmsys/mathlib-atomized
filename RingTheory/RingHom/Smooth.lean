/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.Smooth.Locus

/-!
# Smooth ring homomorphisms

In this file we define smooth ring homomorphisms and show their meta properties.

-/

@[expose] public section

universe u

variable {R S : Type*} [CommRing R] [CommRing S]

open TensorProduct

namespace RingHom

/-- A ring homomorphism `f : R →+* S` is formally smooth
if `S` is formally smooth as an `R` algebra. -/
@[algebraize RingHom.FormallySmooth.toAlgebra]
/-
**RingHom.FormallySmooth** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：FormallySmooth (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f : R →+* S` is formally smooth
if `S` is formally smooth as an `R` algebra.
-/
def FormallySmooth (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallySmooth R S

/-- Helper lemma for the `algebraize` tactic -/
/-
**RingHom.FormallySmooth.toAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FormallySm
ooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S},   f.FormallySmooth → Algebra.FormallySmooth R S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper lemma for the `algebraize` tactic
-/
lemma FormallySmooth.toAlgebra {f : R →+* S} (hf : FormallySmooth f) :
    @Algebra.FormallySmooth R S _ _ f.toAlgebra := hf
/-
**RingHom.formallySmooth_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：formallySmooth_algebraMap [Algebra R S] : (algebraMap R S).FormallySmooth 
↔ Algebra.FormallySmooth R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.FormallySmooth.eq_1`：∀ {R : Type u_1} {S : Type u_2} [inst : Com
mRing R] [inst_1 : CommRing S] (f : R →+* S),   f.FormallySmooth = Algebra.Forma
llySmooth R S
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma formallySmooth_algebraMap [Algebra R S] :
    (algebraMap R S).FormallySmooth ↔ Algebra.FormallySmooth R S := by
  rw [FormallySmooth, toAlgebra_algebraMap]

/-- Composition of formally smooth ring homomorphisms is formally smooth. -/
/-
**RingHom.FormallySmooth.comp** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.FormallySmooth`
。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{T : Type u_3} [inst_2 : CommRing T]   {f : R →+* S} {g : S →+* T}, f.FormallySm
ooth → g.FormallySmooth → (g.comp f).FormallySmooth
参数：g.comp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.FormallySmooth.comp`：∀ (R : Type u_4) [inst : CommRing R] (A : T
ype u_5) [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_6)   [inst_3 :
 CommRing B] [ins…
· 使用定理 `RingHom.FormallySmooth.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] {f : R →+* S},   f.FormallySmooth → Algebra.
FormallySmooth R S

--- 原说明 ---
Composition of formally smooth ring homomorphisms is formally smooth.
-/
lemma FormallySmooth.comp {T : Type*} [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.FormallySmooth) (hg : g.FormallySmooth) : (g.comp f).FormallySmooth := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallySmooth.comp R S T
/-
**RingHom.FormallySmooth.of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Formall
ySmooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S},   Function.Bijective ⇑f → f.FormallySmooth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallySmooth.of_equiv`：∀ {R : Type u_4} [inst : CommRing R] {A
 : Type u_5} {B : Type u_6} [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst
_3 : CommRing B] [ins…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
· 使用定理 `Algebra.Etale.instSmooth`：∀ {R : Type u} {A : Type v} [inst : CommRing R
] [inst_1 : CommRing A] [inst_2 : Algebra R A] [Algebra.Etale R A],   Algebra.Sm
ooth R A
· 使用定理 `Algebra.Etale.inst`：∀ {R : Type u} [inst : CommRing R], Algebra.Etale R 
R
-/
lemma FormallySmooth.of_bijective {f : R →+* S} (hf : Function.Bijective f) :
    f.FormallySmooth := by
  algebraize [f]
  exact Algebra.FormallySmooth.of_equiv (AlgEquiv.ofBijective (Algebra.ofId R S) hf)
/-
**RingHom.FormallySmooth.holdsForLocalizationAway** 是 Mathlib 中的一个定理，位于命名空间 `Rin
gHom.FormallySmooth`。
形式化陈述：RingHom.HoldsForLocalizationAway @RingHom.FormallySmooth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RingHom.formallySmooth_algebraMap`：formallySmooth_algebraMap [Algebra R 
S] : (algebraMap R S).FormallySmooth ↔ Algebra.FormallySmooth R S
· 使用定理 `Algebra.FormallySmooth.of_isLocalization`：∀ {R : Type u_4} {Rₘ : Type u_
6} [inst : CommRing R] [inst_1 : CommRing Rₘ] (M : Submonoid R) [inst_2 : Algebr
a R Rₘ]   [IsLocalization M Rₘ…
-/
lemma FormallySmooth.holdsForLocalizationAway : HoldsForLocalizationAway @FormallySmooth :=
  fun _ _ _ _ _ r _ ↦ formallySmooth_algebraMap.mpr <| .of_isLocalization (.powers r)
/-
**RingHom.FormallySmooth.stableUnderComposition** 是 Mathlib 中的一个定理，位于命名空间 `RingH
om.FormallySmooth`。
形式化陈述：RingHom.StableUnderComposition @RingHom.FormallySmooth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.FormallySmooth.comp`：∀ {R : Type u_1} {S : Type u_2} [inst : Com
mRing R] [inst_1 : CommRing S] {T : Type u_3} [inst_2 : CommRing T]   {f : R →+*
 S} {g : S →+* T}…
-/
lemma FormallySmooth.stableUnderComposition : StableUnderComposition @FormallySmooth :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hf.comp hg
/-
**RingHom.FormallySmooth.respectsIso** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Formally
Smooth`。
形式化陈述：RingHom.RespectsIso @RingHom.FormallySmooth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.StableUnderComposition.respectsIso`：∀ {P : {R S : Type u} → [ins
t : CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.StableUnd
erComposition P →     (∀ {R S : …
· 使用定理 `RingHom.FormallySmooth.stableUnderComposition`：RingHom.StableUnderCompos
ition @RingHom.FormallySmooth
· 使用定理 `RingHom.HoldsForLocalizationAway.of_bijective`：RingHom.HoldsForLocalizat
ionAway.of_bijective (H : RingHom.HoldsForLocalizationAway P) (hf : Function.Bij
ective f) : P f
· 使用定理 `RingHom.FormallySmooth.holdsForLocalizationAway`：RingHom.HoldsForLocaliz
ationAway @RingHom.FormallySmooth
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
lemma FormallySmooth.respectsIso : RespectsIso @FormallySmooth :=
  stableUnderComposition.respectsIso fun e ↦ holdsForLocalizationAway.of_bijective _ _ e.bijective
/-
**RingHom.FormallySmooth.isStableUnderBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `Ring
Hom.FormallySmooth`。
形式化陈述：RingHom.IsStableUnderBaseChange @RingHom.FormallySmooth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsStableUnderBaseChange.mk`：∀ {P : {R S : Type u} → [inst : Comm
Ring R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P →  
   (∀ ⦃R S T : Type u⦄ […
· 使用定理 `RingHom.FormallySmooth.respectsIso`：RingHom.RespectsIso @RingHom.Formall
ySmooth
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.formallySmooth_algebraMap`：formallySmooth_algebraMap [Algebra R 
S] : (algebraMap R S).FormallySmooth ↔ Algebra.FormallySmooth R S
· 使用定理 `Algebra.FormallySmooth.instTensorProduct`：∀ {R : Type u_4} [inst : CommR
ing R] {A : Type u_5} [inst_1 : CommRing A] [inst_2 : Algebra R A] (B : Type u_6
)   [inst_3 : CommRing B] [ins…
-/
lemma FormallySmooth.isStableUnderBaseChange : IsStableUnderBaseChange @FormallySmooth := by
  refine .mk respectsIso ?_
  introv H
  rw [formallySmooth_algebraMap] at H ⊢
  infer_instance
/-
**RingHom.FormallySmooth.localizationPreserves** 是 Mathlib 中的一个定理，位于命名空间 `RingHo
m.FormallySmooth`。
形式化陈述：RingHom.LocalizationPreserves @RingHom.FormallySmooth
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用定理 `RingHom.FormallySmooth.isStableUnderBaseChange`：RingHom.IsStableUnderBas
eChange @RingHom.FormallySmooth
-/
lemma FormallySmooth.localizationPreserves : LocalizationPreserves @FormallySmooth :=
  isStableUnderBaseChange.localizationPreserves

/-- A ring homomorphism `f : R →+* S` is smooth if `S` is smooth as an `R` algebra. -/
@[algebraize RingHom.Smooth.toAlgebra]
/-
**RingHom.Smooth** 是 Mathlib 中的一个定义，位于命名空间 `RingHom`。
形式化陈述：Smooth (f : R ->+* S) : Prop
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `f : R →+* S` is smooth if `S` is smooth as an `R` algebra.
-/
def Smooth (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.Smooth R S

/-- Helper lemma for the `algebraize` tactic -/
/-
**RingHom.Smooth.toAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `RingHom.Smooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
{f : R →+* S}, f.Smooth → Algebra.Smooth R S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper lemma for the `algebraize` tactic
-/
lemma Smooth.toAlgebra {f : R →+* S} (hf : Smooth f) :
    @Algebra.Smooth R _ S _ f.toAlgebra := hf
/-
**RingHom.smooth_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：smooth_algebraMap [Algebra R S] : (algebraMap R S).Smooth ↔ Algebra.Smooth
 R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.Smooth.eq_1`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R]
 [inst_1 : CommRing S] (f : R →+* S), f.Smooth = Algebra.Smooth R S
· 使用定理 `toAlgebra_algebraMap`：∀ {R : Type u} {S : Type v} [inst : CommSemiring R
] [inst_1 : CommSemiring S] [inst_2 : Algebra R S],   (algebraMap R S).toAlgebra
 = inst_2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma smooth_algebraMap [Algebra R S] :
    (algebraMap R S).Smooth ↔ Algebra.Smooth R S := by
  rw [RingHom.Smooth, toAlgebra_algebraMap]
/-
**RingHom.smooth_def** 是 Mathlib 中的一个引理，位于命名空间 `RingHom`。
形式化陈述：smooth_def {f : R ->+* S} : f.Smooth ↔ f.FormallySmooth ∧ f.FinitePresenta
tion
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.smooth_iff`：∀ (R : Type u_4) [inst : CommRing R] (A : Type u) [i
nst_1 : CommRing A] [inst_2 : Algebra R A],   Algebra.Smooth R A ↔     autoParam
 (Algebr…
-/
lemma smooth_def {f : R →+* S} : f.Smooth ↔ f.FormallySmooth ∧ f.FinitePresentation :=
  letI := f.toAlgebra
  Algebra.smooth_iff _ _

namespace Smooth

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-
**RingHom.Smooth.formallySmooth** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smooth`。
形式化陈述：formallySmooth {f : R ->+* S} (hf : f.Smooth) : f.FormallySmooth
参数：hf : f.Smooth。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.smooth_def`：smooth_def {f : R ->+* S} : f.Smooth ↔ f.FormallySmo
oth ∧ f.FinitePresentation
-/
lemma formallySmooth {f : R →+* S} (hf : f.Smooth) : f.FormallySmooth := by
  rw [smooth_def] at hf
  exact hf.1
/-
**RingHom.Smooth.finitePresentation** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smooth`。
形式化陈述：finitePresentation {f : R ->+* S} (hf : f.Smooth) : f.FinitePresentation
参数：hf : f.Smooth。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.smooth_def`：smooth_def {f : R ->+* S} : f.Smooth ↔ f.FormallySmo
oth ∧ f.FinitePresentation
-/
lemma finitePresentation {f : R →+* S} (hf : f.Smooth) : f.FinitePresentation := by
  rw [smooth_def] at hf
  exact hf.2

/-- Composition of smooth ring homomorphisms is smooth. -/
/-
**RingHom.Smooth.comp** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smooth`。
形式化陈述：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Smooth) (hg : g.Smooth) : (g.co
mp f).Smooth
参数：hf : f.Smooth；hg : g.Smooth。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Algebra.Smooth.comp`：∀ (R : Type u_4) [inst : CommRing R] (A : Type u_5)
 (B : Type u_6) [inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : CommRin
g B] [ins…
· 使用定理 `RingHom.Smooth.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRi
ng R] [inst_1 : CommRing S] {f : R →+* S}, f.Smooth → Algebra.Smooth R S

--- 原说明 ---
Composition of smooth ring homomorphisms is smooth.
-/
lemma comp {f : R →+* S} {g : S →+* T} (hf : f.Smooth) (hg : g.Smooth) : (g.comp f).Smooth := by
  algebraize [f, g, g.comp f]
  exact Algebra.Smooth.comp R S T
/-
**RingHom.Smooth.stableUnderComposition** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smoot
h`。
形式化陈述：stableUnderComposition : StableUnderComposition Smooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.Smooth.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Smooth) 
(hg : g.Smooth) : (g.comp f).Smooth
-/
lemma stableUnderComposition : StableUnderComposition Smooth :=
  fun _ _ _ _ _ _ _ _ ↦ RingHom.Smooth.comp
/-
**RingHom.Smooth.isStableUnderBaseChange** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smoo
th`。
形式化陈述：isStableUnderBaseChange : IsStableUnderBaseChange Smooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.smooth_def`：smooth_def {f : R ->+* S} : f.Smooth ↔ f.FormallySmo
oth ∧ f.FinitePresentation
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `RingHom.IsStableUnderBaseChange.and`：∀ {P Q : {R S : Type u} → [inst : C
ommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.IsStableUnder
BaseChange fun {R S} [Com…
· 使用定理 `RingHom.FormallySmooth.isStableUnderBaseChange`：RingHom.IsStableUnderBas
eChange @RingHom.FormallySmooth
· 使用定理 `RingHom.finitePresentation_isStableUnderBaseChange`：finitePresentation_i
sStableUnderBaseChange : IsStableUnderBaseChange @FinitePresentation
-/
lemma isStableUnderBaseChange : IsStableUnderBaseChange Smooth := by
  convert!
    RingHom.FormallySmooth.isStableUnderBaseChange.and
      RingHom.finitePresentation_isStableUnderBaseChange
  rw [smooth_def]
/-
**RingHom.Smooth.holdsForLocalizationAway** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smo
oth`。
形式化陈述：holdsForLocalizationAway : HoldsForLocalizationAway Smooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.smooth_algebraMap`：smooth_algebraMap [Algebra R S] : (algebraMap
 R S).Smooth ↔ Algebra.Smooth R S
· 使用定理 `Algebra.FormallySmooth.of_isLocalization`：∀ {R : Type u_4} {Rₘ : Type u_
6} [inst : CommRing R] [inst_1 : CommRing Rₘ] (M : Submonoid R) [inst_2 : Algebr
a R Rₘ]   [IsLocalization M Rₘ…
· 使用定理 `IsLocalization.Away.finitePresentation`：IsLocalization.Away.finitePresen
tation (r : R) {S} [CommRing S] [Algebra R S] [IsLocalization.Away r S] : Algebr
a.FinitePresentation R S
-/
lemma holdsForLocalizationAway : HoldsForLocalizationAway Smooth := by
  introv R h
  rw [smooth_algebraMap]
  exact ⟨Algebra.FormallySmooth.of_isLocalization (.powers r),
    IsLocalization.Away.finitePresentation r⟩
/-
**RingHom.Smooth.of_bijective** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smooth`。
形式化陈述：of_bijective {f : R ->+* S} (hf : Function.Bijective f) : f.Smooth
参数：hf : Function.Bijective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.smooth_def`：smooth_def {f : R ->+* S} : f.Smooth ↔ f.FormallySmo
oth ∧ f.FinitePresentation
· 使用定理 `RingHom.FormallySmooth.of_bijective`：∀ {R : Type u_1} {S : Type u_2} [in
st : CommRing R] [inst_1 : CommRing S] {f : R →+* S},   Function.Bijective ⇑f → 
f.FormallySmooth
· 使用引理 `RingHom.FinitePresentation.of_bijective`：of_bijective {f : A ->+* B} (hf
 : Function.Bijective f) : f.FinitePresentation
-/
lemma of_bijective {f : R →+* S} (hf : Function.Bijective f) : f.Smooth := by
  rw [RingHom.smooth_def]
  exact ⟨.of_bijective hf, .of_bijective hf⟩

variable (R) in
/-- The identity of a ring is smooth. -/
/-
**RingHom.Smooth.id** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smooth`。
形式化陈述：id : RingHom.Smooth (RingHom.id R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.HoldsForLocalizationAway.containsIdentities`：RingHom.HoldsForLoc
alizationAway.containsIdentities (hPl : HoldsForLocalizationAway P) : ContainsId
entities P
· 使用引理 `RingHom.Smooth.holdsForLocalizationAway`：holdsForLocalizationAway : Hold
sForLocalizationAway Smooth

--- 原说明 ---
The identity of a ring is smooth.
-/
lemma id : RingHom.Smooth (RingHom.id R) :=
  holdsForLocalizationAway.containsIdentities R
/-
**RingHom.Smooth.ofLocalizationSpanTarget** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smo
oth`。
形式化陈述：ofLocalizationSpanTarget : OfLocalizationSpanTarget Smooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.finitePresentation_ofLocalizationSpanTarget`：finitePresentation_
ofLocalizationSpanTarget : OfLocalizationSpanTarget @FinitePresentation
· 使用引理 `RingHom.Smooth.finitePresentation`：finitePresentation {f : R ->+* S} (hf
 : f.Smooth) : f.FinitePresentation
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.smoothLocus_eq_univ_iff`：smoothLocus_eq_univ_iff [FinitePresenta
tion R A] : smoothLocus R A = Set.univ ↔ Algebra.FormallySmooth R A
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `TopologicalSpace.Opens.coe_top`：coe_top : ((⊤ : Opens α) : Set α) = Set.
univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PrimeSpectrum.iSup_basicOpen_eq_top_iff'`：iSup_basicOpen_eq_top_iff' {s 
: Set R} : (⨆ i in s, PrimeSpectrum.basicOpen i) = ⊤ ↔ Ideal.span s = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
-/
lemma ofLocalizationSpanTarget : OfLocalizationSpanTarget Smooth := by
  introv R hs hf
  have : f.FinitePresentation :=
    finitePresentation_ofLocalizationSpanTarget _ s hs fun r ↦ (hf r).finitePresentation
  algebraize [f]
  refine ⟨?_, ‹_›⟩
  rw [← Algebra.smoothLocus_eq_univ_iff, ← Set.univ_subset_iff, ← TopologicalSpace.Opens.coe_top,
    ← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs]
  simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subset_iff,
    Algebra.basicOpen_subset_smoothLocus_iff, ← formallySmooth_algebraMap]
  exact fun r hr ↦ (hf ⟨r, hr⟩).1

/-- Smoothness is a local property of ring homomorphisms. -/
/-
**RingHom.Smooth.propertyIsLocal** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smooth`。
形式化陈述：propertyIsLocal : PropertyIsLocal Smooth where localizationAwayPreserves
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用引理 `RingHom.IsStableUnderBaseChange.localizationPreserves`：RingHom.IsStableU
nderBaseChange.localizationPreserves : LocalizationPreserves P
· 使用引理 `RingHom.Smooth.isStableUnderBaseChange`：isStableUnderBaseChange : IsStab
leUnderBaseChange Smooth
· 使用引理 `RingHom.Smooth.ofLocalizationSpanTarget`：ofLocalizationSpanTarget : OfLo
calizationSpanTarget Smooth
· 使用定理 `RingHom.OfLocalizationSpanTarget.ofLocalizationSpan`：RingHom.OfLocalizat
ionSpanTarget.ofLocalizationSpan (hP : RingHom.OfLocalizationSpanTarget @P) (hP'
 : RingHom.StableUnderCompositionWithLoca…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAwa
y`：RingHom.StableUnderComposition.stableUnderCompositionWithLocalizationAway (hP
c : RingHom.StableUnderComposition P) (hPl : HoldsForLocalizati…
· 使用引理 `RingHom.Smooth.stableUnderComposition`：stableUnderComposition : StableUn
derComposition Smooth
· 使用引理 `RingHom.Smooth.holdsForLocalizationAway`：holdsForLocalizationAway : Hold
sForLocalizationAway Smooth
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Smoothness is a local property of ring homomorphisms.
-/
lemma propertyIsLocal : PropertyIsLocal Smooth where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right
/-
**RingHom.Smooth.respectsIso** 是 Mathlib 中的一个引理，位于命名空间 `RingHom.Smooth`。
形式化陈述：respectsIso : RespectsIso Smooth
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用引理 `RingHom.Smooth.propertyIsLocal`：propertyIsLocal : PropertyIsLocal Smooth
 where localizationAwayPreserves
-/
lemma respectsIso : RespectsIso Smooth :=
  propertyIsLocal.respectsIso

end RingHom.Smooth

