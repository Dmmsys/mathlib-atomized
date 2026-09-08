/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Injective
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!

# Being injective is a local property

## Main Results

* `Module.injective_of_isLocalizedModule` : For module `M` over Noetherian ring `R`,
  being injective is preserved under localization.

* `Module.injective_of_localization_maximal` : For module `M` over Noetherian ring `R`,
  being injective can be checked at localization at maximal ideals.

-/

universe u v

public section

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (S : Submonoid R)

section

universe u' v'

open IsLocalizedModule in
/-
**Module.injective_of_isLocalizedModule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.injective_of_isLocalizedModule [Small.{v} R] [IsNoetherianRing R] {
Rₛ : Type u'} [Small.{v'} Rₛ] [CommRing Rₛ] [Algebra R Rₛ] {Mₛ : Type v'} [AddCo
mmGroup Mₛ] [Module R Mₛ] [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (f : M ->ₗ[R] M
ₛ) [IsLocalization S Rₛ] [IsLocalizedModule S f] [Module.Injective R M] : Module
.Injective Rₛ Mₛ
参数：f : M ->ₗ[R] Mₛ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Baer.of_injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [i
nst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] [Small.{v, u} R],   Module.
Injective R Q …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.localized'_eq_map`：∀ {R : Type u_1} (S : Type u_2) [inst : CommSem
iring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   (p : Submonoid R) [i
nst_3 : IsLoc…
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Module.finitePresentation_of_finite`：Module.finitePresentation_of_finite
 [IsNoetherianRing R] [h : Module.Finite R M] : Module.FinitePresentation R M
· 使用定理 `Module.instFiniteSubtypeMemIdealOfIsNoetherian`：∀ {R₁ : Type u_5} {S : T
ype u_6} [inst : CommSemiring R₁] [inst_1 : Semiring S] [inst_2 : Algebra R₁ S] 
  [IsNoetherian R₁ S] (I : Ideal S),…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
· 使用定理 `LinearMap.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars R : (M ->ₗ[S] M₂) -> M ->ₗ[R] M₂)
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
（共 41 条，此处仅展示前 30 条）
-/
theorem Module.injective_of_isLocalizedModule [Small.{v} R] [IsNoetherianRing R] {Rₛ : Type u'}
    [Small.{v'} Rₛ] [CommRing Rₛ] [Algebra R Rₛ] {Mₛ : Type v'} [AddCommGroup Mₛ] [Module R Mₛ]
    [Module Rₛ Mₛ] [IsScalarTower R Rₛ Mₛ] (f : M →ₗ[R] Mₛ) [IsLocalization S Rₛ]
    [IsLocalizedModule S f] [Module.Injective R M] : Module.Injective Rₛ Mₛ := by
  have MB : Baer R M := Baer.of_injective ‹_›
  simp only [← Baer.iff_injective, Module.Baer.iff_surjective] at MB ⊢
  intro Iₛ g
  obtain ⟨I, rfl⟩ : ∃ I, .localized' Rₛ S (Algebra.linearMap R Rₛ) I = Iₛ :=
    ⟨Iₛ.comap (algebraMap R Rₛ), by simp [Ideal.localized'_eq_map, IsLocalization.map_under S]⟩
  have : FinitePresentation R I := finitePresentation_of_finite R I
  obtain ⟨⟨g', a⟩, e : a.1 • g = _⟩ := surj S (mapExtendScalars S (I.toLocalized' _ _ _) f Rₛ) g
  obtain ⟨g', rfl⟩ := MB I g'
  refine ⟨IsLocalization.mk' Rₛ 1 a • mapExtendScalars S (Algebra.linearMap _ _) f _ g', ?_⟩
  apply ((Module.End.isUnit_iff _).mp ((IsLocalization.map_units Rₛ a).map
    (algebraMap _ (Module.End Rₛ _)))).1
  simp_rw [algebraMap_end_apply, map_smul, ← mul_smul, algebraMap_smul, IsLocalization.mk'_spec', e]
  apply LinearMap.restrictScalars_injective R
  refine IsLocalizedModule.linearMap_ext S (I.toLocalized' Rₛ S (Algebra.linearMap R Rₛ)) f ?_
  ext
  simp [-Algebra.linearMap_apply]

end

/-
**Module.injective_of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.injective_of_localization_maximal [Small.{v} R] [IsNoetherianRing R
] (H : forall (I : Ideal R) (_ : I.IsMaximal), Module.Injective (Localization.At
Prime I) (LocalizedModule I.primeCompl M)) : Module.Injective R M
参数：H : forall (I : Ideal R) (_ : I.IsMaximal), Module.Injective (Localization.At
Prime I) (LocalizedModule I.primeCompl M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Baer.iff_injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [
inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] [Small.{v, u} R],   Module
.Baer R Q ↔ Mod…
· 使用引理 `Module.Baer.iff_surjective`：iff_surjective {R : Type u} [CommRing R] [Mo
dule R M] : Module.Baer R M ↔ forall (I : Ideal R), Function.Surjective (LinearM
ap.lcomp R M I.s…
· 使用引理 `Module.finitePresentation_of_finite`：Module.finitePresentation_of_finite
 [IsNoetherianRing R] [h : Module.Finite R M] : Module.FinitePresentation R M
· 使用定理 `Module.instFiniteSubtypeMemIdealOfIsNoetherian`：∀ {R₁ : Type u_5} {S : T
ype u_6} [inst : CommSemiring R₁] [inst_1 : Semiring S] [inst_2 : Algebra R₁ S] 
  [IsNoetherian R₁ S] (I : Ideal S),…
· 使用定理 `surjective_of_localized_maximal`：surjective_of_localized_maximal (h : fo
rall (J : Ideal R) [J.IsMaximal], Function.Surjective (map J.primeCompl f)) : Fu
nction.Surjective f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsLocalizedModule.ext`：ext (map_unit : forall x : S, IsUnit ((algebraMap
 R (Module.End R M'')) x)) ⦃j k : M' ->ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j =
 k
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.toLocalized'_apply_coe`：∀ {R : Type u_1} (S : Type u_2) {M : T
ype u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [ins
t_2 : AddCommMonoid M]…
· 使用引理 `IsLocalizedModule.map_apply`：map_apply (h : M ->ₗ[R] N) (x) : map S f g 
h (f x) = g (h x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `instFinitePresentation`：∀ {R : Type u_1} [inst : Ring R], Module.FiniteP
resentation R R
· 使用定理 `LinearMap.restrictScalars_injective`：restrictScalars_injective : Functio
n.Injective (restrictScalars R : (M ->ₗ[S] M₂) -> M ->ₗ[R] M₂)
· 使用定理 `IsLocalizedModule.mapExtendScalars_apply_apply`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddC
ommMonoid M]   [inst_2 : AddCommMono…
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.restrictScalars.congr_simp`：∀ (R : Type u_1) {S : Type u_5} {M
 : Type u_8} {M₂ : Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_
2 : AddCommMonoid M] [inst…
（共 37 条，此处仅展示前 30 条）
-/
theorem Module.injective_of_localization_maximal [Small.{v} R] [IsNoetherianRing R]
    (H : ∀ (I : Ideal R) (_ : I.IsMaximal),
      Module.Injective (Localization.AtPrime I) (LocalizedModule I.primeCompl M)) :
    Module.Injective R M := by
  rw [← Baer.iff_injective, Baer.iff_surjective]
  intro I
  let _ : FinitePresentation R I := finitePresentation_of_finite R I
  apply surjective_of_localized_maximal _ (fun m _ ↦ ?_)
  let Rₘ := Localization.AtPrime m
  let Mₘ := LocalizedModule m.primeCompl M
  let f := LocalizedModule.mkLinearMap m.primeCompl M
  let h : R →ₗ[R] Rₘ := Algebra.linearMap R Rₘ
  let Iₘ : Ideal Rₘ := Submodule.localized' Rₘ m.primeCompl h I
  let g : I →ₗ[R] Iₘ := I.toLocalized' Rₘ m.primeCompl h
  let gM := IsLocalizedModule.mapExtendScalars m.primeCompl g f Rₘ
  let hM := IsLocalizedModule.mapExtendScalars m.primeCompl h f Rₘ
  have eq'' : Iₘ.subtype.restrictScalars R = IsLocalizedModule.map m.primeCompl g h I.subtype :=
    IsLocalizedModule.ext m.primeCompl g (IsLocalizedModule.map_units h) (by ext; simp [g, h, Iₘ])
  have eq' : (Iₘ.subtype.lcomp Rₘ Mₘ).restrictScalars R =
    IsLocalizedModule.map m.primeCompl hM gM (I.subtype.lcomp R M) :=
    IsLocalizedModule.ext m.primeCompl hM (IsLocalizedModule.map_units gM) <| LinearMap.ext
      fun l ↦ LinearMap.restrictScalars_injective R (IsLocalizedModule.ext m.primeCompl g
        (IsLocalizedModule.map_units f) (by ext; simp +zetaDelta [-Algebra.linearMap_apply]))
  have eq : Iₘ.subtype.lcomp Rₘ Mₘ = IsLocalizedModule.mapExtendScalars m.primeCompl hM gM Rₘ
    (I.subtype.lcomp R M) := by
    simp [IsLocalizedModule.mapExtendScalars, ← eq']
  have MB : Baer Rₘ Mₘ := Baer.of_injective (H m ‹_›)
  have surj : Function.Surjective (LinearMap.lcomp Rₘ Mₘ (Submodule.subtype Iₘ)) :=
    Baer.iff_surjective.mp MB Iₘ
  rw [eq] at surj
  rw [← LinearMap.coe_restrictScalars (R := R),
    LocalizedModule.restrictScalars_map_eq m.primeCompl hM gM]
  simpa using! surj

section

universe u' v'

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type u')
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Small.{v'} (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type v')
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]

set_option backward.defeqAttrib.useBackward true in
attribute [local instance] RingHomInvPair.of_ringEquiv in
include f in
/--
A variant of `Module.injective_of_localization_maximal` that accepts `IsLocalizedModule`.
-/
/-
**Module.injective_of_localization_maximal'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.injective_of_localization_maximal' [Small.{v} R] [IsNoetherianRing 
R] (H : forall (I : Ideal R) (_ : I.IsMaximal), Module.Injective (Rₚ I) (Mₚ I)) 
: Module.Injective R M
参数：H : forall (I : Ideal R) (_ : I.IsMaximal), Module.Injective (Rₚ I) (Mₚ I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.injective_of_localization_maximal`：Module.injective_of_localizati
on_maximal [Small.{v} R] [IsNoetherianRing R] (H : forall (I : Ideal R) (_ : I.I
sMaximal), Module.Injective (L…
· 使用定理 `Module.Injective.of_ringEquiv`：Module.Injective.of_ringEquiv {R : Type u
} [Ring R] [Small.{v} R] {S : Type u'} [Ring S] {M : Type v} {N : Type v'} [AddC
ommGroup M] [AddCom…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `RingHomInvPair.of_ringEquiv`：of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPa
ir (↑e : R₁ ->+* R₂) ↑e.symm
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.smul_mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsLocalization.map_id_mk'`：map_id_mk' {Q : Type*} [CommSemiring Q] [Alge
bra R Q] [IsLocalization M Q] (x) (y : M) : map Q (RingHom.id R) (le_refl M) (mk
' S x y) = mk' …
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…

--- 原说明 ---
A variant of `Module.injective_of_localization_maximal` that accepts `IsLocalize
dModule`.
-/
theorem Module.injective_of_localization_maximal' [Small.{v} R] [IsNoetherianRing R]
    (H : ∀ (I : Ideal R) (_ : I.IsMaximal), Module.Injective (Rₚ I) (Mₚ I)) :
    Module.Injective R M := by
  apply Module.injective_of_localization_maximal
  intro P hP
  refine Module.Injective.of_ringEquiv (M := Mₚ P)
    (IsLocalization.algEquiv P.primeCompl (Rₚ P) (Localization.AtPrime P)).toRingEquiv
    { __ := IsLocalizedModule.linearEquiv P.primeCompl (f P)
        (LocalizedModule.mkLinearMap P.primeCompl M)
      map_smul' := ?_ }
  · intro r m
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl r
    apply ((Module.End.isUnit_iff _).mp
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap P.primeCompl M) s)).1
    dsimp
    simp only [← map_smul, ← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul,
      IsLocalization.map_id_mk']

end

