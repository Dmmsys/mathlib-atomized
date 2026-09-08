/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su, Yongle Hu, Yi Song
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime

/-!
# Local properties about linear maps

In this file, we show that
injectivity, surjectivity, bijectivity and exactness of linear maps are local properties.
More precisely, we show that these can be checked at maximal ideals and on standard covers.
-/

public section

open Submodule LocalizedModule Ideal LinearMap

section isLocalized_maximal

open IsLocalizedModule

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L]

-- For every maximal ideal `p` of `R`, let `Mₚ` (resp. `Nₚ`, resp. `Lₚ`) the localizations
-- of `M` (resp. `N`, resp. `L`) at `p`.
variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P)]
  (Nₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Nₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Nₚ P)]
  (g : ∀ (P : Ideal R) [P.IsMaximal], N →ₗ[R] Nₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (g P)]
  (Lₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Lₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Lₚ P)]
  (h : ∀ (P : Ideal R) [P.IsMaximal], L →ₗ[R] Lₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (h P)]
  (F : M →ₗ[R] N) (G : N →ₗ[R] L)

/-
**injective_of_isLocalized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_of_isLocalized_maximal (H : forall (P : Ideal R) [P.IsMaximal], 
Function.Injective (map P.primeCompl (f P) (g P) F)) : Function.Injective F
参数：H : forall (P : Ideal R) [P.IsMaximal], Function.Injective (map P.primeCompl 
(f P) (g P) F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.eq_of_localization_maximal`：Module.eq_of_localization_maximal (m 
m' : M) (h : forall (P : Ideal R) [P.IsMaximal], f P m = f P m') : m = m'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.map_apply`：map_apply (h : M ->ₗ[R] N) (x) : map S f g 
h (f x) = g (h x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem injective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Function.Injective (map P.primeCompl (f P) (g P) F)) :
    Function.Injective F :=
  fun x y eq ↦ Module.eq_of_localization_maximal _ f _ _ fun P _ ↦ H P <| by simp [eq]
/-
**surjective_of_isLocalized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_of_isLocalized_maximal (H : forall (P : Ideal R) [P.IsMaximal],
 Function.Surjective (map P.primeCompl (f P) (g P) F)) : Function.Surjective F
参数：H : forall (P : Ideal R) [P.IsMaximal], Function.Surjective (map P.primeCompl
 (f P) (g P) F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.eq_top_of_localization₀_maximal`：Submodule.eq_top_of_localizat
ion₀_maximal (N : Submodule R M) (h : forall (P : Ideal R) [P.IsMaximal], N.loca
lized₀ P.primeCompl (f P) = ⊤) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.range_localizedMap_eq_localized₀_range`：range_localizedMap_eq_
localized₀_range (g : M ->ₗ[R] P) : range (map p f f' g) = (range g).localized₀ 
p f'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem surjective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Function.Surjective (map P.primeCompl (f P) (g P) F)) :
    Function.Surjective F :=
  range_eq_top.mp <| eq_top_of_localization₀_maximal Nₚ g _ <|
    fun P _ ↦ (range_localizedMap_eq_localized₀_range _ (f P) (g P) F).symm.trans <|
    range_eq_top.mpr <| H P
/-
**bijective_of_isLocalized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bijective_of_isLocalized_maximal (H : forall (P : Ideal R) [P.IsMaximal], 
Function.Bijective (map P.primeCompl (f P) (g P) F)) : Function.Bijective F
参数：H : forall (P : Ideal R) [P.IsMaximal], Function.Bijective (map P.primeCompl 
(f P) (g P) F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `injective_of_isLocalized_maximal`：injective_of_isLocalized_maximal (H : 
forall (P : Ideal R) [P.IsMaximal], Function.Injective (map P.primeCompl (f P) (
g P) F)) : Function.In…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `surjective_of_isLocalized_maximal`：surjective_of_isLocalized_maximal (H 
: forall (P : Ideal R) [P.IsMaximal], Function.Surjective (map P.primeCompl (f P
) (g P) F)) : Function.…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem bijective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) [P.IsMaximal], Function.Bijective (map P.primeCompl (f P) (g P) F)) :
    Function.Bijective F :=
  ⟨injective_of_isLocalized_maximal Mₚ f Nₚ g F fun J _ ↦ (H J).1,
  surjective_of_isLocalized_maximal Mₚ f Nₚ g F fun J _ ↦ (H J).2⟩
/-
**exact_of_isLocalized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exact_of_isLocalized_maximal (H : forall (J : Ideal R) [J.IsMaximal], Func
tion.Exact (map J.primeCompl (f J) (g J) F) (map J.primeCompl (g J) (h J) G)) : 
Function.Exact F G
参数：H : forall (J : Ideal R) [J.IsMaximal], Function.Exact (map J.primeCompl (f J
) (g J) F) (map J.primeCompl (g J) (h J) G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Submodule.eq_of_localization₀_maximal`：Submodule.eq_of_localization₀_max
imal {N₁ N₂ : Submodule R M} (h : forall (P : Ideal R) [P.IsMaximal], N₁.localiz
ed₀ P.primeCompl (f P) = N₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.range_localizedMap_eq_localized₀_range`：range_localizedMap_eq_
localized₀_range (g : M ->ₗ[R] P) : range (map p f f' g) = (range g).localized₀ 
p f'
· 使用引理 `LinearMap.ker_localizedMap_eq_localized₀_ker`：ker_localizedMap_eq_locali
zed₀_ker (g : M ->ₗ[R] P) : ker (map p f f' g) = (ker g).localized₀ p f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem exact_of_isLocalized_maximal (H : ∀ (J : Ideal R) [J.IsMaximal],
    Function.Exact (map J.primeCompl (f J) (g J) F) (map J.primeCompl (g J) (h J) G)) :
    Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply eq_of_localization₀_maximal Nₚ g
  intro J hJ
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f J) (g J) F,
    ← LinearMap.ker_localizedMap_eq_localized₀_ker J.primeCompl (g J) (h J) G]
  have := SetLike.ext_iff.mp <| H J
  ext x
  simp only [mem_range, mem_ker] at this ⊢
  exact this x
/-
**LinearIndependent.of_isLocalized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.of_isLocalized_maximal {ι} (v : ι -> M) (H : forall (P :
 Ideal R) [P.IsMaximal], LinearIndependent (Rₚ P) (f P ∘ v)) : LinearIndependent
 R v
参数：v : ι -> M；H : forall (P : Ideal R) [P.IsMaximal], LinearIndependent (Rₚ P) (
f P ∘ v)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `injective_of_isLocalized_maximal`：injective_of_isLocalized_maximal (H : 
forall (P : Ideal R) [P.IsMaximal], Function.Injective (map P.primeCompl (f P) (
g P) F)) : Function.In…
· 使用定理 `instIsLocalizedModuleFinsuppLinearMap`：∀ (R : Type u_1) [inst : CommSemi
ring R] (S : Submonoid R) (M : Type u_3) [inst_1 : AddCommMonoid M]   [inst_2 : 
_root_.Module R M] {M' : Ty…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `LinearMap.CompatibleSMul.finsupp_dom`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.map_linearCombination`：IsLocalizedModule.map_linearCom
bination {α : Type*} {v : α -> M} [IsLocalizedModule S f] : map S (mapRange.line
arMap (Algebra.linearMap R A)…
-/
theorem LinearIndependent.of_isLocalized_maximal {ι} (v : ι → M)
    (H : ∀ (P : Ideal R) [P.IsMaximal], LinearIndependent (Rₚ P) (f P ∘ v)) :
    LinearIndependent R v :=
  injective_of_isLocalized_maximal _ (fun P _ ↦ Finsupp.mapRange.linearMap <|
    Algebra.linearMap R (Rₚ P)) _ f _ fun P _ ↦ by rw [map_linearCombination]; exact H P

end isLocalized_maximal

section localized_maximal

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L] (f : M →ₗ[R] N) (g : N →ₗ[R] L)

/-
**injective_of_localized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_of_localized_maximal (h : forall (J : Ideal R) [J.IsMaximal], Fu
nction.Injective (map J.primeCompl f)) : Function.Injective f
参数：h : forall (J : Ideal R) [J.IsMaximal], Function.Injective (map J.primeCompl 
f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `injective_of_isLocalized_maximal`：injective_of_isLocalized_maximal (H : 
forall (P : Ideal R) [P.IsMaximal], Function.Injective (map P.primeCompl (f P) (
g P) F)) : Function.In…
-/
theorem injective_of_localized_maximal
    (h : ∀ (J : Ideal R) [J.IsMaximal], Function.Injective (map J.primeCompl f)) :
    Function.Injective f :=
  injective_of_isLocalized_maximal _ (fun _ _ ↦ mkLinearMap _ _) _ (fun _ _ ↦ mkLinearMap _ _) f h
/-
**surjective_of_localized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_of_localized_maximal (h : forall (J : Ideal R) [J.IsMaximal], F
unction.Surjective (map J.primeCompl f)) : Function.Surjective f
参数：h : forall (J : Ideal R) [J.IsMaximal], Function.Surjective (map J.primeCompl
 f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `surjective_of_isLocalized_maximal`：surjective_of_isLocalized_maximal (H 
: forall (P : Ideal R) [P.IsMaximal], Function.Surjective (map P.primeCompl (f P
) (g P) F)) : Function.…
-/
theorem surjective_of_localized_maximal
    (h : ∀ (J : Ideal R) [J.IsMaximal], Function.Surjective (map J.primeCompl f)) :
    Function.Surjective f :=
  surjective_of_isLocalized_maximal _ (fun _ _ ↦ mkLinearMap _ _) _ (fun _ _ ↦ mkLinearMap _ _) f h
/-
**bijective_of_localized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bijective_of_localized_maximal (h : forall (J : Ideal R) [J.IsMaximal], Fu
nction.Bijective (map J.primeCompl f)) : Function.Bijective f
参数：h : forall (J : Ideal R) [J.IsMaximal], Function.Bijective (map J.primeCompl 
f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `injective_of_localized_maximal`：injective_of_localized_maximal (h : fora
ll (J : Ideal R) [J.IsMaximal], Function.Injective (map J.primeCompl f)) : Funct
ion.Injective f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `surjective_of_localized_maximal`：surjective_of_localized_maximal (h : fo
rall (J : Ideal R) [J.IsMaximal], Function.Surjective (map J.primeCompl f)) : Fu
nction.Surjective f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem bijective_of_localized_maximal
    (h : ∀ (J : Ideal R) [J.IsMaximal], Function.Bijective (map J.primeCompl f)) :
    Function.Bijective f :=
  ⟨injective_of_localized_maximal _ fun J _ ↦ (h J).1,
  surjective_of_localized_maximal _ fun J _ ↦ (h J).2⟩
/-
**exact_of_localized_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exact_of_localized_maximal (h : forall (J : Ideal R) [J.IsMaximal], Functi
on.Exact (map J.primeCompl f) (map J.primeCompl g)) : Function.Exact f g
参数：h : forall (J : Ideal R) [J.IsMaximal], Function.Exact (map J.primeCompl f) (
map J.primeCompl g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `exact_of_isLocalized_maximal`：exact_of_isLocalized_maximal (H : forall (
J : Ideal R) [J.IsMaximal], Function.Exact (map J.primeCompl (f J) (g J) F) (map
 J.primeCompl (g J…
-/
theorem exact_of_localized_maximal
    (h : ∀ (J : Ideal R) [J.IsMaximal], Function.Exact (map J.primeCompl f) (map J.primeCompl g)) :
    Function.Exact f g :=
  exact_of_isLocalized_maximal _ (fun _ _ ↦ mkLinearMap _ _) _ (fun _ _ ↦ mkLinearMap _ _)
    _ (fun _ _ ↦ mkLinearMap _ _) f g h

end localized_maximal

section isLocalized_span

open IsLocalizedModule

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L] (s : Set R) (spn : Ideal.span s = ⊤)
include spn

-- For every element `r ∈ s`, let `Mᵣ` (resp. `Nᵣ`, resp. `Lᵣ`) the localizations
-- of `M` (resp. `N`, resp. `L`) away from `r`.
variable
  (Mₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Mₚ r)]
  [∀ r : s, Module R (Mₚ r)]
  (f : ∀ r : s, M →ₗ[R] Mₚ r)
  [∀ r : s, IsLocalizedModule.Away r.1 (f r)]
  (Nₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Nₚ r)]
  [∀ r : s, Module R (Nₚ r)]
  (g : ∀ r : s, N →ₗ[R] Nₚ r)
  [∀ r : s, IsLocalizedModule.Away r.1 (g r)]
  (Lₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Lₚ r)]
  [∀ r : s, Module R (Lₚ r)]
  (h : ∀ r : s, L →ₗ[R] Lₚ r)
  [∀ r : s, IsLocalizedModule.Away r.1 (h r)]
  (F : M →ₗ[R] N) (G : N →ₗ[R] L)

/-
**injective_of_isLocalized_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_of_isLocalized_span (H : forall r : s, Function.Injective (map (
.powers r.1) (f r) (g r) F)) : Function.Injective F
参数：H : forall r : s, Function.Injective (map (.powers r.1) (f r) (g r) F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.eq_of_isLocalized_span`：Module.eq_of_isLocalized_span (x y : M) (
h : forall r : s, f r x = f r y) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.map_apply`：map_apply (h : M ->ₗ[R] N) (x) : map S f g 
h (f x) = g (h x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem injective_of_isLocalized_span
    (H : ∀ r : s, Function.Injective (map (.powers r.1) (f r) (g r) F)) :
    Function.Injective F :=
  fun x y eq ↦ Module.eq_of_isLocalized_span _ spn _ f _ _ fun P ↦ H P <| by simp [eq]
/-
**surjective_of_isLocalized_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_of_isLocalized_span (H : forall r : s, Function.Surjective (map
 (.powers r.1) (f r) (g r) F)) : Function.Surjective F
参数：H : forall r : s, Function.Surjective (map (.powers r.1) (f r) (g r) F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.eq_top_of_isLocalized₀_span`：Submodule.eq_top_of_isLocalized₀_
span {N : Submodule R M} (h : forall r : s, N.localized₀ (.powers r.1) (f r) = ⊤
) : N = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.range_localizedMap_eq_localized₀_range`：range_localizedMap_eq_
localized₀_range (g : M ->ₗ[R] P) : range (map p f f' g) = (range g).localized₀ 
p f'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem surjective_of_isLocalized_span
    (H : ∀ r : s, Function.Surjective (map (.powers r.1) (f r) (g r) F)) :
    Function.Surjective F :=
  range_eq_top.mp <| eq_top_of_isLocalized₀_span s spn Nₚ g fun r ↦
    (range_localizedMap_eq_localized₀_range _ (f r) (g r) F).symm.trans <| range_eq_top.mpr <| H r
/-
**bijective_of_isLocalized_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bijective_of_isLocalized_span (H : forall r : s, Function.Bijective (map (
.powers r.1) (f r) (g r) F)) : Function.Bijective F
参数：H : forall r : s, Function.Bijective (map (.powers r.1) (f r) (g r) F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `injective_of_isLocalized_span`：injective_of_isLocalized_span (H : forall
 r : s, Function.Injective (map (.powers r.1) (f r) (g r) F)) : Function.Injecti
ve F
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `surjective_of_isLocalized_span`：surjective_of_isLocalized_span (H : fora
ll r : s, Function.Surjective (map (.powers r.1) (f r) (g r) F)) : Function.Surj
ective F
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem bijective_of_isLocalized_span
    (H : ∀ r : s, Function.Bijective (map (.powers r.1) (f r) (g r) F)) :
    Function.Bijective F :=
  ⟨injective_of_isLocalized_span _ spn Mₚ f Nₚ g F fun r ↦ (H r).1,
  surjective_of_isLocalized_span _ spn Mₚ f Nₚ g F fun r ↦ (H r).2⟩
/-
**exact_of_isLocalized_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exact_of_isLocalized_span (H : forall r : s, Function.Exact (map (.powers 
r.1) (f r) (g r) F) (map (.powers r.1) (g r) (h r) G)) : Function.Exact F G
参数：H : forall r : s, Function.Exact (map (.powers r.1) (f r) (g r) F) (map (.pow
ers r.1) (g r) (h r) G)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.eq_of_isLocalized₀_span`：Submodule.eq_of_isLocalized₀_span {N 
P : Submodule R M} (h : forall r : s, N.localized₀ (.powers r.1) (f r) = P.local
ized₀ (.powers r.1) (f …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.range_localizedMap_eq_localized₀_range`：range_localizedMap_eq_
localized₀_range (g : M ->ₗ[R] P) : range (map p f f' g) = (range g).localized₀ 
p f'
· 使用引理 `LinearMap.ker_localizedMap_eq_localized₀_ker`：ker_localizedMap_eq_locali
zed₀_ker (g : M ->ₗ[R] P) : ker (map p f f' g) = (ker g).localized₀ p f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma exact_of_isLocalized_span (H : ∀ r : s, Function.Exact
    (map (.powers r.1) (f r) (g r) F) (map (.powers r.1) (g r) (h r) G)) :
    Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply Submodule.eq_of_isLocalized₀_span s spn Nₚ g
  intro r
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f r) (g r) F]
  rw [← LinearMap.ker_localizedMap_eq_localized₀_ker (.powers r.1) (g r) (h r) G]
  have := SetLike.ext_iff.mp <| H r
  ext x
  simp only [mem_range, mem_ker] at this ⊢
  exact this x

end isLocalized_span

section localized_span

variable {R M N L : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L]
  (s : Set R) (spn : span s = ⊤) (f : M →ₗ[R] N) (g : N →ₗ[R] L)
include spn

/-
**injective_of_localized_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_of_localized_span (h : forall r : s, Function.Injective (map (.p
owers r.1) f)) : Function.Injective f
参数：h : forall r : s, Function.Injective (map (.powers r.1) f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `injective_of_isLocalized_span`：injective_of_isLocalized_span (H : forall
 r : s, Function.Injective (map (.powers r.1) (f r) (g r) F)) : Function.Injecti
ve F
-/
theorem injective_of_localized_span
    (h : ∀ r : s, Function.Injective (map (.powers r.1) f)) :
    Function.Injective f :=
  injective_of_isLocalized_span s spn _ (fun _ ↦ mkLinearMap _ _) _ (fun _ ↦ mkLinearMap _ _) f h
/-
**surjective_of_localized_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_of_localized_span (h : forall r : s, Function.Surjective (map (
.powers r.1) f)) : Function.Surjective f
参数：h : forall r : s, Function.Surjective (map (.powers r.1) f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `surjective_of_isLocalized_span`：surjective_of_isLocalized_span (H : fora
ll r : s, Function.Surjective (map (.powers r.1) (f r) (g r) F)) : Function.Surj
ective F
-/
theorem surjective_of_localized_span
    (h : ∀ r : s, Function.Surjective (map (.powers r.1) f)) :
    Function.Surjective f :=
  surjective_of_isLocalized_span s spn _ (fun _ ↦ mkLinearMap _ _) _ (fun _ ↦ mkLinearMap _ _) f h
/-
**bijective_of_localized_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bijective_of_localized_span (h : forall r : s, Function.Bijective (map (.p
owers r.1) f)) : Function.Bijective f
参数：h : forall r : s, Function.Bijective (map (.powers r.1) f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `injective_of_localized_span`：injective_of_localized_span (h : forall r :
 s, Function.Injective (map (.powers r.1) f)) : Function.Injective f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `surjective_of_localized_span`：surjective_of_localized_span (h : forall r
 : s, Function.Surjective (map (.powers r.1) f)) : Function.Surjective f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem bijective_of_localized_span
    (h : ∀ r : s, Function.Bijective (map (.powers r.1) f)) :
    Function.Bijective f :=
  ⟨injective_of_localized_span _ spn _ fun r ↦ (h r).1,
  surjective_of_localized_span _ spn _ fun r ↦ (h r).2⟩
/-
**exact_of_localized_span** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exact_of_localized_span (h : forall r : s, Function.Exact (map (.powers r.
1) f) (map (.powers r.1) g)) : Function.Exact f g
参数：h : forall r : s, Function.Exact (map (.powers r.1) f) (map (.powers r.1) g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用引理 `exact_of_isLocalized_span`：exact_of_isLocalized_span (H : forall r : s, 
Function.Exact (map (.powers r.1) (f r) (g r) F) (map (.powers r.1) (g r) (h r) 
G)) : Function.…
-/
lemma exact_of_localized_span
    (h : ∀ r : s, Function.Exact (map (.powers r.1) f) (map (.powers r.1) g)) :
    Function.Exact f g :=
  exact_of_isLocalized_span s spn _ (fun _ ↦ mkLinearMap _ _) _ (fun _ ↦ mkLinearMap _ _)
    _ (fun _ ↦ mkLinearMap _ _) f g h

end localized_span

section Algebra

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

-- For every maximal ideal `p` of `R`, let `Rₚ` be the localization of `R` at `p`
-- and `Sₚ` the localization of `S` at `p`.
variable
  (Rₚ : ∀ (p : Ideal R) [p.IsMaximal], Type*)
  [∀ (p : Ideal R) [p.IsMaximal], CommSemiring (Rₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra R (Rₚ p)]
  (Sₚ : ∀ (p : Ideal R) [p.IsMaximal], Type*)
  [∀ (p : Ideal R) [p.IsMaximal], CommSemiring (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra S (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra (Rₚ p) (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], Algebra R (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], IsScalarTower R (Rₚ p) (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], IsScalarTower R S (Sₚ p)]
  [∀ (p : Ideal R) [p.IsMaximal], IsLocalization.AtPrime (Rₚ p) p]
  [∀ (p : Ideal R) [p.IsMaximal],
    IsLocalizedModule.AtPrime p (IsScalarTower.toAlgHom R S (Sₚ p) : S →ₗ[R] (Sₚ p))]

open TensorProduct

/-
**IsLocalizedModule.map_linearMap_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：IsLocalizedModule.map_linearMap_of_isLocalization (Rₚ Sₚ : Type*) [CommSem
iring Rₚ] [Algebra R Rₚ] [CommSemiring Sₚ] [Algebra S Sₚ] [Algebra R Sₚ] [IsScal
arTower R S Sₚ] [Algebra Rₚ Sₚ] [IsScalarTower R Rₚ Sₚ] (p : Ideal R) [p.IsPrime
] [IsLocalization.AtPrime Rₚ p] [IsLocalizedModule.AtPrime p (IsScalarTower.toAl
gHom R S Sₚ : S ->ₗ[R] Sₚ)] : IsLocalizedModule.map p.primeCompl (Algebra.linear
Map R Rₚ) (IsScalarTower.toAlgHom R S Sₚ : S ->ₗ[R] Sₚ) (Algebra.linearMap R S) 
= (Algebra.linearMap Rₚ Sₚ
参数：Rₚ Sₚ : Type*；p : Ideal R；IsScalarTower.toAlgHom R S Sₚ : S ->ₗ[R] Sₚ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `IsLocalizedModule.linearMap_ext`：linearMap_ext {N N'} [AddCommMonoid N] 
[Module R N] [AddCommMonoid N'] [Module R N'] (f' : N ->ₗ[R] N') [IsLocalizedMod
ule S f'] ⦃g g' : M' …
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsLocalizedModule.map_apply`：map_apply (h : M ->ₗ[R] N) (x) : map S f g 
h (f x) = g (h x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma IsLocalizedModule.map_linearMap_of_isLocalization (Rₚ Sₚ : Type*) [CommSemiring Rₚ]
    [Algebra R Rₚ] [CommSemiring Sₚ] [Algebra S Sₚ] [Algebra R Sₚ] [IsScalarTower R S Sₚ]
    [Algebra Rₚ Sₚ] [IsScalarTower R Rₚ Sₚ] (p : Ideal R) [p.IsPrime]
    [IsLocalization.AtPrime Rₚ p]
    [IsLocalizedModule.AtPrime p (IsScalarTower.toAlgHom R S Sₚ : S →ₗ[R] Sₚ)] :
    IsLocalizedModule.map p.primeCompl (Algebra.linearMap R Rₚ)
        (IsScalarTower.toAlgHom R S Sₚ : S →ₗ[R] Sₚ) (Algebra.linearMap R S) =
    (Algebra.linearMap Rₚ Sₚ).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext p.primeCompl (Algebra.linearMap _ _)
    (IsScalarTower.toAlgHom R S Sₚ : S →ₗ[R] Sₚ)
  ext
  simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, map_one,
    LinearMap.coe_restrictScalars]
  rw [show 1 = Algebra.linearMap R Rₚ 1 by simp, IsLocalizedModule.map_apply]
  simp
/-
**injective_of_isLocalization_isMaximal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：injective_of_isLocalization_isMaximal (H : forall (p : Ideal R) [p.IsMaxim
al], Function.Injective (algebraMap (Rₚ p) (Sₚ p))) : Function.Injective (algebr
aMap R S)
参数：H : forall (p : Ideal R) [p.IsMaximal], Function.Injective (algebraMap (Rₚ p)
 (Sₚ p))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `injective_of_isLocalized_maximal`：injective_of_isLocalized_maximal (H : 
forall (P : Ideal R) [P.IsMaximal], Function.Injective (map P.primeCompl (f P) (
g P) F)) : Function.In…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
· 使用引理 `IsLocalizedModule.map_linearMap_of_isLocalization`：IsLocalizedModule.map
_linearMap_of_isLocalization (Rₚ Sₚ : Type*) [CommSemiring Rₚ] [Algebra R Rₚ] [C
ommSemiring Sₚ] [Algebra S Sₚ] [Algebra…
-/
lemma injective_of_isLocalization_isMaximal
    (H : ∀ (p : Ideal R) [p.IsMaximal], Function.Injective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Injective (algebraMap R S) := by
  apply injective_of_isLocalized_maximal (fun P _ ↦ Rₚ P) (fun P _ ↦ Algebra.linearMap _ _)
    (fun P _ ↦ Sₚ P) (fun P _ ↦ IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Injective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw [DFunLike.coe_fn_eq]
    apply IsLocalizedModule.map_linearMap_of_isLocalization
  · exact H p
/-
**surjective_of_isLocalization_isMaximal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：surjective_of_isLocalization_isMaximal (H : forall (p : Ideal R) [p.IsMaxi
mal], Function.Surjective (algebraMap (Rₚ p) (Sₚ p))) : Function.Surjective (alg
ebraMap R S)
参数：H : forall (p : Ideal R) [p.IsMaximal], Function.Surjective (algebraMap (Rₚ p
) (Sₚ p))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `surjective_of_isLocalized_maximal`：surjective_of_isLocalized_maximal (H 
: forall (P : Ideal R) [P.IsMaximal], Function.Surjective (map P.primeCompl (f P
) (g P) F)) : Function.…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFunLike.coe_fn_eq`：coe_fn_eq {f g : F} : (f : forall a : α, β a) = (g :
 forall a : α, β a) ↔ f = g
· 使用引理 `IsLocalizedModule.map_linearMap_of_isLocalization`：IsLocalizedModule.map
_linearMap_of_isLocalization (Rₚ Sₚ : Type*) [CommSemiring Rₚ] [Algebra R Rₚ] [C
ommSemiring Sₚ] [Algebra S Sₚ] [Algebra…
-/
lemma surjective_of_isLocalization_isMaximal
    (H : ∀ (p : Ideal R) [p.IsMaximal], Function.Surjective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Surjective (algebraMap R S) := by
  apply surjective_of_isLocalized_maximal (fun P _ ↦ Rₚ P) (fun P _ ↦ Algebra.linearMap _ _)
    (fun P _ ↦ Sₚ P) (fun P _ ↦ IsScalarTower.toAlgHom R S (Sₚ P)) (Algebra.linearMap R S) _
  intro p hp
  convert_to Function.Surjective ((Algebra.linearMap (Rₚ p) (Sₚ p)).restrictScalars R)
  · rw [DFunLike.coe_fn_eq]
    apply IsLocalizedModule.map_linearMap_of_isLocalization
  · exact H p
/-
**bijective_of_isLocalization_isMaximal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bijective_of_isLocalization_isMaximal (H : forall (p : Ideal R) [p.IsMaxim
al], Function.Bijective (algebraMap (Rₚ p) (Sₚ p))) : Function.Bijective (algebr
aMap R S)
参数：H : forall (p : Ideal R) [p.IsMaximal], Function.Bijective (algebraMap (Rₚ p)
 (Sₚ p))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用引理 `injective_of_isLocalization_isMaximal`：injective_of_isLocalization_isMax
imal (H : forall (p : Ideal R) [p.IsMaximal], Function.Injective (algebraMap (Rₚ
 p) (Sₚ p))) : Function.Inj…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `surjective_of_isLocalization_isMaximal`：surjective_of_isLocalization_isM
aximal (H : forall (p : Ideal R) [p.IsMaximal], Function.Surjective (algebraMap 
(Rₚ p) (Sₚ p))) : Function.S…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma bijective_of_isLocalization_isMaximal
    (H : ∀ (p : Ideal R) [p.IsMaximal], Function.Bijective (algebraMap (Rₚ p) (Sₚ p))) :
    Function.Bijective (algebraMap R S) :=
  ⟨injective_of_isLocalization_isMaximal _ _ (fun p _ ↦ (H p).1),
    surjective_of_isLocalization_isMaximal _ _ (fun p _ ↦ (H p).2)⟩

end Algebra

section IsLocalization

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {s : Set R} (hs : span s = ⊤)
-- For every element `r ∈ s`, let `Rᵣ` be the localization of `R` away from `r`
-- and `Sᵣ` the localization of `S` away from `f r`.
variable (Rᵣ : s → Type*) [∀ r, CommSemiring (Rᵣ r)] [∀ r, Algebra R (Rᵣ r)]
  (Sᵣ : s → Type*) [∀ r, CommSemiring (Sᵣ r)] [∀ r, Algebra S (Sᵣ r)]
variable (f : R →+* S) [∀ r, IsLocalization.Away r.val (Rᵣ r)]
    [∀ r, IsLocalization.Away (f r.val) (Sᵣ r)]
include hs

/-
**injective_of_isLocalization_of_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：injective_of_isLocalization_of_span_eq_top (h : forall r : s, Function.Inj
ective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) : Function.Injective f
参数：h : forall r : s, Function.Injective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f
 r.1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsLocalization.Away.instAlgebraMapSubmonoidPowersOfCoeRingHomAlgebraMap`
：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_5} [inst_1 : CommSemiring 
A] [inst_2 : Algebra R A] (Aₚ : Type u_7)   [inst_3 : CommSem…
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.algebraMapSubmonoid_powers`：algebraMapSubmonoid_powers (r : R) :
 Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.map.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M M_1 : Submonoid R} (e_M : M = M_1) {S : Type u_2} [inst_1 : CommSemiring S]  
 [inst_2 : Algebra …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `injective_of_isLocalized_span`：injective_of_isLocalized_span (H : forall
 r : s, Function.Injective (map (.powers r.1) (f r) (g r) F)) : Function.Injecti
ve F
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmon
oid`：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {A : Type u_2} {
Aₛ : Type u_3} [inst_1 : CommSemiring A]   [inst_2 : Algebra R A]…
· 使用定理 `instIsLocalizationAlgebraMapSubmonoid`：∀ {R : Type u_1} [inst : CommSemi
ring R] {M : Submonoid R} (Rₘ : Type u_4) [inst_1 : CommSemiring Rₘ]   [inst_2 :
 Algebra R Rₘ] [IsLocalizat…
· 使用引理 `Algebra.algebraMapSubmonoid_self`：algebraMapSubmonoid_self (M : Submonoi
d R) : Algebra.algebraMapSubmonoid R M = M
· 使用引理 `Algebra.algebraMapSubmonoid_le_comap`：algebraMapSubmonoid_le_comap (f : 
A ->ₐ[R] B) : algebraMapSubmonoid A M <= (algebraMapSubmonoid B M).comap f.toRin
gHom
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsLocalization.map_linearMap_eq_toLinearMap_mapₐ`：map_linearMap_eq_toLin
earMap_mapₐ : IsLocalizedModule.map M (Algebra.linearMap R Rₚ) (IsScalarTower.to
AlgHom R A Aₚ).toLinearMap (Algebra.li…
-/
lemma injective_of_isLocalization_of_span_eq_top
    (h : ∀ r : s, Function.Injective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) :
    Function.Injective f := by
  algebraize [f]
  let (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f |>.toAlgebra
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  let (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localizationAlgebra (.powers r.val) S
  have (r : s) : IsScalarTower R (Rᵣ r) (Sᵣ r) :=
    .of_algebraMap_eq <| by simp [RingHom.algebraMap_toAlgebra]
  apply injective_of_isLocalized_span s hs Rᵣ (fun r : s ↦ Algebra.linearMap _ _) _
    (fun r : s ↦ ((IsScalarTower.toAlgHom R S (Sᵣ r)).toLinearMap)) (Algebra.linearMap R S)
  simpa [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ] using! h
/-
**surjective_of_isLocalization_of_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：surjective_of_isLocalization_of_span_eq_top (h : forall r : s, Function.Su
rjective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) : Function.Surjective f
参数：h : forall r : s, Function.Surjective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) 
f r.1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsLocalization.Away.instAlgebraMapSubmonoidPowersOfCoeRingHomAlgebraMap`
：∀ {R : Type u_1} [inst : CommSemiring R] {A : Type u_5} [inst_1 : CommSemiring 
A] [inst_2 : Algebra R A] (Aₚ : Type u_7)   [inst_3 : CommSem…
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.algebraMapSubmonoid_powers`：algebraMapSubmonoid_powers (r : R) :
 Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.map.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M M_1 : Submonoid R} (e_M : M = M_1) {S : Type u_2} [inst_1 : CommSemiring S]  
 [inst_2 : Algebra …
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `surjective_of_isLocalized_span`：surjective_of_isLocalized_span (H : fora
ll r : s, Function.Surjective (map (.powers r.1) (f r) (g r) F)) : Function.Surj
ective F
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmon
oid`：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {A : Type u_2} {
Aₛ : Type u_3} [inst_1 : CommSemiring A]   [inst_2 : Algebra R A]…
· 使用定理 `instIsLocalizationAlgebraMapSubmonoid`：∀ {R : Type u_1} [inst : CommSemi
ring R] {M : Submonoid R} (Rₘ : Type u_4) [inst_1 : CommSemiring Rₘ]   [inst_2 :
 Algebra R Rₘ] [IsLocalizat…
· 使用引理 `Algebra.algebraMapSubmonoid_self`：algebraMapSubmonoid_self (M : Submonoi
d R) : Algebra.algebraMapSubmonoid R M = M
· 使用引理 `Algebra.algebraMapSubmonoid_le_comap`：algebraMapSubmonoid_le_comap (f : 
A ->ₐ[R] B) : algebraMapSubmonoid A M <= (algebraMapSubmonoid B M).comap f.toRin
gHom
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsLocalization.map_linearMap_eq_toLinearMap_mapₐ`：map_linearMap_eq_toLin
earMap_mapₐ : IsLocalizedModule.map M (Algebra.linearMap R Rₚ) (IsScalarTower.to
AlgHom R A Aₚ).toLinearMap (Algebra.li…
-/
lemma surjective_of_isLocalization_of_span_eq_top
    (h : ∀ r : s, Function.Surjective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) :
    Function.Surjective f := by
  algebraize [f]
  let (r : s) : Algebra R (Sᵣ r) := (algebraMap S (Sᵣ r)).comp f |>.toAlgebra
  have (r : s) : IsScalarTower R S (Sᵣ r) := IsScalarTower.of_algebraMap_eq' rfl
  have : ∀ r, IsLocalization.Away (algebraMap R S r.val) (Sᵣ r) := ‹_›
  let (r : s) : Algebra (Rᵣ r) (Sᵣ r) := localizationAlgebra (.powers r.val) S
  have (r : s) : IsScalarTower R (Rᵣ r) (Sᵣ r) :=
    .of_algebraMap_eq <| by simp [RingHom.algebraMap_toAlgebra]
  apply surjective_of_isLocalized_span s hs Rᵣ (fun r : s ↦ Algebra.linearMap _ _) _
    (fun r : s ↦ ((IsScalarTower.toAlgHom R S (Sᵣ r)).toLinearMap)) (Algebra.linearMap R S)
  simpa [IsLocalization.map_linearMap_eq_toLinearMap_mapₐ] using! h
/-
**bijective_of_isLocalization_of_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：bijective_of_isLocalization_of_span_eq_top (h : forall r : s, Function.Bij
ective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) : Function.Bijective f
参数：h : forall r : s, Function.Bijective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f
 r.1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `injective_of_isLocalization_of_span_eq_top`：injective_of_isLocalization_
of_span_eq_top (h : forall r : s, Function.Injective (IsLocalization.Away.map (R
ᵣ r) (Sᵣ r) f r.1)) : Function.I…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `surjective_of_isLocalization_of_span_eq_top`：surjective_of_isLocalizatio
n_of_span_eq_top (h : forall r : s, Function.Surjective (IsLocalization.Away.map
 (Rᵣ r) (Sᵣ r) f r.1)) : Function…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma bijective_of_isLocalization_of_span_eq_top
    (h : ∀ r : s, Function.Bijective (IsLocalization.Away.map (Rᵣ r) (Sᵣ r) f r.1)) :
    Function.Bijective f :=
  ⟨injective_of_isLocalization_of_span_eq_top hs _ _ _ (fun r ↦ (h r).1),
    surjective_of_isLocalization_of_span_eq_top hs _ _ _ (fun r ↦ (h r).2)⟩

end IsLocalization

