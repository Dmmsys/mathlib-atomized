/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.LocalProperties.Exactness

/-!
# Flatness and localization

In this file we show that localizations are flat, and flatness is a local property.

## Main result
* `IsLocalization.flat`: a localization of a commutative ring is flat over it.
* `Module.flat_iff_of_isLocalization` : Let `Rₚ` a localization of a commutative ring `R`
  and `M` be a module over `Rₚ`. Then `M` is flat over `R` if and only if `M` is flat over `Rₚ`.
* `Module.flat_of_isLocalized_maximal` : Let `M` be a module over a commutative ring `R`.
  If the localization of `M` at each maximal ideal `P` is flat over `Rₚ`, then `M` is flat over `R`.
* `Module.flat_of_isLocalized_span` : Let `M` be a module over a commutative ring `R`
  and `S` be a set that spans `R`. If the localization of `M` at each `s : S` is flat
  over `Localization.Away s`, then `M` is flat over `R`.
-/

public section

open IsLocalizedModule LocalizedModule LinearMap TensorProduct

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (p : Submonoid R) [IsLocalization p S]
variable (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

set_option backward.isDefEq.respectTransparency.types false in
include p in
/-
**IsLocalization.flat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.flat : Module.Flat R S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.Flat.iff_lTensor_injectiveₛ`：iff_lTensor_injectiveₛ : Flat R M ↔ 
forall ⦃P : Type u⦄ [AddCommMonoid P] [Module R P] (N : Submodule R P), Function
.Injective (N.subtype.lT…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.isBaseChange`：IsLocalizedModule.isBaseChange [IsLocali
zedModule S f] : IsBaseChange A f
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Submodule.toLocalized'_apply_coe`：∀ {R : Type u_1} (S : Type u_2) {M : T
ype u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [ins
t_2 : AddCommMonoid M]…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem IsLocalization.flat : Module.Flat R S := by
  refine Module.Flat.iff_lTensor_injectiveₛ.mpr fun P _ _ N ↦ ?_
  have h := ((range N.subtype).isLocalizedModule S p (TensorProduct.mk R S P 1)).isBaseChange _ S
  let e := (LinearEquiv.ofInjective _ Subtype.val_injective).lTensor S ≪≫ₗ h.equiv.restrictScalars R
  have : N.subtype.lTensor S = Submodule.subtype _ ∘ₗ e.toLinearMap := by
    ext; change _ = (h.equiv _).1; simp [h.equiv_tmul, TensorProduct.smul_tmul']
  simpa [this] using! e.injective
/-
**Localization.flat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Localization.flat [Module.Flat R S] (p : Submonoid S) : Module.Flat R (Loc
alization p)
参数：p : Submonoid S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.flat`：IsLocalization.flat : Module.Flat R S
· 使用定理 `Module.Flat.trans`：trans [Flat R S] [Flat S M] : Flat R M
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
-/
instance Localization.flat [Module.Flat R S] (p : Submonoid S) : Module.Flat R (Localization p) :=
  have : Module.Flat S (Localization p) := IsLocalization.flat _ p
  .trans R S _

namespace Module

include p in
/-
**Module.flat_iff_of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：flat_iff_of_isLocalization : Flat S M ↔ Flat R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isLocalizedModule_id`：isLocalizedModule_id (R') [CommSemiring R'] [Algeb
ra R R'] [IsLocalization S R'] [Module R' M] [IsScalarTower R R' M] : IsLocalize
dModule S …
· 使用定理 `IsLocalization.flat`：IsLocalization.flat : Module.Flat R S
· 使用定理 `Module.Flat.trans`：trans [Flat R S] [Flat S M] : Flat R M
· 使用定理 `Module.Flat.of_isLocalizedModule`：of_isLocalizedModule [Flat R M] (S : S
ubmonoid R) [IsLocalization S Rp] (f : M ->ₗ[R] Mp) [h : IsLocalizedModule S f] 
: Flat Rp Mp
-/
theorem flat_iff_of_isLocalization : Flat S M ↔ Flat R M :=
  have := isLocalizedModule_id p M S
  have := IsLocalization.flat S p
  ⟨fun _ ↦ .trans R S M, fun _ ↦ .of_isLocalizedModule S p .id⟩

variable (Mₚ : ∀ (P : Ideal S) [P.IsMaximal], Type*)
  [∀ (P : Ideal S) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal S) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal S) [P.IsMaximal], Module S (Mₚ P)]
  [∀ (P : Ideal S) [P.IsMaximal], IsScalarTower R S (Mₚ P)]
  (f : ∀ (P : Ideal S) [P.IsMaximal], M →ₗ[S] Mₚ P)
  [∀ (P : Ideal S) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P)]

include f in
/-
**Module.flat_of_isLocalized_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：flat_of_isLocalized_maximal (H : forall (P : Ideal S) [P.IsMaximal], Flat 
R (Mₚ P)) : Module.Flat R M
参数：H : forall (P : Ideal S) [P.IsMaximal], Flat R (Mₚ P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TensorProduct.AlgebraTensorModule.coe_lTensor`：coe_lTensor (f : N ->ₗ[R]
 Q) : (lTensor A M f : M otimes[R] N -> M otimes[R] Q) = f.lTensor M
· 使用定理 `injective_of_isLocalized_maximal`：injective_of_isLocalized_maximal (H : 
forall (P : Ideal R) [P.IsMaximal], Function.Injective (map P.primeCompl (f P) (
g P) F)) : Function.In…
· 使用引理 `IsLocalizedModule.map_lTensor`：IsLocalizedModule.map_lTensor (g : M ->ₗ[
A] M') [h : IsLocalizedModule S g] : IsLocalizedModule.map S (AlgebraTensorModul
e.rTensor R N g) (A…
-/
theorem flat_of_isLocalized_maximal (H : ∀ (P : Ideal S) [P.IsMaximal], Flat R (Mₚ P)) :
    Module.Flat R M := by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N ↦ injective_of_isLocalized_maximal _
    (fun P ↦ AlgebraTensorModule.rTensor R _ (f P)) _
    (fun P ↦ AlgebraTensorModule.rTensor R _ (f P)) _ fun P hP ↦ ?_
  simpa [IsLocalizedModule.map_lTensor] using H P N
/-
**Module.flat_of_localized_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：flat_of_localized_maximal (h : forall (P : Ideal R) [P.IsMaximal], Flat R 
(LocalizedModule P.primeCompl M)) : Flat R M
参数：h : forall (P : Ideal R) [P.IsMaximal], Flat R (LocalizedModule P.primeCompl 
M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.flat_of_isLocalized_maximal`：flat_of_isLocalized_maximal (H : for
all (P : Ideal S) [P.IsMaximal], Flat R (Mₚ P)) : Module.Flat R M
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
-/
theorem flat_of_localized_maximal
    (h : ∀ (P : Ideal R) [P.IsMaximal], Flat R (LocalizedModule P.primeCompl M)) :
    Flat R M :=
  flat_of_isLocalized_maximal _ _ _ (fun _ _ ↦ mkLinearMap _ _) h

variable (s : Set S) (spn : Ideal.span s = ⊤)
  (Mₛ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Mₛ r)]
  [∀ r : s, Module R (Mₛ r)]
  [∀ r : s, Module S (Mₛ r)]
  [∀ r : s, IsScalarTower R S (Mₛ r)]
  (g : ∀ r : s, M →ₗ[S] Mₛ r)
  [∀ r : s, IsLocalizedModule.Away r.1 (g r)]
include spn

include g in
/-
**Module.flat_of_isLocalized_span** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：flat_of_isLocalized_span (H : forall r : s, Module.Flat R (Mₛ r)) : Module
.Flat R M
参数：H : forall r : s, Module.Flat R (Mₛ r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TensorProduct.AlgebraTensorModule.coe_lTensor`：coe_lTensor (f : N ->ₗ[R]
 Q) : (lTensor A M f : M otimes[R] N -> M otimes[R] Q) = f.lTensor M
· 使用定理 `injective_of_isLocalized_span`：injective_of_isLocalized_span (H : forall
 r : s, Function.Injective (map (.powers r.1) (f r) (g r) F)) : Function.Injecti
ve F
· 使用引理 `IsLocalizedModule.map_lTensor`：IsLocalizedModule.map_lTensor (g : M ->ₗ[
A] M') [h : IsLocalizedModule S g] : IsLocalizedModule.map S (AlgebraTensorModul
e.rTensor R N g) (A…
-/
theorem flat_of_isLocalized_span (H : ∀ r : s, Module.Flat R (Mₛ r)) :
    Module.Flat R M := by
  simp_rw [Flat.iff_lTensor_injectiveₛ] at H ⊢
  simp_rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  refine fun _ _ _ N ↦ injective_of_isLocalized_span s spn _
    (fun r ↦ AlgebraTensorModule.rTensor R _ (g r)) _
    (fun r ↦ AlgebraTensorModule.rTensor R _ (g r)) _ fun r ↦ ?_
  simpa [IsLocalizedModule.map_lTensor] using H r N
/-
**Module.flat_of_localized_span** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：flat_of_localized_span (h : forall r : s, Flat S (LocalizedModule.Away r.1
 M)) : Flat S M
参数：h : forall r : s, Flat S (LocalizedModule.Away r.1 M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.flat_of_isLocalized_span`：flat_of_isLocalized_span (H : forall r 
: s, Module.Flat R (Mₛ r)) : Module.Flat R M
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
-/
theorem flat_of_localized_span
    (h : ∀ r : s, Flat S (LocalizedModule.Away r.1 M)) :
    Flat S M :=
  flat_of_isLocalized_span _ _ _ spn _ (fun _ ↦ mkLinearMap _ _) h

end Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Flat A B] (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra p P] :
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime P) := by
  rw [Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl]
  exact Module.Flat.trans A B (Localization.AtPrime P)

section IsSMulRegular

variable {M} in
/-
**IsSMulRegular.of_isLocalizedModule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSMulRegular.of_isLocalizedModule {K : Type*} [AddCommMonoid K] [Module R
 K] (f : K ->ₗ[R] M) [IsLocalizedModule p f] {x : R} (reg : IsSMulRegular K x) :
 IsSMulRegular M (algebraMap R S x)
参数：f : K ->ₗ[R] M；reg : IsSMulRegular K x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.flat`：IsLocalization.flat : Module.Flat R S
· 使用定理 `IsSMulRegular.of_flat_of_isBaseChange`：IsSMulRegular.of_flat_of_isBaseCh
ange {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {x : R} (reg : IsSMulRegular M x) 
: IsSMulRegular N (algebraM…
· 使用定理 `IsLocalizedModule.isBaseChange`：IsLocalizedModule.isBaseChange [IsLocali
zedModule S f] : IsBaseChange A f
-/
theorem IsSMulRegular.of_isLocalizedModule {K : Type*} [AddCommMonoid K] [Module R K]
    (f : K →ₗ[R] M) [IsLocalizedModule p f] {x : R} (reg : IsSMulRegular K x) :
    IsSMulRegular M (algebraMap R S x) :=
  have : Module.Flat R S := IsLocalization.flat S p
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange p S f)

include p in
/-
**IsSMulRegular.of_isLocalization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSMulRegular.of_isLocalization {x : R} (reg : IsSMulRegular R x) : IsSMul
Regular S (algebraMap R S x)
参数：reg : IsSMulRegular R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_isLocalizedModule`：IsSMulRegular.of_isLocalizedModule {
K : Type*} [AddCommMonoid K] [Module R K] (f : K ->ₗ[R] M) [IsLocalizedModule p 
f] {x : R} (reg : IsSMul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
-/
theorem IsSMulRegular.of_isLocalization {x : R} (reg : IsSMulRegular R x) :
    IsSMulRegular S (algebraMap R S x) :=
  reg.of_isLocalizedModule S p (Algebra.linearMap R S)

end IsSMulRegular

