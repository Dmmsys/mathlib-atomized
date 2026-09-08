/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Module

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definition

* `isLocalizedModule_iff_isBaseChange` : A localization of modules corresponds to a base change.
-/

@[expose] public section

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization S A]
  {M : Type*} [AddCommMonoid M] [Module R M]
  {M' : Type*} [AddCommMonoid M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
  (f : M →ₗ[R] M')

/-- The forward direction of `isLocalizedModule_iff_isBaseChange`. It is also used to prove the
other direction. -/
/-
**IsLocalizedModule.isBaseChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.isBaseChange [IsLocalizedModule S f] : IsBaseChange A f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBaseChange.of_lift_unique`：IsBaseChange.of_lift_unique (h : forall (Q 
: Type max v₁ v₂ v₃) [AddCommMonoid Q], forall [Module R Q] [Module S Q], forall
 [IsScalarTower R…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsLocalizedModule.is_universal`：is_universal : forall (g : M ->ₗ[R] M'')
 (_ : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x)), exists! l : M
' ->ₗ[R] M'', l.comp…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The forward direction of `isLocalizedModule_iff_isBaseChange`. It is also used t
o prove the
other direction.
-/
theorem IsLocalizedModule.isBaseChange [IsLocalizedModule S f] : IsBaseChange A f :=
  .of_lift_unique _ fun Q _ _ _ _ g ↦ by
    obtain ⟨ℓ, rfl, h₂⟩ := IsLocalizedModule.is_universal S f g fun s ↦ by
      rw [← (Algebra.lsmul R (A := A) R Q).commutes]; exact (IsLocalization.map_units A s).map _
    refine ⟨ℓ.extendScalarsOfIsLocalization S A, by simp, fun g'' h ↦ ?_⟩
    cases h₂ (LinearMap.restrictScalars R g'') h; rfl

variable (M) in
/-
**LocalizedModule.isBaseChange** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.isBaseChange : IsBaseChange (Localization S) (LocalizedMod
ule.mkLinearMap S M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.isBaseChange`：IsLocalizedModule.isBaseChange [IsLocali
zedModule S f] : IsBaseChange A f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
-/
lemma LocalizedModule.isBaseChange :
    IsBaseChange (Localization S) (LocalizedModule.mkLinearMap S M) :=
  IsLocalizedModule.isBaseChange S (Localization S) (LocalizedModule.mkLinearMap S M)

/-- The map `(f : M →ₗ[R] M')` is a localization of modules iff the map
`(Localization S) × M → N, (s, m) ↦ s • f m` is the tensor product (insomuch as it is the universal
bilinear map).
In particular, there is an isomorphism between `LocalizedModule S M` and `(Localization S) ⊗[R] M`
given by `m/s ↦ (1/s) ⊗ₜ m`.
-/
/-
**isLocalizedModule_iff_isBaseChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLocalizedModule_iff_isBaseChange : IsLocalizedModule S f ↔ IsBaseChange 
A f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.isBaseChange`：IsLocalizedModule.isBaseChange [IsLocali
zedModule S f] : IsBaseChange A f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LocalizedModule.instIsScalarTower`：∀ {R : Type u} [inst : CommSemiring R
] {S : Submonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (T : Type u_…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `LinearEquiv.trans_apply`：trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[
σ₁₃] M₃) c = e₂₃ (e₁₂ c)
· 使用定理 `IsBaseChange.equiv_symm_apply`：IsBaseChange.equiv_symm_apply (m : M) : h
.equiv.symm (f m) = 1 otimesₜ m
· 使用定理 `IsBaseChange.equiv_tmul`：IsBaseChange.equiv_tmul (s : S) (m : M) : h.equ
iv (s otimesₜ m) = s • f m
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
The map `(f : M →ₗ[R] M')` is a localization of modules iff the map
`(Localization S) × M → N, (s, m) ↦ s • f m` is the tensor product (insomuch as 
it is the universal
bilinear map).
In particular, there is an isomorphism between `LocalizedModule S M` and `(Local
ization S) ⊗[R] M`
given by `m/s ↦ (1/s) ⊗ₜ m`.
-/
theorem isLocalizedModule_iff_isBaseChange : IsLocalizedModule S f ↔ IsBaseChange A f := by
  refine ⟨fun _ ↦ IsLocalizedModule.isBaseChange S A f, fun h ↦ ?_⟩
  let : Module A (LocalizedModule S M) := LocalizedModule.moduleOfIsLocalization ..
  have : IsBaseChange A (LocalizedModule.mkLinearMap S M) := IsLocalizedModule.isBaseChange S A _
  let e := (this.equiv.symm.trans h.equiv).restrictScalars R
  convert! IsLocalizedModule.of_linearEquiv S (LocalizedModule.mkLinearMap S M) e
  ext
  rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.trans_apply, IsBaseChange.equiv_symm_apply,
    IsBaseChange.equiv_tmul, one_smul]

open TensorProduct

variable (M) in
/-- The localization of an `R`-module `M` at a submonoid `S` is isomorphic to `S⁻¹R ⊗[R] M` as
an `S⁻¹R`-module. -/
/-
**LocalizedModule.equivTensorProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LocalizedModule.equivTensorProduct : LocalizedModule S M ≃ₗ[Localization S
] Localization S otimes[R] M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LocalizedModule.isBaseChange`：LocalizedModule.isBaseChange : IsBaseChang
e (Localization S) (LocalizedModule.mkLinearMap S M)

--- 原说明 ---
The localization of an `R`-module `M` at a submonoid `S` is isomorphic to `S⁻¹R 
⊗[R] M` as
an `S⁻¹R`-module.
-/
noncomputable def LocalizedModule.equivTensorProduct :
    LocalizedModule S M ≃ₗ[Localization S] Localization S ⊗[R] M :=
  (LocalizedModule.isBaseChange S M).equiv.symm

@[simp]
/-
**LocalizedModule.equivTensorProduct_symm_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：LocalizedModule.equivTensorProduct_symm_apply_tmul (x : M) (r : R) (s : S)
 : (equivTensorProduct S M).symm (Localization.mk r s otimesₜ[R] x) = r • mk x s
参数：x : M；r : R；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
· 使用定理 `LocalizedModule.mk_smul_mk`：mk_smul_mk (r : R) (m : M) (s t : S) : Local
ization.mk r s • mk m t = mk (r • m) (s * t)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul (x : M) (r : R) (s : S) :
    (equivTensorProduct S M).symm (Localization.mk r s ⊗ₜ[R] x) = r • mk x s := by
  simp [equivTensorProduct, IsBaseChange.equiv_tmul, mk_smul_mk, smul'_mk]

@[simp]
/-
**LocalizedModule.equivTensorProduct_symm_apply_tmul_one** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：LocalizedModule.equivTensorProduct_symm_apply_tmul_one (x : M) : (equivTen
sorProduct S M).symm (1 otimesₜ[R] x) = mk x 1
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LocalizedModule.equivTensorProduct_symm_apply_tmul`：LocalizedModule.equi
vTensorProduct_symm_apply_tmul (x : M) (r : R) (s : S) : (equivTensorProduct S M
).symm (Localization.mk r s otimesₜ[R] x…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LocalizedModule.equivTensorProduct_symm_apply_tmul_one (x : M) :
    (equivTensorProduct S M).symm (1 ⊗ₜ[R] x) = mk x 1 := by
  simp [← Localization.mk_one]

@[simp]
/-
**LocalizedModule.equivTensorProduct_apply_mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocalizedModule.equivTensorProduct_apply_mk (x : M) (s : S) : equivTensorP
roduct S M (mk x s) = Localization.mk 1 s otimesₜ[R] x
参数：x : M；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用引理 `LocalizedModule.equivTensorProduct_symm_apply_tmul`：LocalizedModule.equi
vTensorProduct_symm_apply_tmul (x : M) (r : R) (s : S) : (equivTensorProduct S M
).symm (Localization.mk r s otimesₜ[R] x…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LocalizedModule.equivTensorProduct_apply_mk (x : M) (s : S) :
    equivTensorProduct S M (mk x s) = Localization.mk 1 s ⊗ₜ[R] x := by
  apply (equivTensorProduct S M).symm.injective
  simp

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {T : Type*} [CommSemiring T] [Algebra R T] :
    IsLocalizedModule S (IsScalarTower.toAlgHom R T (A ⊗[R] T) : T →ₗ[R] A ⊗[R] T) := by
  rw [isLocalizedModule_iff_isBaseChange (S := S) (A := A)]
  exact TensorProduct.isBaseChange _ _ _

namespace IsLocalization

open TensorProduct Algebra.TensorProduct

/-
**IsLocalization.tensorProduct_isLocalizedModule** 是 Mathlib 中的一个实例，位于命名空间 `IsLo
calization`。
形式化陈述：tensorProduct_isLocalizedModule : IsLocalizedModule S (TensorProduct.mk R 
A M 1)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用定理 `TensorProduct.isBaseChange`：TensorProduct.isBaseChange : IsBaseChange S 
(TensorProduct.mk R S M 1)
-/
instance tensorProduct_isLocalizedModule : IsLocalizedModule S (TensorProduct.mk R A M 1) :=
  (isLocalizedModule_iff_isBaseChange _ A _).mpr (TensorProduct.isBaseChange _ _ _)

variable (M₁ M₂ B C) [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
  [Module A M₁] [Module A M₂] [IsScalarTower R A M₁] [IsScalarTower R A M₂]
  [Semiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Semiring C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
include S
/-
**IsLocalization.tensorProduct_compatibleSMul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
ization`。
形式化陈述：tensorProduct_compatibleSMul : CompatibleSMul R A M₁ M₂ where smul_tmul a 
_ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsUnit.smul_left_cancel`：smul_left_cancel {a : α} (ha : IsUnit a) {x y :
 β} : a • x = a • y ↔ x = y
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `IsLocalization.smul_mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensorProduct_compatibleSMul : CompatibleSMul R A M₁ M₂ where
  smul_tmul a _ _ := by
    obtain ⟨r, s, rfl⟩ := exists_mk'_eq S a
    rw [← (map_units A s).smul_left_cancel]
    simp_rw [algebraMap_smul, smul_tmul', ← smul_assoc, smul_tmul, ← smul_assoc, smul_mk'_self,
      algebraMap_smul, smul_tmul]
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module (Localization S) M₁] [Module (Localization S) M₂]
    [IsScalarTower R (Localization S) M₁] [IsScalarTower R (Localization S) M₂] :
    CompatibleSMul R (Localization S) M₁ M₂ :=
  tensorProduct_compatibleSMul S ..
/-
**IsLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (N N') [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N'] (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (TensorProduct.map f g) := by
  let eM := IsLocalizedModule.linearEquiv S f (TensorProduct.mk R (Localization S) M 1)
  let eN := IsLocalizedModule.linearEquiv S g (TensorProduct.mk R (Localization S) N 1)
  convert!
    IsLocalizedModule.of_linearEquiv S (TensorProduct.mk R (Localization S) (M ⊗[R] N) 1) <|
      (AlgebraTensorModule.distribBaseChange R (Localization S) ..).restrictScalars R ≪≫ₗ
        (congr eM eN ≪≫ₗ TensorProduct.equivOfCompatibleSMul ..).symm
  ext; congrm (?_ ⊗ₜ ?_) <;> simp [LinearEquiv.eq_symm_apply, eM, eN]

/-- If `A` is a localization of `R`, tensoring two `A`-modules over `A` is the same as
tensoring them over `R`. -/
/-
**IsLocalization.moduleTensorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：moduleTensorEquiv : M₁ otimes[A] M₂ ≃ₗ[A] M₁ otimes[R] M₂
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.tensorProduct_compatibleSMul`：tensorProduct_compatibleSMu
l : CompatibleSMul R A M₁ M₂ where smul_tmul a _ _

--- 原说明 ---
If `A` is a localization of `R`, tensoring two `A`-modules over `A` is the same 
as
tensoring them over `R`.
-/
noncomputable def moduleTensorEquiv : M₁ ⊗[A] M₂ ≃ₗ[A] M₁ ⊗[R] M₂ :=
  have := tensorProduct_compatibleSMul S A M₁ M₂
  equivOfCompatibleSMul R A A M₁ M₂

/-- If `A` is a localization of `R`, tensoring an `A`-module with `A` over `R` does nothing. -/
/-
**IsLocalization.moduleLid** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：moduleLid : A otimes[R] M₁ ≃ₗ[A] M₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is a localization of `R`, tensoring an `A`-module with `A` over `R` does 
nothing.
-/
noncomputable def moduleLid : A ⊗[R] M₁ ≃ₗ[A] M₁ :=
  have := tensorProduct_compatibleSMul S A A M₁
  (equivOfCompatibleSMul R A A A M₁).symm ≪≫ₗ TensorProduct.lid _ _

/-- If `A` is a localization of `R`, tensoring two `A`-algebras over `A` is the same as
tensoring them over `R`. -/
/-
**IsLocalization.algebraTensorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：algebraTensorEquiv : B otimes[A] C ≃ₐ[A] B otimes[R] C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is a localization of `R`, tensoring two `A`-algebras over `A` is the same
 as
tensoring them over `R`.
-/
noncomputable def algebraTensorEquiv : B ⊗[A] C ≃ₐ[A] B ⊗[R] C :=
  have := tensorProduct_compatibleSMul S A B C
  Algebra.TensorProduct.equivOfCompatibleSMul R A A B C

/-- If `A` is a localization of `R`, tensoring an `A`-algebra with `A` over `R` does nothing. -/
/-
**IsLocalization.algebraLid** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：algebraLid : A otimes[R] B ≃ₐ[A] B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is a localization of `R`, tensoring an `A`-algebra with `A` over `R` does
 nothing.
-/
noncomputable def algebraLid : A ⊗[R] B ≃ₐ[A] B :=
  have := tensorProduct_compatibleSMul S A A B
  Algebra.TensorProduct.lidOfCompatibleSMul R A B

set_option linter.docPrime false in
/-
**IsLocalization.bijective_linearMap_mul'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizat
ion`。
形式化陈述：bijective_linearMap_mul' : Function.Bijective (LinearMap.mul' R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.tensorProduct_compatibleSMul`：tensorProduct_compatibleSMu
l : CompatibleSMul R A M₁ M₂ where smul_tmul a _ _
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem bijective_linearMap_mul' : Function.Bijective (LinearMap.mul' R A) :=
  have := tensorProduct_compatibleSMul S A A A
  (Algebra.TensorProduct.lmulEquiv R A).bijective

end IsLocalization

variable (T B : Type*) [CommSemiring T] [CommSemiring B]
  [Algebra R T] [Algebra T B] [Algebra R B] [Algebra A B] [IsScalarTower R T B]
  [IsScalarTower R A B]

variable {T B} in
/-
**Algebra.isLocalization_iff_isPushout** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.isLocalization_iff_isPushout : IsLocalization (Algebra.algebraMapS
ubmonoid T S) B ↔ IsPushout R T A B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.IsPushout.comm`：Algebra.IsPushout.comm : Algebra.IsPushout R S R
' S' ↔ Algebra.IsPushout R R' S S'
· 使用定理 `Algebra.isPushout_iff`：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiri
ng R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (R' : Type u_6)   (S' : T
ype u_7) [i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isLocalizedModule_iff_isLocalization`：isLocalizedModule_iff_isLocalizati
on : IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔ IsLocaliz
ation (Algebra.algebraMapS…
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Algebra.isLocalization_iff_isPushout :
    IsLocalization (Algebra.algebraMapSubmonoid T S) B ↔ IsPushout R T A B := by
  rw [Algebra.IsPushout.comm, Algebra.isPushout_iff, ← isLocalizedModule_iff_isLocalization]
  rw [← isLocalizedModule_iff_isBaseChange (S := S)]
/-
**Algebra.isPushout_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.isPushout_of_isLocalization [IsLocalization (Algebra.algebraMapSub
monoid T S) B] : Algebra.IsPushout R T A B
参数：Algebra.algebraMapSubmonoid T S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.isLocalization_iff_isPushout`：Algebra.isLocalization_iff_isPusho
ut : IsLocalization (Algebra.algebraMapSubmonoid T S) B ↔ IsPushout R T A B
-/
lemma Algebra.isPushout_of_isLocalization [IsLocalization (Algebra.algebraMapSubmonoid T S) B] :
    Algebra.IsPushout R T A B :=
  (Algebra.isLocalization_iff_isPushout S _).mp inferInstance
/-
**Submonoid.map_isUnit_le_isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submonoid.map_isUnit_le_isUnit {M N : Type*} [Monoid M] [Monoid N] {F : Ty
pe*} [FunLike F M N] [MonoidHomClass F M N] (f : F) : Submonoid.map f (IsUnit.su
bmonoid M) <= IsUnit.submonoid N
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
-/
lemma Submonoid.map_isUnit_le_isUnit {M N : Type*} [Monoid M] [Monoid N]
    {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) :
    Submonoid.map f (IsUnit.submonoid M) ≤ IsUnit.submonoid N := by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _
/-
**Algebra.algebraMapSubmonoid_isUnit_le_isUnit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.algebraMapSubmonoid_isUnit_le_isUnit {R S : Type*} [CommSemiring R
] [Semiring S] [Algebra R S] : Algebra.algebraMapSubmonoid S (IsUnit.submonoid R
) <= IsUnit.submonoid S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma Algebra.algebraMapSubmonoid_isUnit_le_isUnit {R S : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] :
    Algebra.algebraMapSubmonoid S (IsUnit.submonoid R) ≤ IsUnit.submonoid S := by
  rintro x ⟨y, hy, rfl⟩
  exact hy.map _
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] :
    IsLocalization (Algebra.algebraMapSubmonoid S (IsUnit.submonoid R)) S :=
  IsLocalization.of_le_isUnit Algebra.algebraMapSubmonoid_isUnit_le_isUnit
/-
**Algebra.IsPushout.of_bijective_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.of_bijective_left [Algebra A T] [IsScalarTower R A T] (H
 : Function.Bijective (algebraMap R A)) : IsPushout R T A T
参数：H : Function.Bijective (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.of_le_isUnit_of_bijective`：of_le_isUnit_of_bijective {M :
 Submonoid R} (hM : Algebra.algebraMapSubmonoid S M <= IsUnit.submonoid S) (h : 
Function.Bijective (algebraMap…
· 使用引理 `Algebra.algebraMapSubmonoid_isUnit_le_isUnit`：Algebra.algebraMapSubmonoi
d_isUnit_le_isUnit {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S] : A
lgebra.algebraMapSubmonoid S (IsUn…
· 使用引理 `Algebra.isPushout_of_isLocalization`：Algebra.isPushout_of_isLocalization
 [IsLocalization (Algebra.algebraMapSubmonoid T S) B] : Algebra.IsPushout R T A 
B
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizationAlgebraMapSubmonoidSubmonoid`：∀ {R : Type u_7} {S : Ty
pe u_8} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]
,   IsLocalization (Algebra.algebraM…
-/
lemma Algebra.IsPushout.of_bijective_left [Algebra A T] [IsScalarTower R A T]
    (H : Function.Bijective (algebraMap R A)) :
    IsPushout R T A T := by
  have : IsLocalization (IsUnit.submonoid R) A :=
    IsLocalization.of_le_isUnit_of_bijective Algebra.algebraMapSubmonoid_isUnit_le_isUnit H
  apply isPushout_of_isLocalization (IsUnit.submonoid R)
/-
**Algebra.IsPushout.of_bijective_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.of_bijective_right [Algebra A T] [IsScalarTower R A T] (
H : Function.Bijective (algebraMap A T)) : IsPushout R A R T
参数：H : Function.Bijective (algebraMap A T)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.of_le_isUnit_of_bijective`：of_le_isUnit_of_bijective {M :
 Submonoid R} (hM : Algebra.algebraMapSubmonoid S M <= IsUnit.submonoid S) (h : 
Function.Bijective (algebraMap…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMapSubmonoid_map_map`：Algebra.algebraMapSubmonoid_map_map
 {R A B : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (M : Submonoid 
R) [Semiring B] [Algebra …
· 使用引理 `Algebra.algebraMapSubmonoid_isUnit_le`：algebraMapSubmonoid_isUnit_le : a
lgebraMapSubmonoid S (IsUnit.submonoid R) <= IsUnit.submonoid S
· 使用引理 `Algebra.isPushout_of_isLocalization`：Algebra.isPushout_of_isLocalization
 [IsLocalization (Algebra.algebraMapSubmonoid T S) B] : Algebra.IsPushout R T A 
B
· 使用定理 `IsLocalization.instSubmonoid`：∀ {R : Type u_1} [inst : CommSemiring R], 
IsLocalization (IsUnit.submonoid R) R
-/
lemma Algebra.IsPushout.of_bijective_right [Algebra A T] [IsScalarTower R A T]
    (H : Function.Bijective (algebraMap A T)) :
    IsPushout R A R T := by
  have : IsLocalization (algebraMapSubmonoid A (IsUnit.submonoid R)) T := by
    apply IsLocalization.of_le_isUnit_of_bijective _ H
    simpa using Algebra.algebraMapSubmonoid_isUnit_le
  apply Algebra.isPushout_of_isLocalization (IsUnit.submonoid R)

variable (R M) in
open TensorProduct in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α} [IsLocalizedModule S f] :
    IsLocalizedModule S (Finsupp.mapRange.linearMap (α := α) f) := by
  classical
  let e : Localization S ⊗[R] M ≃ₗ[R] M' :=
    (LocalizedModule.equivTensorProduct S M).symm.restrictScalars R ≪≫ₗ IsLocalizedModule.iso S f
  let e' : Localization S ⊗[R] (α →₀ M) ≃ₗ[R] (α →₀ M') :=
    finsuppRight R R (Localization S) M α ≪≫ₗ Finsupp.mapRange.linearEquiv e
  suffices IsLocalizedModule S (e'.symm.toLinearMap ∘ₗ Finsupp.mapRange.linearMap f) by
    convert! this.of_linearEquiv (e := e')
    ext
    simp
  rw [isLocalizedModule_iff_isBaseChange S (Localization S)]
  convert! TensorProduct.isBaseChange R (α →₀ M) (Localization S) using 1
  ext a m
  apply (finsuppRight R R (Localization S) M α).injective
  ext b
  apply e.injective
  suffices (if a = b then f m else 0) = e (1 ⊗ₜ[R] if a = b then m else 0) by
    simpa [e', Finsupp.single_apply, -EmbeddingLike.apply_eq_iff_eq, apply_ite]
  split_ifs with h
  · simp [e]
  · simp only [tmul_zero, map_zero]

open Finsupp in
/-
**IsLocalizedModule.map_linearCombination** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.map_linearCombination {α : Type*} {v : α -> M} [IsLocali
zedModule S f] : map S (mapRange.linearMap (Algebra.linearMap R A)) f (linearCom
bination R v) = linearCombination A (f ∘ v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.linearMap_ext`：linearMap_ext {N N'} [AddCommMonoid N] 
[Module R N] [AddCommMonoid N'] [Module R N'] (f' : N ->ₗ[R] N') [IsLocalizedMod
ule S f'] ⦃g g' : M' …
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
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `IsLocalizedModule.map_comp`：map_comp (h : M ->ₗ[R] N) : (map S f g h) ∘ₗ
 f = g ∘ₗ h
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsLocalizedModule.map_linearCombination {α : Type*} {v : α → M} [IsLocalizedModule S f] :
    map S (mapRange.linearMap (Algebra.linearMap R A)) f (linearCombination R v) =
      linearCombination A (f ∘ v) :=
  linearMap_ext (S := S) (mapRange.linearMap (Algebra.linearMap R A)) f <| by
    ext; simp [IsLocalizedModule.map_comp]

section

variable (S : Submonoid A) {N : Type*} [AddCommMonoid N] [Module R N]
variable [Module A M] [IsScalarTower R A M]

open TensorProduct

/-- `S⁻¹M ⊗[R] N = S⁻¹(M ⊗[R] N)`. -/
/-
**IsLocalizedModule.rTensor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsLocalizedModule.rTensor (g : M ->ₗ[A] M') [h : IsLocalizedModule S g] : 
IsLocalizedModule S (AlgebraTensorModule.rTensor R N g)
参数：g : M ->ₗ[A] M'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `LinearEquiv.isScalarTower`：LinearEquiv.isScalarTower [Module R α] [Modul
e R β] [IsScalarTower R A β] (e : α ≃ₗ[R] β) : letI
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `IsScalarTower.of_algebraMap_smul`：of_algebraMap_smul [SMul R M] (h : for
all (r : R) (x : M), algebraMap R A r • x = r • x) : IsScalarTower R A M where s
mul_assoc r a x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用引理 `isBaseChange_tensorProduct_map`：isBaseChange_tensorProduct_map {f : M ->
ₗ[S] N} (hf : IsBaseChange A f) : IsBaseChange A (AlgebraTensorModule.map f (Lin
earMap.id (R

--- 原说明 ---
`S⁻¹M ⊗[R] N = S⁻¹(M ⊗[R] N)`.
-/
instance IsLocalizedModule.rTensor (g : M →ₗ[A] M') [h : IsLocalizedModule S g] :
    IsLocalizedModule S (AlgebraTensorModule.rTensor R N g) := by
  let Aₚ := Localization S
  let : Module Aₚ M' := (IsLocalizedModule.iso S g).symm.toAddEquiv.module Aₚ
  have : IsScalarTower A Aₚ M' := (IsLocalizedModule.iso S g).symm.isScalarTower Aₚ
  have : IsScalarTower R Aₚ M' :=
    IsScalarTower.of_algebraMap_smul <| fun r x ↦ by simp [IsScalarTower.algebraMap_apply R A Aₚ]
  rw [isLocalizedModule_iff_isBaseChange (S := S) (A := Aₚ)] at h ⊢
  exact isBaseChange_tensorProduct_map _ h

variable {P : Type*} [AddCommMonoid P] [Module R P] (f : N →ₗ[R] P)
/-
**IsLocalizedModule.map_lTensor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.map_lTensor (g : M ->ₗ[A] M') [h : IsLocalizedModule S g
] : IsLocalizedModule.map S (AlgebraTensorModule.rTensor R N g) (AlgebraTensorMo
dule.rTensor R P g) (AlgebraTensorModule.lTensor A M f) = AlgebraTensorModule.lT
ensor A M' f
参数：g : M ->ₗ[A] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.linearMap_ext`：linearMap_ext {N N'} [AddCommMonoid N] 
[Module R N] [AddCommMonoid N'] [Module R N'] (f' : N ->ₗ[R] N') [IsLocalizedMod
ule S f'] ⦃g g' : M' …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.map_comp`：map_comp (h : M ->ₗ[R] N) : (map S f g h) ∘ₗ
 f = g ∘ₗ h
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsLocalizedModule.map_lTensor (g : M →ₗ[A] M') [h : IsLocalizedModule S g] :
    IsLocalizedModule.map S (AlgebraTensorModule.rTensor R N g) (AlgebraTensorModule.rTensor R P g)
      (AlgebraTensorModule.lTensor A M f) = AlgebraTensorModule.lTensor A M' f := by
  apply linearMap_ext S (AlgebraTensorModule.rTensor R N g) (AlgebraTensorModule.rTensor R P g)
  rw [map_comp]
  ext
  simp

end

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (r : R) (A : Type*) [CommSemiring A] [Algebra R A]

/-
**IsLocalization.tensor** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsLocalization.tensor (M : Submonoid R) [IsLocalization M A] : IsLocalizat
ion (Algebra.algebraMapSubmonoid S M) (S otimes[R] A)
参数：M : Submonoid R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.isLocalization_iff_isPushout`：Algebra.isLocalization_iff_isPusho
ut : IsLocalization (Algebra.algebraMapSubmonoid T S) B ↔ IsPushout R T A B
-/
instance IsLocalization.tensor (M : Submonoid R) [IsLocalization M A] :
    IsLocalization (Algebra.algebraMapSubmonoid S M) (S ⊗[R] A) := by
  let _ : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  rw [Algebra.isLocalization_iff_isPushout _ A]
  infer_instance

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-
**IsLocalization.tensorRight** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsLocalization.tensorRight (M : Submonoid R) [IsLocalization M A] : IsLoca
lization (Algebra.algebraMapSubmonoid S M) (A otimes[R] S)
参数：M : Submonoid R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.isLocalization_iff_isPushout`：Algebra.isLocalization_iff_isPusho
ut : IsLocalization (Algebra.algebraMapSubmonoid T S) B ↔ IsPushout R T A B
-/
instance IsLocalization.tensorRight (M : Submonoid R) [IsLocalization M A] :
    IsLocalization (Algebra.algebraMapSubmonoid S M) (A ⊗[R] S) := by
  rw [Algebra.isLocalization_iff_isPushout _ A]
  infer_instance

open Algebra.TensorProduct in
/-
**IsLocalization.tmul_mk'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalization.tmul_mk' (M : Submonoid R) [IsLocalization M A] (s : S) (x 
: R) (y : M) : s otimesₜ IsLocalization.mk' A x y = IsLocalization.mk' (S otimes
[R] A) (algebraMap R S x * s) ⟨algebraMap R S y.1, Algebra.mem_algebraMapSubmono
id_of_mem _⟩
参数：M : Submonoid R；s : S；x : R；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.mem_algebraMapSubmonoid_of_mem`：mem_algebraMapSubmonoid_of_mem {
M : Submonoid R} (x : M) : algebraMap R S x in algebraMapSubmonoid S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Algebra.TensorProduct.algebraMap_apply`：algebraMap_apply [SMulCommClass 
R S A] (r : S) : algebraMap S (A otimes[R] B) r = (algebraMap S A) r otimesₜ 1
· 使用定理 `Algebra.algebraMap_self`：∀ {R : Type u} [inst : CommSemiring R], algebra
Map R R = RingHom.id R
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用引理 `Algebra.TensorProduct.tmul_one_eq_one_tmul`：tmul_one_eq_one_tmul (r : R)
 : algebraMap R A r otimesₜ[R] 1 = 1 otimesₜ algebraMap R B r
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.TensorProduct.tmul_mul_tmul`：tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : 
B) : a₁ otimesₜ[R] b₁ * a₂ otimesₜ[R] b₂ = (a₁ * a₂) otimesₜ[R] (b₁ * b₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
-/
lemma IsLocalization.tmul_mk' (M : Submonoid R) [IsLocalization M A] (s : S) (x : R) (y : M) :
    s ⊗ₜ IsLocalization.mk' A x y =
      IsLocalization.mk' (S ⊗[R] A) (algebraMap R S x * s)
        ⟨algebraMap R S y.1, Algebra.mem_algebraMapSubmonoid_of_mem _⟩ := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, algebraMap_apply, Algebra.algebraMap_self,
    RingHomCompTriple.comp_apply, tmul_one_eq_one_tmul, tmul_mul_tmul, mul_one, mul_comm,
    IsLocalization.mk'_spec', algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    ← Algebra.smul_def, smul_tmul, Algebra.smul_def, mul_one]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
open Algebra.TensorProduct in
/-
**IsLocalization.mk'_tmul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：∀ {R : Type u_7} {S : Type u_8} [inst : CommSemiring R] [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S] (A : Type u_9)   [inst_3 : CommSemiring A] [inst_
4 : Algebra R A] (M : Submonoid R) [inst_5 : IsLocalization M A] (s : S) (x : R)
   (y : ↥M),   IsLocalization.mk' A x y ⊗ₜ[R] s =     IsLocalization.mk' (Tensor
Product R A S) ((algebraMap R S) x * s) ⟨(algebraMap R S) ↑y, ⋯⟩
参数：A : Type u_9；M : Submonoid R；s : S；x : R；y : ↥M；TensorProduct R A S；(algebraM
ap R S) x * s；algebraMap R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Algebra.mem_algebraMapSubmonoid_of_mem`：mem_algebraMapSubmonoid_of_mem {
M : Submonoid R} (x : M) : algebraMap R S x in algebraMapSubmonoid S M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsLocalization.mk'_tmul (M : Submonoid R) [IsLocalization M A] (s : S) (x : R) (y : M) :
    IsLocalization.mk' A x y ⊗ₜ s =
      IsLocalization.mk' (A ⊗[R] S) (algebraMap R S x * s)
        ⟨algebraMap R S y.1, Algebra.mem_algebraMapSubmonoid_of_mem _⟩ := by
  simp [IsLocalization.eq_mk'_iff_mul_eq, map_mul,
    RingHom.algebraMap_toAlgebra]

namespace Localization

variable {R : Type*} [CommRing R] (M : Submonoid R) (Rₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ]
  (S : Type*) [CommRing S] [Algebra R S]

/-- The isomorphism `S ⊗[R] Rₘ ≃ₐ[S] Sₘ`. This is a specialization of `IsLocalization.algEquiv`,
but with additional properties since now `Sₘ` is automatically an `Rₘ`-algebra. -/
/-
**Localization.tensorLeftAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：tensorLeftAlgEquiv : (S otimes[R] Localization M) ≃ₐ[S] Localization (Alge
bra.algebraMapSubmonoid S M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `S ⊗[R] Rₘ ≃ₐ[S] Sₘ`. This is a specialization of `IsLocalizatio
n.algEquiv`,
but with additional properties since now `Sₘ` is automatically an `Rₘ`-algebra.
-/
noncomputable def tensorLeftAlgEquiv :
    (S ⊗[R] Localization M) ≃ₐ[S] Localization (Algebra.algebraMapSubmonoid S M) :=
  (algEquiv (Algebra.algebraMapSubmonoid S M) (S ⊗[R] Localization M)).symm

variable {S} in
@[simp]
/-
**Localization.tensorLeftAlgEquiv_apply_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `Loca
lization`。
形式化陈述：tensorLeftAlgEquiv_apply_tmul_one (x : S) : tensorLeftAlgEquiv M S (x otim
esₜ[R] 1) = algebraMap _ _ x
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem tensorLeftAlgEquiv_apply_tmul_one (x : S) :
    tensorLeftAlgEquiv M S (x ⊗ₜ[R] 1) = algebraMap _ _ x :=
  (tensorLeftAlgEquiv M S).commutes x

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Localization.tensorLeftAlgEquiv_apply_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Loca
lization`。
形式化陈述：tensorLeftAlgEquiv_apply_one_tmul (x : Localization M) : tensorLeftAlgEqui
v M S (1 otimesₜ[R] x) = algebraMap _ _ x
参数：x : Localization M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.tensorLeftAlgEquiv.eq_1`：∀ {R : Type u_10} [inst : CommRing
 R] (M : Submonoid R) (S : Type u_12) [inst_1 : CommRing S] [inst_2 : Algebra R 
S],   Localization.tensorL…
· 使用定理 `Localization.algEquiv_symm_apply`：∀ {R : Type u_1} [inst : CommSemiring 
R] (M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Algebra.mem_algebraMapSubmonoid_of_mem`：mem_algebraMapSubmonoid_of_mem {
M : Submonoid R} (x : M) : algebraMap R S x in algebraMapSubmonoid S M
· 使用定理 `IsLocalization.algebraMap_mk'`：IsLocalization.algebraMap_mk' (x : R) (y 
: M) : algebraMap Rₘ Sₘ (IsLocalization.mk' Rₘ x y) = IsLocalization.mk' Sₘ (alg
ebraMap R S x) ⟨alg…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `IsLocalization.mk'_eq_iff_eq_mul`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `instIsScalarTowerLocalizationAlgebraMapSubmonoid`：∀ {R : Type u_1} [inst
 : CommSemiring R] (M : Submonoid R) (S : Type u_2) [inst_1 : CommSemiring S]   
[inst_2 : Algebra R S], IsScalarTower …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
-/
theorem tensorLeftAlgEquiv_apply_one_tmul (x : Localization M) :
    tensorLeftAlgEquiv M S (1 ⊗ₜ[R] x) = algebraMap _ _ x := by
  let Rₘ := Localization M
  let Sₘ := Localization (Algebra.algebraMapSubmonoid S M)
  obtain ⟨x, y, rfl⟩ := IsLocalization.exists_mk'_eq M x
  let : Algebra Rₘ (S ⊗[R] Rₘ) := Algebra.TensorProduct.rightAlgebra
  have h1 : (1 : S) ⊗ₜ[R] IsLocalization.mk' Rₘ x y = algebraMap _ _ (IsLocalization.mk' Rₘ x y) :=
    rfl
  rw [h1, tensorLeftAlgEquiv, algEquiv_symm_apply,
    IsLocalization.algebraMap_mk' S, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp_rw [RingHom.id_apply]
  have h x : algebraMap S Sₘ ((algebraMap R S) x) = algebraMap Rₘ Sₘ ((algebraMap R Rₘ) x) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [h, h, ← map_mul, IsLocalization.mk'_spec]

/-- The isomorphism `Rₘ ⊗[R] S ≃ₐ[Rₘ] Sₘ`. -/
/-
**Localization.tensorRightAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：tensorRightAlgEquiv : Localization M otimes[R] S ≃ₐ[Localization M] Locali
zation (Algebra.algebraMapSubmonoid S M) where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.tensorLeftAlgEquiv_apply_one_tmul`：tensorLeftAlgEquiv_apply
_one_tmul (x : Localization M) : tensorLeftAlgEquiv M S (1 otimesₜ[R] x) = algeb
raMap _ _ x

--- 原说明 ---
The isomorphism `Rₘ ⊗[R] S ≃ₐ[Rₘ] Sₘ`.
-/
noncomputable def tensorRightAlgEquiv :
    Localization M ⊗[R] S ≃ₐ[Localization M] Localization (Algebra.algebraMapSubmonoid S M) where
  __ := (Algebra.TensorProduct.comm R (Localization M) S).toRingEquiv.trans
    (tensorLeftAlgEquiv M S).toRingEquiv
  commutes' := tensorLeftAlgEquiv_apply_one_tmul M S

@[simp]
/-
**Localization.tensorRightAlgEquiv_apply_tmul_one** 是 Mathlib 中的一个定理，位于命名空间 `Loc
alization`。
形式化陈述：tensorRightAlgEquiv_apply_tmul_one (x : Localization M) : tensorRightAlgEq
uiv M S (x otimesₜ[R] 1) = algebraMap _ _ x
参数：x : Localization M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem tensorRightAlgEquiv_apply_tmul_one (x : Localization M) :
    tensorRightAlgEquiv M S (x ⊗ₜ[R] 1) = algebraMap _ _ x :=
  (tensorRightAlgEquiv M S).commutes x

variable {S} in
@[simp]
/-
**Localization.tensorRightAlgEquiv_apply_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Loc
alization`。
形式化陈述：tensorRightAlgEquiv_apply_one_tmul (x : S) : tensorRightAlgEquiv M S (1 ot
imesₜ[R] x) = algebraMap _ _ x
参数：x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem tensorRightAlgEquiv_apply_one_tmul (x : S) :
    tensorRightAlgEquiv M S (1 ⊗ₜ[R] x) = algebraMap _ _ x :=
  (tensorLeftAlgEquiv M S).commutes x

end Localization

variable (R S) {A} in
/-- `A[M⁻¹] ⊗[R] S` is the localization of `A ⊗[R] S` at `M`. -/
/-
**IsLocalization.tensorProduct_tensorProduct** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalization.tensorProduct_tensorProduct (M : Submonoid A) (B : Type*) [
CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsLocalizatio
n M B] [Algebra (A otimes[R] S) (B otimes[R] S)] [IsScalarTower A (A otimes[R] S
) (B otimes[R] S)] (H : (algebraMap (A otimes[R] S) (B otimes[R] S)).comp Algebr
a.TensorProduct.includeRight.toRingHom = Algebra.TensorProduct.includeRight.toRi
ngHom) : IsLocalization (Algebra.algebraMapSubmonoid (A otimes[R] S) M) (B otime
s[R] S)
参数：M : Submonoid A；B : Type*；A otimes[R] S；B otimes[R] S；A otimes[R] S；B otimes[
R] S；H : (algebraMap (A otimes[R] S) (B otimes[R] S)).comp Algebra.TensorProduct
.includeRight.toRingHom = Algebra.TensorProduct.includeRight.toRingHom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Algebra.isLocalization_iff_isPushout`：Algebra.isLocalization_iff_isPusho
ut : IsLocalization (Algebra.algebraMapSubmonoid T S) B ↔ IsPushout R T A B
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用引理 `Algebra.IsPushout.tensorProduct_tensorProduct`：Algebra.IsPushout.tensorP
roduct_tensorProduct (R S A B : Type*) [CommSemiring R] [CommSemiring S] [CommSe
miring A] [CommSemiring B] [Algebra…

--- 原说明 ---
`A[M⁻¹] ⊗[R] S` is the localization of `A ⊗[R] S` at `M`.
-/
lemma IsLocalization.tensorProduct_tensorProduct (M : Submonoid A)
    (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsLocalization M B]
    [Algebra (A ⊗[R] S) (B ⊗[R] S)] [IsScalarTower A (A ⊗[R] S) (B ⊗[R] S)]
    (H : (algebraMap (A ⊗[R] S) (B ⊗[R] S)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) :
    IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[R] S) M) (B ⊗[R] S) :=
  (Algebra.isLocalization_iff_isPushout M _).mpr
    (Algebra.IsPushout.tensorProduct_tensorProduct R S A B H).symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
variable (R S) {A} in
/-- `S ⊗[R] A[M⁻¹]` is the localization of `S ⊗[R] A` at `M`. -/
/-
**IsLocalization.tensorProduct_tensorProduct_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalization.tensorProduct_tensorProduct_right (M : Submonoid A) (B : Ty
pe*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsLocal
ization M B] [Algebra (S otimes[R] A) (S otimes[R] B)] [IsScalarTower S (S otime
s[R] A) (S otimes[R] B)] (H : (algebraMap (S otimes[R] A) (S otimes[R] B)).comp 
Algebra.TensorProduct.includeRight.toRingHom = Algebra.TensorProduct.includeRigh
t.toRingHom.comp (algebraMap A B)) : IsLocalization (M.map (Algebra.TensorProduc
t.includeRight (R
参数：M : Submonoid A；B : Type*；S otimes[R] A；S otimes[R] B；S otimes[R] A；S otimes[
R] B；H : (algebraMap (S otimes[R] A) (S otimes[R] B)).comp Algebra.TensorProduct
.includeRight.toRingHom = Algebra.TensorProduct.includeRight.toRingHom.comp (alg
ebraMap A B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.compHom_algebraMap_eq`：compHom_algebraMap_eq : letI
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `IsScalarTower.to₁₃₄`：∀ (M : Type u_9) (N : Type u_10) (P : Type u_11) (Q
 : Type u_12) [inst : SMul M N] [inst_1 : SMul M P]   [inst_2 : SMul M Q] [inst_
3 : SMul …
· 使用引理 `Algebra.isLocalization_iff_isPushout`：Algebra.isLocalization_iff_isPusho
ut : IsLocalization (Algebra.algebraMapSubmonoid T S) B ↔ IsPushout R T A B
· 使用定理 `Algebra.IsPushout.comm`：Algebra.IsPushout.comm : Algebra.IsPushout R S R
' S' ↔ Algebra.IsPushout R R' S S'
· 使用引理 `Algebra.IsPushout.comp_iff`：Algebra.IsPushout.comp_iff {T' : Type*} [Com
mSemiring T'] [Algebra R T'] [Algebra S' T'] [Algebra S T'] [Algebra T T'] [Alge
bra R' T'] [IsSc…

--- 原说明 ---
`S ⊗[R] A[M⁻¹]` is the localization of `S ⊗[R] A` at `M`.
-/
lemma IsLocalization.tensorProduct_tensorProduct_right (M : Submonoid A)
    (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsLocalization M B]
    [Algebra (S ⊗[R] A) (S ⊗[R] B)] [IsScalarTower S (S ⊗[R] A) (S ⊗[R] B)]
    (H : (algebraMap (S ⊗[R] A) (S ⊗[R] B)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap A B)) :
    IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) (S ⊗[R] B) := by
  change IsLocalization (Algebra.algebraMapSubmonoid _ M) (S ⊗[R] B)
  let : Algebra A (S ⊗[R] B) := .compHom _ (algebraMap A B)
  have : IsScalarTower A (S ⊗[R] A) (S ⊗[R] B) := .of_algebraMap_eq' H.symm
  have : IsScalarTower R A (S ⊗[R] B) :=
    .of_algebraMap_eq' <| by
      rw [Algebra.compHom_algebraMap_eq, RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq R B]
  have : IsScalarTower R (S ⊗[R] A) (S ⊗[R] B) := .to₁₃₄ _ A _ _
  have : IsScalarTower A B (S ⊗[R] B) := .of_algebraMap_eq' rfl
  rw [Algebra.isLocalization_iff_isPushout _ B, Algebra.IsPushout.comm,
    ← Algebra.IsPushout.comp_iff R _ S]
  infer_instance

variable (R S) {A} in
/-- The natural isomorphism `S ⊗[R] A[M⁻¹] ≃ (S ⊗[R] A)[M⁻¹]`. -/
noncomputable
/-
**IsLocalization.tensorProductEquivOfMapIncludeRight** 是 Mathlib 中的一个定义，位于命名空间 `
`。
形式化陈述：IsLocalization.tensorProductEquivOfMapIncludeRight (M : Submonoid A) (B : 
Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsLoc
alization M B] (C : Type*) [CommSemiring C] [Algebra S C] [Algebra (S otimes[R] 
A) C] [IsScalarTower S (S otimes[R] A) C] [IsLocalization (M.map (Algebra.Tensor
Product.includeRight (R
参数：M : Submonoid A；B : Type*；C : Type*；S otimes[R] A；S otimes[R] A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsLocalization.tensorProductEquivOfMapIncludeRight (M : Submonoid A)
    (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [IsLocalization M B]
    (C : Type*) [CommSemiring C] [Algebra S C] [Algebra (S ⊗[R] A) C] [IsScalarTower S (S ⊗[R] A) C]
    [IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) C] :
    S ⊗[R] B ≃ₐ[S] C :=
  letI M' : Submonoid (S ⊗[R] A) := M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))
  letI : Algebra (S ⊗[R] A) (S ⊗[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R _ _)).toAlgebra
  haveI : IsScalarTower S (S ⊗[R] A) (S ⊗[R] B) :=
    .of_algebraMap_eq <| by intro; simp [RingHom.algebraMap_toAlgebra]
  haveI := IsLocalization.tensorProduct_tensorProduct_right R S M B
    (by ext; simp [RingHom.algebraMap_toAlgebra])
  (IsLocalization.algEquiv M' _ _).restrictScalars S

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**IsLocalization.tensorProductEquivOfMapIncludeRight_tmul** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：IsLocalization.tensorProductEquivOfMapIncludeRight_tmul (M : Submonoid A) 
(B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [
IsLocalization M B] (C : Type*) [CommSemiring C] [Algebra S C] [Algebra (S otime
s[R] A) C] [IsScalarTower S (S otimes[R] A) C] [IsLocalization (M.map (Algebra.T
ensorProduct.includeRight (R
参数：M : Submonoid A；B : Type*；C : Type*；S otimes[R] A；S otimes[R] A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsLocalization.tensorProductEquivOfMapIncludeRight_tmul (M : Submonoid A)
    (B : Type*) [CommSemiring B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [IsLocalization M B]
    (C : Type*) [CommSemiring C] [Algebra S C] [Algebra (S ⊗[R] A) C] [IsScalarTower S (S ⊗[R] A) C]
    [IsLocalization (M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) C]
    (x : S) (a : A) :
    IsLocalization.tensorProductEquivOfMapIncludeRight R S M B C (x ⊗ₜ algebraMap A B a) =
      algebraMap _ _ (x ⊗ₜ[R] a) := by
  let : Algebra (S ⊗[R] A) (S ⊗[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R _ _)).toAlgebra
  have heq : x ⊗ₜ[R] (algebraMap A B) a = algebraMap _ _ (x ⊗ₜ[R] a) := rfl
  simp [heq, IsLocalization.tensorProductEquivOfMapIncludeRight]

variable (R S) {A} in
/-- The natural isomorphism `S ⊗[R] A[1/g] ≃ (S ⊗[R] A)[1/g]`. -/
noncomputable
/-
**IsLocalization.Away.tensorProductEquivTMulRight** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsLocalization.Away.tensorProductEquivTMulRight (g : A) (B : Type*) [CommS
emiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsLocalization.Awa
y g B] : S otimes[R] B ≃ₐ[S] Localization.Away ((1 : S) otimesₜ[R] g)
参数：g : A；B : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsLocalization.Away.tensorProductEquivTMulRight (g : A) (B : Type*) [CommSemiring B]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsLocalization.Away g B] :
    S ⊗[R] B ≃ₐ[S] Localization.Away ((1 : S) ⊗ₜ[R] g) :=
  haveI : IsLocalization
      ((Submonoid.powers g).map (Algebra.TensorProduct.includeRight (R := R) (A := S)))
      (Localization.Away ((1 : S) ⊗ₜ[R] g)) := by
    simp only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply]
    infer_instance
  IsLocalization.tensorProductEquivOfMapIncludeRight _ _ (.powers g) _ _

@[simp]
/-
**IsLocalization.Away.tensorProductEquivTMulRight_tmul** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：IsLocalization.Away.tensorProductEquivTMulRight_tmul (g : A) (B : Type*) [
CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsLocalizatio
n.Away g B] (x : S) (a : A) : IsLocalization.Away.tensorProductEquivTMulRight R 
S g B (x otimesₜ algebraMap _ _ a) = algebraMap _ _ (x otimesₜ[R] a)
参数：g : A；B : Type*；x : S；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.tensorProductEquivOfMapIncludeRight_tmul`：IsLocalization.
tensorProductEquivOfMapIncludeRight_tmul (M : Submonoid A) (B : Type*) [CommSemi
ring B] [Algebra R B] [Algebra A B] [IsScalar…
-/
lemma IsLocalization.Away.tensorProductEquivTMulRight_tmul (g : A) (B : Type*) [CommSemiring B]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [IsLocalization.Away g B]
    (x : S) (a : A) :
    IsLocalization.Away.tensorProductEquivTMulRight R S g B (x ⊗ₜ algebraMap _ _ a) =
      algebraMap _ _ (x ⊗ₜ[R] a) :=
  haveI : IsLocalization
      ((Submonoid.powers g).map (Algebra.TensorProduct.includeRight (R := R) (A := S)))
      (Localization.Away ((1 : S) ⊗ₜ[R] g)) := by
    simp only [Submonoid.map_powers, Algebra.TensorProduct.includeRight_apply]
    infer_instance
  IsLocalization.tensorProductEquivOfMapIncludeRight_tmul _ _ _ _ _ _

namespace IsLocalization.Away

/-
**IsLocalization.Away.tensor** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization.Away`。
形式化陈述：tensor [IsLocalization.Away r A] : IsLocalization.Away (algebraMap R S r) 
(S otimes[R] A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance tensor [IsLocalization.Away r A] :
    IsLocalization.Away (algebraMap R S r) (S ⊗[R] A) := by
  simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  infer_instance

variable (S) in
/-- The `S`-isomorphism `S ⊗[R] Rᵣ ≃ₐ Sᵣ`. -/
/-
**IsLocalization.Away.tensorEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsLocalization.Aw
ay`。
形式化陈述：tensorEquiv [IsLocalization.Away r A] : S otimes[R] A ≃ₐ[S] Localization.A
way (algebraMap R S r)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `S`-isomorphism `S ⊗[R] Rᵣ ≃ₐ Sᵣ`.
-/
noncomputable abbrev tensorEquiv [IsLocalization.Away r A] :
    S ⊗[R] A ≃ₐ[S] Localization.Away (algebraMap R S r) :=
  IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

attribute [local instance] Algebra.TensorProduct.rightAlgebra
/-
**IsLocalization.Away.tensorRight** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization.Away
`。
形式化陈述：tensorRight [IsLocalization.Away r A] : IsLocalization.Away (algebraMap R 
S r) (A otimes[R] S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance tensorRight [IsLocalization.Away r A] :
    IsLocalization.Away (algebraMap R S r) (A ⊗[R] S) := by
  simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  infer_instance

variable (S) in
/-- The `S`-isomorphism `S ⊗[R] Rᵣ ≃ₐ Sᵣ`. -/
/-
**IsLocalization.Away.tensorRightEquiv** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsLocalizati
on.Away`。
形式化陈述：tensorRightEquiv [IsLocalization.Away r A] : A otimes[R] S ≃ₐ[S] Localizat
ion.Away (algebraMap R S r)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `S`-isomorphism `S ⊗[R] Rᵣ ≃ₐ Sᵣ`.
-/
noncomputable abbrev tensorRightEquiv [IsLocalization.Away r A] :
    A ⊗[R] S ≃ₐ[S] Localization.Away (algebraMap R S r) :=
  IsLocalization.algEquiv (Submonoid.powers <| algebraMap R S r) _ _

end IsLocalization.Away

end

