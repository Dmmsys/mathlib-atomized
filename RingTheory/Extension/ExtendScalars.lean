/-
Copyright (c) 2024 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.RingTheory.Kaehler.JacobiZariski

/-!
# Extension of Scalars for Algebra Extensions

This file provides APIs for extending the base ring of an algebra extension `P : Extension R S`
to its own extension ring `P.Ring`. We introduce canonical maps and isomorphisms between
the cotangent spaces and the first homology of naive cotangent complex associated with
`P.extendScalars` and `P`. We provide commutativity results of these maps and ismorphisms
(See https://github.com/leanprover-community/mathlib4/pull/39520 for an image of the full diagram).
In particular, we show the boundary map of the Jacobi-Zariski sequence of `R → P.Ring → S`
coincides with `P.cotangentComplex` via a canonical isomorphism `P.h1CotangentEquivCotangent`.

## Main definitions and results

- `extendScalars`: Views `P : Extension R S` as `Extension P.Ring S`.
- `toExtendScalars`: The canonical homomorphism from `P` to `P.extendScalars` induced by
  the identity map on the underlying extension rings.
- `cotangentExtendScalarsEquiv` : The linear equivalence between the cotangent spaces of
  `P.extensScalars` and `P` induced by the identity map.
- `h1CotangentExtendScalarsEquiv`: `P.extensScalars` can be used to compute the first homology of
  the naive cotangent complex of `S` over `P.Ring`.
- `h1CotangentEquivOfSurjective`: If `R → P.Ring` is surjective, this is the linear isomorphism
  induced by `P.h1Cotangentι`.
- `h1CotangentEquivCotangent`: This is the linear equivalence between `H1Cotangent P.Ring S` and
  `P.Cotangent` defined by the composition of `h1CotangentExtendScalarsEquiv.symm`,
  `h1CotangentEquivOfSurjective` and `cotangentExtendScalarsEquiv`.
- `cotangentComplex_comp_h1CotangentEquivCotangent`,
  `h1CotangentEquivCotangent_comp_map`: commutativity results.

-/

@[expose] public section

open KaehlerDifferential

namespace Algebra.Extension

universe w v u

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Given an extension `P` of `S` over `R`, `P.extendScalars` is the same extension
but viewed as an extension of `S` over `P.Ring`. -/
@[simps]
/-
**Algebra.Extension.extendScalars** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`。
形式化陈述：extendScalars {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra
 R S] (P : Extension.{w} R S) : Extension P.Ring S where Ring
参数：P : Extension.{w} R S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.algebraMap_σ`：∀ {R : Type u} {S : Type v} [inst : Comm
Ring R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : Algebra.Extension
 R S) (x : S), (alge…

--- 原说明 ---
Given an extension `P` of `S` over `R`, `P.extendScalars` is the same extension
but viewed as an extension of `S` over `P.Ring`.
-/
def extendScalars {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{w} R S) : Extension P.Ring S where
  Ring := P.Ring
  σ := P.σ
  algebraMap_σ := P.algebraMap_σ

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical homomorphism from `P` to `P.extendScalars` induced by the identity map
on the underlying extension rings. -/
@[simps!]
noncomputable
/-
**Algebra.Extension.toExtendScalars** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension
`。
形式化陈述：toExtendScalars {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algeb
ra R S] (P : Extension.{w} R S) : P.Hom P.extendScalars
参数：P : Extension.{w} R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toExtendScalars {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (P : Extension.{w} R S) : P.Hom P.extendScalars :=
  .ofAlgHom (IsScalarTower.toAlgHom R P.Ring P.extendScalars.Ring)
    (by dsimp; ext; simp)

/-- `Extension.extendScalars` does not change the cotangent space of an extension. -/
noncomputable
/-
**Algebra.Extension.cotangentExtendScalarsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
ra.Extension`。
形式化陈述：cotangentExtendScalarsEquiv {R : Type u} {S : Type v} [CommRing R] [CommRi
ng S] [Algebra R S] (P : Extension.{w} R S) : P.extendScalars.Cotangent ≃ₗ[S] P.
Cotangent
参数：P : Extension.{w} R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def cotangentExtendScalarsEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) :
    P.extendScalars.Cotangent ≃ₗ[S] P.Cotangent :=
  LinearEquiv.refl _ _

@[simp]
/-
**Algebra.Extension.cotangentExtendScalarsEquiv_symm_toLinearMap** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.Extension`。
形式化陈述：cotangentExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) : P.c
otangentExtendScalarsEquiv.symm.toLinearMap = Cotangent.map P.toExtendScalars
参数：P : Extension.{w} R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
-/
lemma cotangentExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) :
    P.cotangentExtendScalarsEquiv.symm.toLinearMap = Cotangent.map P.toExtendScalars := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Extension.H1Cotangent.map_toExtendScalars_injective** 是 Mathlib 中的一个定理
，位于命名空间 `Algebra.Extension.H1Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   (P : Algebra.Extension R S), Function.Injective ⇑(Algebra.E
xtension.H1Cotangent.map P.toExtendScalars)
参数：P : Algebra.Extension R S；Algebra.Extension.H1Cotangent.map P.toExtendScalars
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Algebra.Extension.H1Cotangent.map.eq_1`：∀ {R : Type u} {S : Type v} [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extens
ion R S}   {R' : Type u'} {S…
· 使用定理 `LinearMap.ker_restrict`：ker_restrict {p : Submodule R M} {q : Submodule 
R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂} (hf : forall x : M, x in p -> f x in q) : ker (f.res
trict hf) = …
· 使用引理 `Algebra.Extension.cotangentExtendScalarsEquiv_symm_toLinearMap`：cotangen
tExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) : P.cotangentExtend
ScalarsEquiv.symm.toLinearMap = Cotangent.map P.toEx…
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
· 使用定理 `Submodule.comap_bot`：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
-/
theorem H1Cotangent.map_toExtendScalars_injective (P : Extension.{w} R S) :
    Function.Injective (H1Cotangent.map P.toExtendScalars) := by
  rw [← LinearMap.ker_eq_bot, H1Cotangent.map, LinearMap.ker_restrict,
    ← cotangentExtendScalarsEquiv_symm_toLinearMap, LinearEquiv.ker,
    Submodule.comap_bot, Submodule.ker_subtype]

/-- The first homology of the naive cotangent complex of `P.extendScalars` is
linearly equivalent to that of `S` over `P.Ring`. -/
@[simps! toLinearMap]
noncomputable
/-
**Algebra.Extension.h1CotangentExtendScalarsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebra.Extension`。
形式化陈述：h1CotangentExtendScalarsEquiv {R : Type u} {S : Type v} [CommRing R] [Comm
Ring S] [Algebra R S] (P : Extension.{w} R S) : P.extendScalars.H1Cotangent ≃ₗ[S
] H1Cotangent P.Ring S
参数：P : Extension.{w} R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def h1CotangentExtendScalarsEquiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) :
    P.extendScalars.H1Cotangent ≃ₗ[S] H1Cotangent P.Ring S :=
  Extension.H1Cotangent.equiv
    (.ofAlgHom (Algebra.ofId _ _) (by ext)) P.extendScalars.defaultHom

@[simp]
/-
**Algebra.Extension.h1CotangentExtendScalarsEquiv_symm_toLinearMap** 是 Mathlib 中
的一个引理，位于命名空间 `Algebra.Extension`。
形式化陈述：h1CotangentExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) : P
.h1CotangentExtendScalarsEquiv.symm = H1Cotangent.map P.extendScalars.defaultHom
参数：P : Extension.{w} R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma h1CotangentExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) :
  P.h1CotangentExtendScalarsEquiv.symm = H1Cotangent.map P.extendScalars.defaultHom := rfl

/-- Given an extension `P` of `S` over `R` such that `algebraMap R P.Ring` is surjective,
this is the equivalence induced by `P.h1Cotangentι`. -/
@[simps! toLinearMap]
noncomputable
/-
**Algebra.Extension.h1CotangentEquivOfSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Alge
bra.Extension`。
形式化陈述：h1CotangentEquivOfSurjective {R : Type u} {S : Type v} [CommRing R] [CommR
ing S] [Algebra R S] (P : Extension.{w} R S) (h : Function.Surjective (algebraMa
p R P.Ring)) : P.H1Cotangent ≃ₗ[S] P.Cotangent where __
参数：P : Extension.{w} R S；h : Function.Surjective (algebraMap R P.Ring)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def h1CotangentEquivOfSurjective {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) (h : Function.Surjective (algebraMap R P.Ring)) :
    P.H1Cotangent ≃ₗ[S] P.Cotangent where
  __ := P.h1Cotangentι
  invFun x := ⟨x, by
    have : Subsingleton Ω[P.Ring⁄R] := subsingleton_of_surjective R P.Ring h
    exact Subsingleton.elim _ _⟩

/-- Given an extension `P : Extension R S`, this is the linear equivalence between
the first homology of the naive cotangent complex of `S` over `P.Ring` and
the cotangent space of `P`. -/
noncomputable
/-
**Algebra.Extension.h1CotangentEquivCotangent** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
.Extension`。
形式化陈述：h1CotangentEquivCotangent {R : Type u} {S : Type v} [CommRing R] [CommRing
 S] [Algebra R S] (P : Extension.{w} R S) : H1Cotangent P.Ring S ≃ₗ[S] P.Cotange
nt
参数：P : Extension.{w} R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def h1CotangentEquivCotangent {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (P : Extension.{w} R S) :
    H1Cotangent P.Ring S ≃ₗ[S] P.Cotangent :=
  P.h1CotangentExtendScalarsEquiv.symm ≪≫ₗ
    P.extendScalars.h1CotangentEquivOfSurjective Function.surjective_id ≪≫ₗ
    P.cotangentExtendScalarsEquiv

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.Extension.cotangentComplex_comp_h1CotangentEquivCotangent** 是 Mathlib 
中的一个定理，位于命名空间 `Algebra.Extension`。
形式化陈述：cotangentComplex_comp_h1CotangentEquivCotangent (P : Extension.{w} R S) : 
P.cotangentComplex.comp P.h1CotangentEquivCotangent.toLinearMap = H1Cotangent.δ 
R P.Ring S
参数：P : Extension.{w} R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.h1CotangentEquivCotangent.eq_1`：∀ {R : Type u} {S : Ty
pe v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P : Al
gebra.Extension R S),   P.h1CotangentE…
· 使用定理 `LinearEquiv.coe_trans`：coe_trans : (e₁₂.trans e₂₃ : M₁ ->ₛₗ[σ₁₃] M₃) = (
e₂₃ : M₂ ->ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `Algebra.Extension.h1CotangentEquivOfSurjective_toLinearMap`：∀ {R : Type 
u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]
 (P : Algebra.Extension R S)   (h : Function.Sur…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearEquiv.comp_toLinearMap_symm_eq`：comp_toLinearMap_symm_eq (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : g.comp e₁₂.symm.toLinearMap = f ↔ g = f.com
p e₁₂.toLinearMap
· 使用定理 `Algebra.Extension.h1CotangentExtendScalarsEquiv_toLinearMap`：∀ {R : Type
 u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S
]   (P : Algebra.Extension R S),   ↑P.h1Cotangent…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用引理 `Algebra.Extension.cotangentComplex_mk`：cotangentComplex_mk (x) : P.cotan
gentComplex (.mk x) = 1 otimesₜ .D _ _ x
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Algebra.Extension.Cotangent.mk_C_mem_ker_cotangentComplex`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{σ : Type u_1}   (G : Algebra.Generators R S σ)…
· 使用引理 `Algebra.Generators.H1Cotangent.δ_C`：δ_C {r : S} (hr : C r in Q.ker) : δ 
Q P ⟨Extension.Cotangent.mk ⟨C r, hr⟩, Extension.Cotangent.mk_C_mem_ker_cotangen
tComplex ..⟩ = 1 otimesₜ…
-/
theorem cotangentComplex_comp_h1CotangentEquivCotangent (P : Extension.{w} R S) :
    P.cotangentComplex.comp P.h1CotangentEquivCotangent.toLinearMap =
      H1Cotangent.δ R P.Ring S := by
  rw [h1CotangentEquivCotangent, LinearEquiv.coe_trans, LinearEquiv.coe_trans,
    h1CotangentEquivOfSurjective_toLinearMap, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc,
    LinearEquiv.comp_toLinearMap_symm_eq, LinearMap.comp_assoc,
    h1CotangentExtendScalarsEquiv_toLinearMap]
  ext ⟨x, _⟩
  obtain ⟨⟨x : P.Ring, x_in : x ∈ P.ker⟩, rfl⟩ := Cotangent.mk_surjective x
  trans 1 ⊗ₜ[P.Ring] D R P.Ring x; · exact cotangentComplex_mk P ⟨x, x_in⟩
  let u : (Generators.self P.Ring S).toExtension.ker :=
    ⟨algebraMap P.Ring (Generators.self P.Ring S).toExtension.Ring x, by
      rwa [← Ideal.mem_comap, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq]⟩
  rw [← Generators.H1Cotangent.δ_C _ _ u.prop]
  congr

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.Extension.h1CotangentEquivCotangent_comp_map** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra.Extension`。
形式化陈述：h1CotangentEquivCotangent_comp_map (P : Extension.{w} R S) : P.h1Cotangent
EquivCotangent.toLinearMap.comp (Algebra.H1Cotangent.map R P.Ring S S) = h1Cotan
gentι.comp (H1Cotangent.map P.defaultHom)
参数：P : Extension.{w} R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.h1CotangentEquivCotangent.eq_1`：∀ {R : Type u} {S : Ty
pe v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P : Al
gebra.Extension R S),   P.h1CotangentE…
· 使用定理 `LinearEquiv.coe_trans`：coe_trans : (e₁₂.trans e₂₃ : M₁ ->ₛₗ[σ₁₃] M₃) = (
e₂₃ : M₂ ->ₛₗ[σ₂₃] M₃).comp (e₁₂ : M₁ ->ₛₗ[σ₁₂] M₂)
· 使用引理 `Algebra.Extension.h1CotangentExtendScalarsEquiv_symm_toLinearMap`：h1Cota
ngentExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) : P.h1Cotangent
ExtendScalarsEquiv.symm = H1Cotangent.map P.extendScal…
· 使用定理 `Algebra.Extension.h1CotangentEquivOfSurjective_toLinearMap`：∀ {R : Type 
u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]
 (P : Algebra.Extension R S)   (h : Function.Sur…
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `Algebra.H1Cotangent.map.eq_1`：∀ (R : Type u) (S : Type v) [inst : CommRi
ng R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (S' : Type u_2)   [inst_3 : C
ommRing S'] [inst_…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.restrictScalars_self`：restrictScalars_self (f : M ->ₗ[R] M₂) :
 f.restrictScalars R = f
· 使用定理 `Algebra.Extension.instIsScalarTowerH1CotangentOfCotangent`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{P : Algebra.Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Algebra.Extension.H1Cotangent.map_comp`：∀ {R : Type u} {S : Type v} [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extens
ion R S}   {R' : Type u'} {S…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `LinearEquiv.toLinearMap_symm_comp_eq`：toLinearMap_symm_comp_eq (f : M₃ -
>ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.t
oLinearMap.comp f
· 使用引理 `Algebra.Extension.cotangentExtendScalarsEquiv_symm_toLinearMap`：cotangen
tExtendScalarsEquiv_symm_toLinearMap (P : Extension.{w} R S) : P.cotangentExtend
ScalarsEquiv.symm.toLinearMap = Cotangent.map P.toEx…
· 使用定理 `Algebra.Extension.Cotangent.map_comp_h1Cotangentι`：∀ {R : Type u} {S : T
ype v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Alg
ebra.Extension R S}   {R' : Type u'} {S…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_1`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `Algebra.Extension.H1Cotangent.map_eq`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   {R' : Type u'} {S…
-/
theorem h1CotangentEquivCotangent_comp_map (P : Extension.{w} R S) :
    P.h1CotangentEquivCotangent.toLinearMap.comp (Algebra.H1Cotangent.map R P.Ring S S) =
      h1Cotangentι.comp (H1Cotangent.map P.defaultHom) := by
  rw [h1CotangentEquivCotangent, LinearEquiv.coe_trans, LinearEquiv.coe_trans,
    h1CotangentExtendScalarsEquiv_symm_toLinearMap, h1CotangentEquivOfSurjective_toLinearMap,
    LinearMap.comp_assoc, LinearMap.comp_assoc, Algebra.H1Cotangent.map,
    ← (H1Cotangent.map P.extendScalars.defaultHom).restrictScalars_self, ← H1Cotangent.map_comp,
    eq_comm, ← LinearEquiv.toLinearMap_symm_comp_eq, cotangentExtendScalarsEquiv_symm_toLinearMap,
    ← LinearMap.comp_assoc, Cotangent.map_comp_h1Cotangentι, LinearMap.restrictScalars_self,
    LinearMap.comp_assoc, ← (H1Cotangent.map P.toExtendScalars).restrictScalars_self,
    ← H1Cotangent.map_comp, H1Cotangent.map_eq]
/-
**Algebra.Extension.H1Cotangent.map_defaultHom_surjective** 是 Mathlib 中的一个定理，位于命
名空间 `Algebra.Extension.H1Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   (P : Algebra.Extension R S),   Function.Surjective ⇑(Algebr
a.Extension.H1Cotangent.map (Algebra.Extension.defaultHom R S P))
参数：P : Algebra.Extension R S；Algebra.Extension.H1Cotangent.map (Algebra.Extensio
n.defaultHom R S P)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用引理 `Algebra.Extension.h1Cotangentι_injective`：h1Cotangentι_injective : Funct
ion.Injective P.h1Cotangentι
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `Algebra.Extension.h1CotangentEquivCotangent_comp_map`：h1CotangentEquivCo
tangent_comp_map (P : Extension.{w} R S) : P.h1CotangentEquivCotangent.toLinearM
ap.comp (Algebra.H1Cotangent.map R P.Ring …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `Algebra.H1Cotangent.exact_map_δ`：∀ (R : Type u₁) (S : Type u₂) [inst : C
ommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (T : Type u₃)   [inst_3 
: CommRing T] [inst_4…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用引理 `Algebra.Extension.exact_hCotangentι_cotangentComplex`：exact_hCotangentι_
cotangentComplex : Function.Exact h1Cotangentι P.cotangentComplex
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.map_equiv_eq_comap_symm`：map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R M) : K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ -
>ₛₗ[τ₂₁] M)
· 使用定理 `LinearMap.ker.eq_1`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ 
: Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid
 M] [ins…
· 使用定理 `Submodule.comap_comp`：comap_comp (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] 
M₃) (p : Submodule R₃ M₃) : comap (g.comp f : M ->ₛₗ[σ₁₃] M₃) p = comap f (comap
 g p)
· 使用定理 `LinearEquiv.comp_toLinearMap_symm_eq`：comp_toLinearMap_symm_eq (f : M₂ -
>ₛₗ[σ₂₃] M₃) (g : M₁ ->ₛₗ[σ₁₃] M₃) : g.comp e₁₂.symm.toLinearMap = f ↔ g = f.com
p e₁₂.toLinearMap
· 使用定理 `Algebra.Extension.cotangentComplex_comp_h1CotangentEquivCotangent`：cotan
gentComplex_comp_h1CotangentEquivCotangent (P : Extension.{w} R S) : P.cotangent
Complex.comp P.h1CotangentEquivCotangent.toLinearMap = …
-/
theorem H1Cotangent.map_defaultHom_surjective (P : Extension.{w} R S) :
    Function.Surjective (H1Cotangent.map P.defaultHom) := by
  rw [← LinearMap.range_eq_top,
    ← (Submodule.map_injective_of_injective h1Cotangentι_injective).eq_iff,
    ← LinearMap.range_comp, ← P.h1CotangentEquivCotangent_comp_map, LinearMap.range_comp,
    ← (Algebra.H1Cotangent.exact_map_δ R P.Ring S).linearMap_ker_eq, Submodule.map_top,
    ← exact_hCotangentι_cotangentComplex.linearMap_ker_eq, Submodule.map_equiv_eq_comap_symm,
    LinearMap.ker, LinearMap.ker, ← Submodule.comap_comp]
  congr
  rw [LinearEquiv.comp_toLinearMap_symm_eq, P.cotangentComplex_comp_h1CotangentEquivCotangent]

end Algebra.Extension

