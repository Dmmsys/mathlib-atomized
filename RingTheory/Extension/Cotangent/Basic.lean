/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!

# Naive cotangent complex associated to a presentation.

Given a presentation `0 → I → R[x₁,...,xₙ] → S → 0` (or equivalently a closed embedding `S ↪ Aⁿ`
defined by `I`), we may define the (naive) cotangent complex `I/I² → ⨁ᵢ S dxᵢ → Ω[S/R] → 0`.

## Main results
- `Algebra.Extension.Cotangent`: The conormal space `I/I²`. (Defined in `Generators/Basic`)
- `Algebra.Extension.CotangentSpace`: The cotangent space `⨁ᵢ S dxᵢ`.
- `Algebra.Generators.cotangentSpaceBasis`: The canonical basis on `⨁ᵢ S dxᵢ`.
- `Algebra.Extension.CotangentComplex`: The map `I/I² → ⨁ᵢ S dxᵢ`.
- `Algebra.Extension.toKaehler`: The projection `⨁ᵢ S dxᵢ → Ω[S/R]`.
- `Algebra.Extension.toKaehler_surjective`: The map `⨁ᵢ S dxᵢ → Ω[S/R]` is surjective.
- `Algebra.Extension.exact_cotangentComplex_toKaehler`: `I/I² → ⨁ᵢ S dxᵢ → Ω[S/R]` is exact.
- `Algebra.Extension.Hom.Sub`: If `f` and `g` are two maps between presentations, `f - g` induces
  a map `⨁ᵢ S dxᵢ → I/I²` that makes `f` and `g` homotopic.
- `Algebra.Extension.H1Cotangent`: The first homology of the (naive) cotangent complex
  of `S` over `R`, induced by a given presentation.
- `Algebra.H1Cotangent`: `H¹(L_{S/R})`,
  the first homology of the (naive) cotangent complex of `S` over `R`.

## Implementation detail
We actually develop these material for general extensions (i.e. surjection `P → S`) so that we can
apply them to infinitesimal smooth (or versal) extensions later.

-/

@[expose] public noncomputable section

open KaehlerDifferential Module MvPolynomial TensorProduct

namespace Algebra

universe w u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

namespace Extension

variable (P : Extension.{w} R S)

/--
The cotangent space on `P = R[X]`.
This is isomorphic to `Sⁿ` with `n` being the number of variables of `P`.
-/
/-
**Algebra.Extension.CotangentSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra.Extensio
n`。
形式化陈述：CotangentSpace : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cotangent space on `P = R[X]`.
This is isomorphic to `Sⁿ` with `n` being the number of variables of `P`.
-/
abbrev CotangentSpace : Type _ := S ⊗[P.Ring] Ω[P.Ring⁄R]

/-- The cotangent complex given by a presentation `R[X] → S` (i.e. a closed embedding `S ↪ Aⁿ`). -/
/-
**Algebra.Extension.cotangentComplex** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extensio
n`。
形式化陈述：cotangentComplex : P.Cotangent ->ₗ[S] P.CotangentSpace
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Extension.algebraMap_surjective`：algebraMap_surjective : Functio
n.Surjective (algebraMap P.Ring S)
· 使用定理 `Algebra.Extension.Cotangent.val_smul'`：∀ {R : Type u} {S : Type v} [inst
 : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensi
on R S}   (r : P.Ring) (x :…

--- 原说明 ---
The cotangent complex given by a presentation `R[X] → S` (i.e. a closed embeddin
g `S ↪ Aⁿ`).
-/
def cotangentComplex : P.Cotangent →ₗ[S] P.CotangentSpace :=
  letI f : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' := Cotangent.val_smul' }
  (kerCotangentToTensor R P.Ring S ∘ₗ f).extendScalarsOfSurjective P.algebraMap_surjective

@[simp]
/-
**Algebra.Extension.cotangentComplex_mk** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Exten
sion`。
形式化陈述：cotangentComplex_mk (x) : P.cotangentComplex (.mk x) = 1 otimesₜ .D _ _ x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma cotangentComplex_mk (x) : P.cotangentComplex (.mk x) = 1 ⊗ₜ .D _ _ x :=
  rfl
/-
**Algebra.Extension.Cotangent.mk_C_mem_ker_cotangentComplex** 是 Mathlib 中的一个定理，位
于命名空间 `Algebra.Extension.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {σ : Type u_1}   (G : Algebra.Generators R S σ) {r : R} (hr :
 MvPolynomial.C r ∈ G.ker),   Algebra.Extension.Cotangent.mk ⟨MvPolynomial.C r, 
hr⟩ ∈ G.toExtension.cotangentComplex.ker
参数：G : Algebra.Generators R S σ；hr : MvPolynomial.C r ∈ G.ker。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Derivation.map_algebraMap`：map_algebraMap : D (algebraMap R A r) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Cotangent.mk_C_mem_ker_cotangentComplex {σ : Type*} (G : Generators R S σ)
    {r : R} (hr : C r ∈ G.ker) :
    Extension.Cotangent.mk ⟨C r, hr⟩ ∈ G.toExtension.cotangentComplex.ker := by
  have : D R G.toExtension.Ring (C r) = 0 := Derivation.map_algebraMap ..
  simp [this]

section baseChange

variable {A : Type*} [CommRing A] [Algebra S A] [Algebra P.Ring A] [IsScalarTower P.Ring S A]

variable (R S) in
/-- This is (isomorphic to) the base change of the cotangent complex to `A`, but
the domain and codomains of this are more manageable. -/
/-
**Algebra.Extension._root_.KaehlerDifferential.cotangentComplexBaseChange** 是 Ma
thlib 中的一个定义，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is (isomorphic to) the base change of the cotangent complex to `A`, but
the domain and codomains of this are more manageable.
-/
def _root_.KaehlerDifferential.cotangentComplexBaseChange
    (P A : Type*) [CommRing P] [CommRing A] [Algebra P S] [Algebra P A]
    [Algebra R P] [Algebra S A] [IsScalarTower P S A] :
    A ⊗[P] RingHom.ker (algebraMap P S) →ₗ[A] A ⊗[P] Ω[P⁄R] :=
  LinearMap.liftBaseChange _ (KaehlerDifferential.kerToTensor _ _ _ ∘ₗ Submodule.inclusion
    (by rw [IsScalarTower.algebraMap_eq P S A]; intro; aesop))

omit [Algebra R S] in
/-
**Algebra.Extension._root_.KaehlerDifferential.cotangentComplexBaseChange_tmul**
 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.KaehlerDifferential.cotangentComplexBaseChange_tmul
    {P A : Type*} [CommRing P] [CommRing A] [Algebra P S]
    [Algebra P A] [Algebra R P] [Algebra S A] [IsScalarTower P S A] (a b) :
  cotangentComplexBaseChange R S P A (a ⊗ₜ b) =
    a • kerToTensor R P A ⟨b.1, by rw [IsScalarTower.algebraMap_eq P S A]; aesop⟩ := rfl

variable (A) in
/-
**Algebra.Extension.cotangentComplexBaseChange_eq_lTensor_cotangentComplex** 是 M
athlib 中的一个引理，位于命名空间 `Algebra.Extension`。
形式化陈述：cotangentComplexBaseChange_eq_lTensor_cotangentComplex : cotangentComplexB
aseChange R S P.Ring A = AlgebraTensorModule.cancelBaseChange P.Ring S A A Ω[P.R
ing⁄R] ∘ₗ P.cotangentComplex.baseChange A ∘ₗ ((AlgebraTensorModule.cancelBaseCha
nge P.Ring S A A P.ker).symm ≪≫ₗ P.cotangentEquiv.baseChange (A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
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
· 使用定理 `KaehlerDifferential.kerToTensor_apply`：∀ (R : Type u) [inst : CommRing R
] (A : Type u_2) (B : Type u_3) [inst_1 : CommRing A] [inst_2 : CommRing B]   [i
nst_3 : Algebra R A] [inst_…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cotangentComplexBaseChange_eq_lTensor_cotangentComplex :
  cotangentComplexBaseChange R S P.Ring A =
    AlgebraTensorModule.cancelBaseChange P.Ring S A A Ω[P.Ring⁄R] ∘ₗ
      P.cotangentComplex.baseChange A ∘ₗ
      ((AlgebraTensorModule.cancelBaseChange P.Ring S A A P.ker).symm ≪≫ₗ
        P.cotangentEquiv.baseChange (A := A)) := by
  ext x
  simp [LinearEquiv.baseChange, cotangentComplexBaseChange_tmul]

variable (A) in
/-
**Algebra.Extension.lTensor_cotangentComplex_eq_cotangentComplexBaseChange** 是 M
athlib 中的一个引理，位于命名空间 `Algebra.Extension`。
形式化陈述：lTensor_cotangentComplex_eq_cotangentComplexBaseChange : P.cotangentComple
x.baseChange A = (AlgebraTensorModule.cancelBaseChange P.Ring S A A Ω[P.Ring⁄R])
.symm ∘ₗ cotangentComplexBaseChange R S P.Ring A ∘ₗ ((AlgebraTensorModule.cancel
BaseChange P.Ring S A A P.ker).symm ≪≫ₗ P.cotangentEquiv.baseChange (A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.coe_injective`：coe_injective : Injective (DFunLike.coe : (M ->
ₛₗ[σ] M₃) -> _)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.eq_symm_comp`：eq_symm_comp {α : Type*} (f : α -> M₁) (g : α 
-> M₂) : f = e₁₂.symm ∘ g ↔ e₁₂ ∘ f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.comp_symm_eq`：comp_symm_eq {α : Type*} (f : M₂ -> α) (g : M₁
 -> α) : g ∘ e₁₂.symm = f ↔ g = f ∘ e₁₂
· 使用引理 `Algebra.Extension.cotangentComplexBaseChange_eq_lTensor_cotangentComplex
`：cotangentComplexBaseChange_eq_lTensor_cotangentComplex : cotangentComplexBaseC
hange R S P.Ring A = AlgebraTensorModule.cancelBaseChange P.Ri…
-/
lemma lTensor_cotangentComplex_eq_cotangentComplexBaseChange :
  P.cotangentComplex.baseChange A =
    (AlgebraTensorModule.cancelBaseChange P.Ring S A A Ω[P.Ring⁄R]).symm ∘ₗ
      cotangentComplexBaseChange R S P.Ring A ∘ₗ
      ((AlgebraTensorModule.cancelBaseChange P.Ring S A A P.ker).symm ≪≫ₗ
        P.cotangentEquiv.baseChange (A := A)).symm := by
  apply LinearMap.coe_injective
  dsimp
  rw [LinearEquiv.eq_symm_comp, ← LinearEquiv.comp_symm_eq]
  exact congr(($(cotangentComplexBaseChange_eq_lTensor_cotangentComplex P A) : _ → _)).symm

end baseChange

universe w' u' v'

variable {R' : Type u'} {S' : Type v'} [CommRing R'] [CommRing S'] [Algebra R' S']
variable (P' : Extension.{w'} R' S')
variable [Algebra R R'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S']

attribute [local instance] SMulCommClass.of_commMonoid

variable {P P'}

universe w'' u'' v''

variable {R'' : Type u''} {S'' : Type v''} [CommRing R''] [CommRing S''] [Algebra R'' S'']
variable {P'' : Extension.{w''} R'' S''}
variable [Algebra R R''] [Algebra S S''] [Algebra R S'']
  [IsScalarTower R R'' S'']
variable [Algebra R' R''] [Algebra S' S''] [Algebra R' S'']
  [IsScalarTower R' R'' S'']
variable [IsScalarTower R R' R''] [IsScalarTower S S' S'']

namespace CotangentSpace

/--
This is the map on the cotangent space associated to a map of presentation.
The matrix associated to this map is the Jacobian matrix. See `CotangentSpace.repr_map`.
-/
/-
**Algebra.Extension.CotangentSpace.map** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extens
ion.CotangentSpace`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {P : Algebra.Extension 
R S} →             {R' : Type u'} →               {S' : Type v'} →              
   [inst_3 : CommRing R'] →                   [inst_4 : CommRing S'] →          
           [inst_5 : Algebra R' S'] →                       {P' : Algebra.Extens
ion R' S'} →                         [inst_6 : Algebra R R'] →                  
         [inst_7 : Algebra S S'] →                             [inst_8 : Algebra
 R S'] →                               [IsScalarTower R R' S'] → P.Hom P' → P.Co
tangentSpace →ₗ[S] P'.CotangentSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the map on the cotangent space associated to a map of presentation.
The matrix associated to this map is the Jacobian matrix. See `CotangentSpace.re
pr_map`.
-/
protected def map (f : Hom P P') : P.CotangentSpace →ₗ[S] P'.CotangentSpace := by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S S' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring S' :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ (f.algebraMap_toRingHom x).symm)
  apply LinearMap.liftBaseChange
  refine (TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ KaehlerDifferential.map R R' P.Ring P'.Ring

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Algebra.Extension.CotangentSpace.map_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.E
xtension.CotangentSpace`。
形式化陈述：map_tmul (f : Hom P P') (x y) : CotangentSpace.map f (x otimesₜ .D _ _ y) 
= (algebraMap _ _ x) otimesₜ .D _ _ (f.toAlgHom y)
参数：f : Hom P P'；x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `KaehlerDifferential.map_D`：KaehlerDifferential.map_D (x : A) : KaehlerDi
fferential.map R S A B (KaehlerDifferential.D R A x) = KaehlerDifferential.D S B
 (algebraMap A …
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
lemma map_tmul (f : Hom P P') (x y) :
    CotangentSpace.map f (x ⊗ₜ .D _ _ y) = (algebraMap _ _ x) ⊗ₜ .D _ _ (f.toAlgHom y) := by
  simp only [CotangentSpace.map, AlgHom.toRingHom_eq_coe, LinearMap.liftBaseChange_tmul,
    LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, map_D, mk_apply]
  rw [smul_tmul', ← Algebra.algebraMap_eq_smul_one]
  rfl
/-
**Algebra.Extension.CotangentSpace.map_tmul_eq_tmul_map** 是 Mathlib 中的一个引理，位于命名空
间 `Algebra.Extension.CotangentSpace`。
形式化陈述：map_tmul_eq_tmul_map (f : P.Hom P') (x : S) (y : Ω[P.Ring⁄R]) : letI : Alg
ebra P.Ring P'.Ring
参数：f : P.Hom P'；x : S；y : Ω[P.Ring⁄R]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_1`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.CotangentSpace.map.eq_1`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Ext
ension R S}   {R' : Type u'} {S…
· 使用引理 `LinearMap.liftBaseChange_tmul`：liftBaseChange_tmul (l : M ->ₗ[R] N) (x y
) : l.liftBaseChange A (x otimesₜ y) = x • l y
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LinearMap.restrictScalars_apply`：restrictScalars_apply (fₗ : M ->ₗ[S] M₂
) (x) : restrictScalars R fₗ x = fₗ x
· 使用定理 `TensorProduct.mk_apply`：mk_apply (m : M) (n : N) : mk R M N m n = m otim
esₜ n
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma map_tmul_eq_tmul_map (f : P.Hom P') (x : S) (y : Ω[P.Ring⁄R]) :
    letI : Algebra P.Ring P'.Ring := f.toAlgHom.toAlgebra
    (CotangentSpace.map f) (x ⊗ₜ[P.Ring] y) =
      (algebraMap S S') x ⊗ₜ[P'.Ring] KaehlerDifferential.map _ _ _ _ y := by
  rw [CotangentSpace.map, LinearMap.liftBaseChange_tmul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.restrictScalars_apply, mk_apply, smul_tmul', Algebra.smul_def, mul_one]

@[simp]
/-
**Algebra.Extension.CotangentSpace.map_id** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Ext
ension.CotangentSpace`。
形式化陈述：map_id : CotangentSpace.map (.id P) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Derivation.liftKaehlerDifferential_unique`：Derivation.liftKaehlerDiffere
ntial_unique (f f' : Ω[S⁄R] ->ₗ[S] M) (hf : f.compDer (KaehlerDifferential.D R S
) = f'.compDer (KaehlerDifferen…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `Derivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
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
· 使用引理 `Algebra.Extension.CotangentSpace.map_tmul`：map_tmul (f : Hom P P') (x y)
 : CotangentSpace.map f (x otimesₜ .D _ _ y) = (algebraMap _ _ x) otimesₜ .D _ _
 (f.toAlgHom y)
· 使用定理 `Algebra.Extension.Hom.toAlgHom_id`：∀ {R : Type u} {S : Type v} [inst : C
ommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P : Algebra.Extension
 R S), (Algebra.Extensi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id :
    CotangentSpace.map (.id P) = LinearMap.id := by ext; simp
/-
**Algebra.Extension.CotangentSpace.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.E
xtension.CotangentSpace`。
形式化陈述：map_comp (f : Hom P P') (g : Hom P' P'') : CotangentSpace.map (g.comp f) =
 (CotangentSpace.map g).restrictScalars S ∘ₗ CotangentSpace.map f
参数：f : Hom P P'；g : Hom P' P''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `KaehlerDifferential.tensorProductTo_surjective`：KaehlerDifferential.tens
orProductTo_surjective : Function.Surjective (KaehlerDifferential.D R S).tensorP
roductTo
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用引理 `Algebra.Extension.CotangentSpace.map_tmul`：map_tmul (f : Hom P P') (x y)
 : CotangentSpace.map f (x otimesₜ .D _ _ y) = (algebraMap _ _ x) otimesₜ .D _ _
 (f.toAlgHom y)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.Extension.Hom.comp_toRingHom`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   {R' : Type u_1} {…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
-/
lemma map_comp (f : Hom P P') (g : Hom P' P'') :
    CotangentSpace.map (g.comp f) =
      (CotangentSpace.map g).restrictScalars S ∘ₗ CotangentSpace.map f := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
  | add =>
    simp only [map_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero]
    | add => simp only [map_add, tmul_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, *]
    | tmul => simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', map_tmul,
        Hom.toAlgHom_apply, Hom.comp_toRingHom, RingHom.coe_comp, Function.comp_apply,
        LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        ← IsScalarTower.algebraMap_apply S S' S'']
/-
**Algebra.Extension.CotangentSpace.map_comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebra.Extension.CotangentSpace`。
形式化陈述：map_comp_apply (f : Hom P P') (g : Hom P' P'') (x) : CotangentSpace.map (g
.comp f) x = .map g (.map f x)
参数：f : Hom P P'；g : Hom P' P''；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `Algebra.Extension.CotangentSpace.map_comp`：map_comp (f : Hom P P') (g : 
Hom P' P'') : CotangentSpace.map (g.comp f) = (CotangentSpace.map g).restrictSca
lars S ∘ₗ CotangentSpace.map f
-/
lemma map_comp_apply (f : Hom P P') (g : Hom P' P'') (x) :
    CotangentSpace.map (g.comp f) x = .map g (.map f x) :=
  DFunLike.congr_fun (map_comp f g) x
/-
**Algebra.Extension.CotangentSpace.map_cotangentComplex** 是 Mathlib 中的一个引理，位于命名空
间 `Algebra.Extension.CotangentSpace`。
形式化陈述：map_cotangentComplex (f : Hom P P') (x) : CotangentSpace.map f (P.cotangen
tComplex x) = P'.cotangentComplex (.map f x)
参数：f : Hom P P'；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.Extension.cotangentComplex_mk`：cotangentComplex_mk (x) : P.cotan
gentComplex (.mk x) = 1 otimesₜ .D _ _ x
· 使用引理 `Algebra.Extension.CotangentSpace.map_tmul`：map_tmul (f : Hom P P') (x y)
 : CotangentSpace.map f (x otimesₜ .D _ _ y) = (algebraMap _ _ x) otimesₜ .D _ _
 (f.toAlgHom y)
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
· 使用定理 `Algebra.Extension.Cotangent.map_mk`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension 
R S}   {R' : Type u_1} {…
-/
lemma map_cotangentComplex (f : Hom P P') (x) :
    CotangentSpace.map f (P.cotangentComplex x) = P'.cotangentComplex (.map f x) := by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  rw [cotangentComplex_mk, map_tmul, map_one, Cotangent.map_mk, cotangentComplex_mk]
/-
**Algebra.Extension.CotangentSpace.map_comp_cotangentComplex** 是 Mathlib 中的一个引理，
位于命名空间 `Algebra.Extension.CotangentSpace`。
形式化陈述：map_comp_cotangentComplex (f : Hom P P') : CotangentSpace.map f ∘ₗ P.cotan
gentComplex = P'.cotangentComplex.restrictScalars S ∘ₗ Cotangent.map f
参数：f : Hom P P'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用引理 `Algebra.Extension.CotangentSpace.map_cotangentComplex`：map_cotangentComp
lex (f : Hom P P') (x) : CotangentSpace.map f (P.cotangentComplex x) = P'.cotang
entComplex (.map f x)
-/
lemma map_comp_cotangentComplex (f : Hom P P') :
    CotangentSpace.map f ∘ₗ P.cotangentComplex =
      P'.cotangentComplex.restrictScalars S ∘ₗ Cotangent.map f := by
  ext x; exact map_cotangentComplex f x

end CotangentSpace

/-
**Algebra.Extension.Hom.sub_aux** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extension.Hom
`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u'} {S' : Type v'} [
inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : Al
gebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8 :
 Algebra R S']   [inst_9 : IsScalarTower R R' S'] (f g : P.Hom P') (x y : P.Ring
),   f.toAlgHom (x * y) - g.toAlgHom (x * y) -       (P'.σ ((algebraMap P.Ring S
') x) * (f.toAlgHom y - g.toAlgHom y) +         P'.σ ((algebraMap P.Ring S') y) 
* (f.toAlgHom x - g.toAlgHom x)) ∈     P'.ker ^ 2
参数：f g : P.Hom P'；x y : P.Ring；x * y；x * y；P'.σ ((algebraMap P.Ring S') x) * (f.
toAlgHom y - g.toAlgHom y) +         P'.σ ((algebraMap P.Ring S') y) * (f.toAlgH
om x - g.toAlgHom x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.Extension.Hom.algebraMap_toRingHom`：∀ {R : Type u} {S : Type v} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Ex
tension R S}   {R' : Type u_1} {…
· 使用定理 `Algebra.Extension.algebraMap_σ`：∀ {R : Type u} {S : Type v} [inst : Comm
Ring R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : Algebra.Extension
 R S) (x : S), (alge…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 50 条，此处仅展示前 30 条）
-/
lemma Hom.sub_aux (f g : Hom P P') (x y) :
    letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
    f.toAlgHom (x * y) - g.toAlgHom (x * y) -
        (P'.σ ((algebraMap P.Ring S') x) * (f.toAlgHom y - g.toAlgHom y) +
          P'.σ ((algebraMap P.Ring S') y) * (f.toAlgHom x - g.toAlgHom x)) ∈
      P'.ker ^ 2 := by
  let := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  have :
      (f.toAlgHom x - P'.σ (algebraMap P.Ring S' x)) * (f.toAlgHom y - g.toAlgHom y) +
      (g.toAlgHom y - P'.σ (algebraMap P.Ring S' y)) * (f.toAlgHom x - g.toAlgHom x)
        ∈ P'.ker ^ 2 := by
    rw [pow_two]
    refine Ideal.add_mem _ (Ideal.mul_mem_mul ?_ ?_) (Ideal.mul_mem_mul ?_ ?_) <;>
      simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp,
        Function.comp_apply,
        ker, RingHom.mem_ker, map_sub, algebraMap_toRingHom,
        algebraMap_σ, sub_self, toAlgHom_apply]
  convert! this using 1
  simp only [map_mul]
  ring

/--
If `f` and `g` are two maps `P → P'` between presentations,
then the image of `f - g` is in the kernel of `P' → S`.
-/
@[simps! apply_coe]
/-
**Algebra.Extension.Hom.subToKer** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.Ho
m`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {P : Algebra.Extension 
R S} →             {R' : Type u'} →               {S' : Type v'} →              
   [inst_3 : CommRing R'] →                   [inst_4 : CommRing S'] →          
           [inst_5 : Algebra R' S'] →                       {P' : Algebra.Extens
ion R' S'} →                         [inst_6 : Algebra R R'] →                  
         [inst_7 : Algebra S S'] →                             [inst_8 : Algebra
 R S'] →                               [inst_9 : IsScalarTower R R' S'] → P.Hom 
P' → P.Hom P' → P.Ring →ₗ[R] ↥P'.ker
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are two maps `P → P'` between presentations,
then the image of `f - g` is in the kernel of `P' → S`.
-/
def Hom.subToKer (f g : Hom P P') : P.Ring →ₗ[R] P'.ker := by
  refine ((f.toAlgHom.toLinearMap - g.toAlgHom.toLinearMap).codRestrict
    (P'.ker.restrictScalars R) ?_)
  intro x
  simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply, ker,
    Submodule.restrictScalars_mem, RingHom.mem_ker, map_sub, algebraMap_toRingHom,
    sub_self, toAlgHom_apply]

variable [IsScalarTower R S S'] in
/--
If `f` and `g` are two maps `P → P'` between presentations,
their difference induces a map `P.CotangentSpace →ₗ[S] P'.Cotangent` that makes two maps
between the cotangent complexes homotopic.
-/
/-
**Algebra.Extension.Hom.sub** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.Hom`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {P : Algebra.Extension 
R S} →             {R' : Type u'} →               {S' : Type v'} →              
   [inst_3 : CommRing R'] →                   [inst_4 : CommRing S'] →          
           [inst_5 : Algebra R' S'] →                       {P' : Algebra.Extens
ion R' S'} →                         [inst_6 : Algebra R R'] →                  
         [inst_7 : Algebra S S'] →                             [inst_8 : Algebra
 R S'] →                               [IsScalarTower R R' S'] →                
                 [IsScalarTower R S S'] → P.Hom P' → P.Hom P' → P.CotangentSpace
 →ₗ[S] P'.Cotangent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `g` are two maps `P → P'` between presentations,
their difference induces a map `P.CotangentSpace →ₗ[S] P'.Cotangent` that makes 
two maps
between the cotangent complexes homotopic.
-/
def Hom.sub (f g : Hom P P') : P.CotangentSpace →ₗ[S] P'.Cotangent := by
  letI := ((algebraMap S S').comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S S' := IsScalarTower.of_algebraMap_eq' rfl
  letI := f.toAlgHom.toAlgebra
  haveI : IsScalarTower P.Ring P'.Ring S' :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (f.algebraMap_toRingHom x).symm
  haveI : IsScalarTower R P.Ring S' :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      show algebraMap R S' x = algebraMap S S' (algebraMap P.Ring S (algebraMap R P.Ring x)) by
        rw [← IsScalarTower.algebraMap_apply R P.Ring S, ← IsScalarTower.algebraMap_apply]
  refine (Derivation.liftKaehlerDifferential ?_).liftBaseChange S
  refine
  { __ := Cotangent.mk.restrictScalars R ∘ₗ f.subToKer g
    map_one_eq_zero' := ?_
    leibniz' := ?_ }
  · ext
    simp [Ideal.toCotangent_eq_zero]
  · intro x y
    ext
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      Cotangent.val_mk, Cotangent.val_add, Cotangent.val_smul''', ← map_smul, ← map_add,
      Ideal.toCotangent_eq]
    exact Hom.sub_aux f g x y

variable [IsScalarTower R S S']
/-
**Algebra.Extension.Hom.sub_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensio
n.Hom`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u'} {S' : Type v'} [
inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : Al
gebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8 :
 Algebra R S']   [inst_9 : IsScalarTower R R' S'] [inst_10 : IsScalarTower R S S
'] (f g : P.Hom P') (x : P.Ring),   (f.sub g) (1 ⊗ₜ[P.Ring] (KaehlerDifferential
.D R P.Ring) x) = Algebra.Extension.Cotangent.mk ((f.subToKer g) x)
参数：f g : P.Hom P'；x : P.Ring；f.sub g；1 ⊗ₜ[P.Ring] (KaehlerDifferential.D R P.Rin
g) x；(f.subToKer g) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Derivation.liftKaehlerDifferential_comp_D`：Derivation.liftKaehlerDiffere
ntial_comp_D (D' : Derivation R S M) (x : S) : D'.liftKaehlerDifferential (Kaehl
erDifferential.D R S x) = D' x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.sub_one_tmul (f g : Hom P P') (x) :
    f.sub g (1 ⊗ₜ .D _ _ x) = Cotangent.mk (f.subToKer g x) := by
  simp only [sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.mk_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    one_smul]

@[simp]
/-
**Algebra.Extension.Hom.sub_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extension.Ho
m`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u'} {S' : Type v'} [
inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : Al
gebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8 :
 Algebra R S']   [inst_9 : IsScalarTower R R' S'] [inst_10 : IsScalarTower R S S
'] (f g : P.Hom P') (r : S) (x : P.Ring),   (f.sub g) (r ⊗ₜ[P.Ring] (KaehlerDiff
erential.D R P.Ring) x) = r • Algebra.Extension.Cotangent.mk ((f.subToKer g) x)
参数：f g : P.Hom P'；r : S；x : P.Ring；f.sub g；r ⊗ₜ[P.Ring] (KaehlerDifferential.D R
 P.Ring) x；(f.subToKer g) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Derivation.liftKaehlerDifferential_comp_D`：Derivation.liftKaehlerDiffere
ntial_comp_D (D' : Derivation R S M) (x : S) : D'.liftKaehlerDifferential (Kaehl
erDifferential.D R S x) = D' x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.sub_tmul (f g : Hom P P') (r x) :
    f.sub g (r ⊗ₜ .D _ _ x) = r • Cotangent.mk (f.subToKer g x) := by
  simp only [sub, LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.mk_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply]
/-
**Algebra.Extension.CotangentSpace.map_sub_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.Extension.CotangentSpace`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u'} {S' : Type v'} [
inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : Al
gebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8 :
 Algebra R S']   [inst_9 : IsScalarTower R R' S'] [inst_10 : IsScalarTower R S S
'] (f g : P.Hom P'),   Algebra.Extension.CotangentSpace.map f - Algebra.Extensio
n.CotangentSpace.map g = ↑S P'.cotangentComplex ∘ₗ f.sub g
参数：f g : P.Hom P'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `KaehlerDifferential.tensorProductTo_surjective`：KaehlerDifferential.tens
orProductTo_surjective : Function.Surjective (KaehlerDifferential.D R S).tensorP
roductTo
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用引理 `Algebra.Extension.CotangentSpace.map_tmul`：map_tmul (f : Hom P P') (x y)
 : CotangentSpace.map f (x otimesₜ .D _ _ y) = (algebraMap _ _ x) otimesₜ .D _ _
 (f.toAlgHom y)
· 使用定理 `Algebra.Extension.Hom.sub_tmul`：∀ {R : Type u} {S : Type v} [inst : Comm
Ring R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S}
   {R' : Type u'} {S…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `Algebra.Extension.Hom.subToKer_apply_coe`：∀ {R : Type u} {S : Type v} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Exte
nsion R S}   {R' : Type u'} {S…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `TensorProduct.tmul_sub`：tmul_sub (m : M) (p₁ p₂ : P) : m otimesₜ (p₁ - p
₂) = m otimesₜ[R] p₁ - m otimesₜ[R] p₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
（共 32 条，此处仅展示前 30 条）
-/
lemma CotangentSpace.map_sub_map (f g : Hom P P') :
    CotangentSpace.map f - CotangentSpace.map g =
      P'.cotangentComplex.restrictScalars S ∘ₗ (f.sub g) := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
  | add =>
    simp only [map_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, *]
  | tmul x y =>
    obtain ⟨y, rfl⟩ := KaehlerDifferential.tensorProductTo_surjective _ _ y
    induction y with
    | zero => simp only [map_zero, tmul_zero]
    | add => simp only [map_add, tmul_add, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Function.comp_apply, *]
    | tmul =>
      simp only [Derivation.tensorProductTo_tmul, tmul_smul, smul_tmul', LinearMap.sub_apply,
        map_tmul, Hom.toAlgHom_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
        Function.comp_apply, Hom.sub_tmul, LinearMap.map_smul_of_tower, cotangentComplex_mk,
        Hom.subToKer_apply_coe, map_sub, ← algebraMap_eq_smul_one, tmul_sub, smul_sub]
/-
**Algebra.Extension.Cotangent.map_sub_map** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ext
ension.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u'} {S' : Type v'} [
inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : Al
gebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8 :
 Algebra R S']   [inst_9 : IsScalarTower R R' S'] [inst_10 : IsScalarTower R S S
'] (f g : P.Hom P'),   Algebra.Extension.Cotangent.map f - Algebra.Extension.Cot
angent.map g = f.sub g ∘ₗ P.cotangentComplex
参数：f g : P.Hom P'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.Extension.Hom.sub_tmul`：∀ {R : Type u} {S : Type v} [inst : Comm
Ring R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S}
   {R' : Type u'} {S…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Algebra.Extension.Hom.subToKer_apply_coe`：∀ {R : Type u} {S : Type v} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Exte
nsion R S}   {R' : Type u'} {S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Cotangent.map_sub_map (f g : Hom P P') :
    map f - map g = (f.sub g) ∘ₗ P.cotangentComplex := by
  ext x
  obtain ⟨x, rfl⟩ := mk_surjective x
  simp only [LinearMap.sub_apply, map_mk, LinearMap.coe_comp, Function.comp_apply,
    cotangentComplex_mk, Hom.sub_tmul, one_smul, val_mk]
  apply (Ideal.cotangentEquivIdeal _).injective
  ext
  simp only [val_sub, val_mk, map_sub, AddSubgroupClass.coe_sub, Ideal.cotangentEquivIdeal_apply,
    Ideal.toCotangent_to_quotient_square, Submodule.mkQ_apply, Ideal.Quotient.mk_eq_mk,
    Hom.subToKer_apply_coe, Hom.toAlgHom_apply]

variable (P) in
/-- The projection map from the relative cotangent space to the module of differentials. -/
/-
**Algebra.Extension.toKaehler** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra.Extension`。
形式化陈述：toKaehler : P.CotangentSpace ->ₗ[S] Ω[S⁄R]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map from the relative cotangent space to the module of differenti
als.
-/
abbrev toKaehler : P.CotangentSpace →ₗ[S] Ω[S⁄R] := mapBaseChange _ _ _
/-
**Algebra.Extension.toKaehler_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Exte
nsion`。
形式化陈述：toKaehler_surjective : Function.Surjective P.toKaehler
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `KaehlerDifferential.mapBaseChange_surjective`：KaehlerDifferential.mapBas
eChange_surjective (h : Function.Surjective (algebraMap A B)) : Function.Surject
ive (KaehlerDifferential.mapBaseCh…
· 使用引理 `Algebra.Extension.algebraMap_surjective`：algebraMap_surjective : Functio
n.Surjective (algebraMap P.Ring S)
-/
lemma toKaehler_surjective : Function.Surjective P.toKaehler :=
  mapBaseChange_surjective _ _ _ P.algebraMap_surjective
/-
**Algebra.Extension.exact_cotangentComplex_toKaehler** 是 Mathlib 中的一个引理，位于命名空间 `
Algebra.Extension`。
形式化陈述：exact_cotangentComplex_toKaehler : Function.Exact P.cotangentComplex P.toK
aehler
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`：KaehlerDif
ferential.exact_kerCotangentToTensor_mapBaseChange (h : Function.Surjective (alg
ebraMap A B)) : Function.Exact (kerCotangentToTens…
· 使用引理 `Algebra.Extension.algebraMap_surjective`：algebraMap_surjective : Functio
n.Surjective (algebraMap P.Ring S)
-/
lemma exact_cotangentComplex_toKaehler : Function.Exact P.cotangentComplex P.toKaehler :=
  exact_kerCotangentToTensor_mapBaseChange _ _ _ P.algebraMap_surjective

variable (P) in
/--
The first homology of the (naive) cotangent complex of `S` over `R`,
induced by a given presentation `0 → I → P → R → 0`,
defined as the kernel of `I/I² → S ⊗[P] Ω[P⁄R]`.
-/
/-
**Algebra.Extension.H1Cotangent** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`。
形式化陈述：{R : Type u} →   {S : Type v} → [inst : CommRing R] → [inst_1 : CommRing S
] → [inst_2 : Algebra R S] → Algebra.Extension R S → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first homology of the (naive) cotangent complex of `S` over `R`,
induced by a given presentation `0 → I → P → R → 0`,
defined as the kernel of `I/I² → S ⊗[P] Ω[P⁄R]`.
-/
protected def H1Cotangent : Type _ := LinearMap.ker P.cotangentComplex

-- The `SMul` instance exists to avoid a zsmul diamond.
variable {R₀} [CommRing R₀] [Algebra R₀ S] [Module R₀ P.Cotangent]
  [IsScalarTower R₀ S P.Cotangent] in
deriving instance SMul R₀, AddCommGroup, Module R₀ for (P).H1Cotangent
/-
**Algebra.Extension.H1Cotangent.val_add** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Exten
sion.H1Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (x y : P.H1Cotangent), ↑(x + y)
 = ↑x + ↑y
参数：x y : P.H1Cotangent；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma H1Cotangent.val_add (x y : P.H1Cotangent) : (x + y).1 = x.1 + y.1 := rfl
/-
**Algebra.Extension.H1Cotangent.val_zero** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Exte
nsion.H1Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   {P : Algebra.Extension R S}, ↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma H1Cotangent.val_zero : (0 : P.H1Cotangent).1 = 0 := rfl
/-
**Algebra.Extension.H1Cotangent.val_smul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Exte
nsion.H1Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R₀ : Type u_1} [inst_3 : CommR
ing R₀] [inst_4 : Algebra R₀ S] [inst_5 : _root_.Module R₀ P.Cotangent]   [inst_
6 : IsScalarTower R₀ S P.Cotangent] (r : R₀) (x : P.H1Cotangent), ↑(r • x) = r •
 ↑x
参数：r : R₀；x : P.H1Cotangent；r • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma H1Cotangent.val_smul {R₀} [CommRing R₀] [Algebra R₀ S] [Module R₀ P.Cotangent]
    [IsScalarTower R₀ S P.Cotangent] (r : R₀) (x : P.H1Cotangent) : (r • x).1 = r • x.1 := rfl
/-
**Algebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₁ R₂} [CommRing R₁] [CommRing R₂] [Algebra R₁ R₂]
    [Algebra R₁ S] [Algebra R₂ S]
    [Module R₁ P.Cotangent] [IsScalarTower R₁ S P.Cotangent]
    [Module R₂ P.Cotangent] [IsScalarTower R₂ S P.Cotangent]
    [IsScalarTower R₁ R₂ P.Cotangent] :
    IsScalarTower R₁ R₂ P.H1Cotangent :=
  inferInstanceAs <| IsScalarTower R₁ R₂ (LinearMap.ker _)
/-
**Algebra.Extension.subsingleton_h1Cotangent** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.
Extension`。
形式化陈述：subsingleton_h1Cotangent (P : Extension R S) : Subsingleton P.H1Cotangent 
↔ Function.Injective P.cotangentComplex
参数：P : Extension R S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x
· 使用定理 `Subtype.forall'`：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Pr
op}, (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma subsingleton_h1Cotangent (P : Extension R S) :
    Subsingleton P.H1Cotangent ↔ Function.Injective P.cotangentComplex := by
  delta Extension.H1Cotangent
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff, subsingleton_iff_forall_eq 0, Subtype.forall']
  simp only [Subtype.ext_iff, Submodule.coe_zero]

/-- The inclusion of `H¹(L_{S/R})` into the conormal space of a presentation. -/
/-
**Algebra.Extension.h1Cotangent** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of `H¹(L_{S/R})` into the conormal space of a presentation.
-/
@[simps!] noncomputable def h1Cotangentι : P.H1Cotangent →ₗ[S] P.Cotangent := Submodule.subtype _
/-
**Algebra.Extension.h1Cotangent** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of `H¹(L_{S/R})` into the conormal space of a presentation.
-/
lemma h1Cotangentι_injective : Function.Injective P.h1Cotangentι := Subtype.val_injective
/-
**Algebra.Extension.h1Cotangent** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[ext] lemma h1Cotangentι_ext (x y : P.H1Cotangent) (e : x.1 = y.1) : x = y := Subtype.ext e

/-- The sequence `H¹(L_{S/R}) → P.Cotangent → P.CotangentSpace` is exact. -/
/-
**Algebra.Extension.exact_hCotangent** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Extensio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sequence `H¹(L_{S/R}) → P.Cotangent → P.CotangentSpace` is exact.
-/
lemma exact_hCotangentι_cotangentComplex : Function.Exact h1Cotangentι P.cotangentComplex := by
  rw [LinearMap.exact_iff]
  exact (Submodule.range_subtype _).symm

/--
The induced map on the first homology of the (naive) cotangent complex.
-/
@[simps!]
/-
**Algebra.Extension.H1Cotangent.map** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension
.H1Cotangent`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {P : Algebra.Extension 
R S} →             {R' : Type u'} →               {S' : Type v'} →              
   [inst_3 : CommRing R'] →                   [inst_4 : CommRing S'] →          
           [inst_5 : Algebra R' S'] →                       {P' : Algebra.Extens
ion R' S'} →                         [inst_6 : Algebra R R'] →                  
         [inst_7 : Algebra S S'] →                             [inst_8 : Algebra
 R S'] →                               [IsScalarTower R R' S'] → P.Hom P' → P.H1
Cotangent →ₗ[S] P'.H1Cotangent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map on the first homology of the (naive) cotangent complex.
-/
def H1Cotangent.map (f : Hom P P') : P.H1Cotangent →ₗ[S] P'.H1Cotangent := by
  refine (Cotangent.map f).restrict (p := LinearMap.ker P.cotangentComplex)
    (q := (LinearMap.ker P'.cotangentComplex).restrictScalars S) fun x hx ↦ ?_
  simp only [LinearMap.mem_ker, Submodule.restrictScalars_mem] at hx ⊢
  apply_fun (CotangentSpace.map f) at hx
  rw [CotangentSpace.map_cotangentComplex] at hx
  rw [hx]
  exact LinearMap.map_zero _

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.Extension.H1Cotangent.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extens
ion.H1Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u'} {S' : Type v'} [
inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : Al
gebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8 :
 Algebra R S']   [inst_9 : IsScalarTower R R' S'] [IsScalarTower R S S'] (f g : 
P.Hom P'),   Algebra.Extension.H1Cotangent.map f = Algebra.Extension.H1Cotangent
.map g
参数：f g : P.Hom P'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.h1Cotangentι_ext`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension 
R S}   (x y : P.H1Cotang…
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.H1Cotangent.map_apply_coe`：∀ {R : Type u} {S : Type v}
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.E
xtension R S}   {R' : Type u'} {S…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Algebra.Extension.Cotangent.val_sub`：∀ {R : Type u} {S : Type v} [inst :
 CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension
 R S}   (x y : P.Cotangen…
· 使用定理 `LinearMap.sub_apply`：sub_apply (f g : M ->ₛₗ[σ₁₂] N₂) (x : M) : (f - g) 
x = f x - g x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.Extension.Cotangent.map_sub_map`：∀ {R : Type u} {S : Type v} [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Exten
sion R S}   {R' : Type u'} {S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.map_coe_ker`：map_coe_ker (f : M ->ₛₗ[τ₁₂] M₂) (x : ker f) : f 
x = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma H1Cotangent.map_eq (f g : Hom P P') : map f = map g := by
  ext x
  simp only [map_apply_coe]
  rw [← sub_eq_zero, ← Cotangent.val_sub, ← LinearMap.sub_apply, Cotangent.map_sub_map]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.map_coe_ker, map_zero,
    Cotangent.val_zero]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.Extension.H1Cotangent.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extens
ion.H1Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   {P : Algebra.Extension R S}, Algebra.Extension.H1Cotangent.
map (Algebra.Extension.Hom.id P) = LinearMap.id
参数：Algebra.Extension.Hom.id P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.h1Cotangentι_ext`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension 
R S}   (x y : P.H1Cotang…
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.H1Cotangent.map_apply_coe`：∀ {R : Type u} {S : Type v}
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.E
xtension R S}   {R' : Type u'} {S…
· 使用定理 `Algebra.Extension.Cotangent.map_id`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.Extensio
n R S}, Algebra.Extensio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma H1Cotangent.map_id : map (.id P) = LinearMap.id := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
omit [IsScalarTower R S S'] in
/-
**Algebra.Extension.H1Cotangent.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Exte
nsion.H1Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u'} {S' : Type v'} [
inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : Al
gebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8 :
 Algebra R S']   [inst_9 : IsScalarTower R R' S'] {R'' : Type u''} {S'' : Type v
''} [inst_10 : CommRing R''] [inst_11 : CommRing S'']   [inst_12 : Algebra R'' S
''] {P'' : Algebra.Extension R'' S''} [inst_13 : Algebra R R''] [inst_14 : Algeb
ra S S'']   [inst_15 : Algebra R S''] [inst_16 : IsScalarTower R R'' S''] [inst_
17 : Algebra R' R''] [inst_18 : Algebra S' S'']   [inst_19 : Algebra R' S''] [in
st_20 : IsScalarTower R' R'' S''] [inst_21 : IsScalarTower R R' R'']   [inst_22 
: IsScalarTower S S' S''] (f : P.Hom P') (g : P'.Hom P''),   Algebra.Extension.H
1Cotangent.map (g.comp f) =     ↑S (Algebra.Extension.H1Cotangent.map g) ∘ₗ Alge
bra.Extension.H1Cotangent.map f
参数：f : P.Hom P'；g : P'.Hom P''；g.comp f；Algebra.Extension.H1Cotangent.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.Extension.instIsScalarTowerH1CotangentOfCotangent`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{P : Algebra.Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Algebra.Extension.h1Cotangentι_ext`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension 
R S}   (x y : P.H1Cotang…
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.H1Cotangent.map_apply_coe`：∀ {R : Type u} {S : Type v}
 [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.E
xtension R S}   {R' : Type u'} {S…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.Extension.Cotangent.map_comp`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   {R' : Type u_1} {…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma H1Cotangent.map_comp
    (f : Hom P P') (g : Hom P' P'') :
    map (g.comp f) = (map g).restrictScalars S ∘ₗ map f := by
  ext; simp [Cotangent.map_comp]

omit [IsScalarTower R S S'] in
@[simp]
/-
**Algebra.Extension.H1Cotangent.map_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.Extension.H1Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u'} {S' : Type v'} [
inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : Al
gebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8 :
 Algebra R S']   [inst_9 : IsScalarTower R R' S'] {R'' : Type u''} {S'' : Type v
''} [inst_10 : CommRing R''] [inst_11 : CommRing S'']   [inst_12 : Algebra R'' S
''] {P'' : Algebra.Extension R'' S''} [inst_13 : Algebra R R''] [inst_14 : Algeb
ra S S'']   [inst_15 : Algebra R S''] [inst_16 : IsScalarTower R R'' S''] [inst_
17 : Algebra R' R''] [inst_18 : Algebra S' S'']   [inst_19 : Algebra R' S''] [in
st_20 : IsScalarTower R' R'' S''] [inst_21 : IsScalarTower R R' R'']   [inst_22 
: IsScalarTower S S' S''] (f : P.Hom P') (g : P'.Hom P'') (x : P.H1Cotangent),  
 (Algebra.Extension.H1Cotangent.map (g.comp f)) x =     (Algebra.Extension.H1Cot
angent.map g) ((Algebra.Extension.H1Cotangent.map f) x)
参数：f : P.Hom P'；g : P'.Hom P''；x : P.H1Cotangent；Algebra.Extension.H1Cotangent.m
ap (g.comp f)；Algebra.Extension.H1Cotangent.map g；(Algebra.Extension.H1Cotangent
.map f) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.Extension.instIsScalarTowerH1CotangentOfCotangent`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{P : Algebra.Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Algebra.Extension.H1Cotangent.map_comp`：∀ {R : Type u} {S : Type v} [ins
t : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extens
ion R S}   {R' : Type u'} {S…
-/
lemma H1Cotangent.map_comp_apply (f : Hom P P') (g : Hom P' P'') (x : P.H1Cotangent) :
    map (g.comp f) x = map g (map f x) :=
  congr($(H1Cotangent.map_comp f g) x)

/-- Maps `P₁ → P₂` and `P₂ → P₁` between extensions
induce an isomorphism between `H¹(L_P₁)` and `H¹(L_P₂)`. -/
@[simps! apply]
/-
**Algebra.Extension.H1Cotangent.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extensi
on.H1Cotangent`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {P₁ : Algebra.Extension
 R S} →             {P₂ : Algebra.Extension R S} → P₁.Hom P₂ → P₂.Hom P₁ → P₁.H1
Cotangent ≃ₗ[S] P₂.H1Cotangent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps `P₁ → P₂` and `P₂ → P₁` between extensions
induce an isomorphism between `H¹(L_P₁)` and `H¹(L_P₂)`.
-/
def H1Cotangent.equiv {P₁ P₂ : Extension R S} (f₁ : P₁.Hom P₂) (f₂ : P₂.Hom P₁) :
    P₁.H1Cotangent ≃ₗ[S] P₂.H1Cotangent where
  __ := map f₁
  invFun := map f₂
  left_inv x :=
    show (map f₂ ∘ₗ map f₁) x = LinearMap.id (R := S) x by
    rw [← Extension.H1Cotangent.map_id, eq_comm, map_eq _ (f₂.comp f₁),
      Extension.H1Cotangent.map_comp]; rfl
  right_inv x :=
    show (map f₁ ∘ₗ map f₂) x = LinearMap.id (R := S) x by
    rw [← Extension.H1Cotangent.map_id, eq_comm, map_eq _ (f₁.comp f₂),
      Extension.H1Cotangent.map_comp]; rfl

omit [IsScalarTower R S S'] in
/-
**Algebra.Extension.Cotangent.map_comp_h1Cotangent** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cotangent.map_comp_h1Cotangentι (f : P.Hom P') :
    Cotangent.map f ∘ₗ P.h1Cotangentι =
      P'.h1Cotangentι.restrictScalars S ∘ₗ H1Cotangent.map f := rfl

end Extension

namespace Generators

variable {ι : Type w} (P : Generators R S ι)

/-- The canonical basis on the `CotangentSpace`. -/
/-
**Algebra.Generators.cotangentSpaceBasis** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Gene
rators`。
形式化陈述：cotangentSpaceBasis : Basis ι S P.toExtension.CotangentSpace
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical basis on the `CotangentSpace`.
-/
def cotangentSpaceBasis : Basis ι S P.toExtension.CotangentSpace :=
  (mvPolynomialBasis _ _).baseChange (R := P.Ring) _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Algebra.Generators.cotangentSpaceBasis_repr_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.Generators`。
形式化陈述：cotangentSpaceBasis_repr_tmul (r x i) : P.cotangentSpaceBasis.repr (r otim
esₜ[P.Ring] KaehlerDifferential.D R P.Ring x : _) i = r * aeval P.val (pderiv i 
x)
参数：r x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Basis.baseChange_repr_tmul`：baseChange_repr_tmul (b : Basis ι R M
) (x y i) : (b.baseChange S).repr (x otimesₜ y) i = b.repr y i • x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `KaehlerDifferential.mvPolynomialBasis_repr_apply`：KaehlerDifferential.mv
PolynomialBasis_repr_apply (σ) (x) (i) : (mvPolynomialBasis R σ).repr (D _ _ x) 
i = MvPolynomial.pderiv i x
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cotangentSpaceBasis_repr_tmul (r x i) :
    P.cotangentSpaceBasis.repr (r ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring x : _) i =
      r * aeval P.val (pderiv i x) := by
  simp only [cotangentSpaceBasis, Basis.baseChange_repr_tmul, mvPolynomialBasis_repr_apply,
    Algebra.smul_def, mul_comm r, algebraMap_apply, toExtension]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.cotangentSpaceBasis_repr_one_tmul** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.Generators`。
形式化陈述：cotangentSpaceBasis_repr_one_tmul (x i) : P.cotangentSpaceBasis.repr (1 ot
imesₜ .D _ _ x) i = aeval P.val (pderiv i x)
参数：x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.Generators.cotangentSpaceBasis_repr_tmul`：cotangentSpaceBasis_re
pr_tmul (r x i) : P.cotangentSpaceBasis.repr (r otimesₜ[P.Ring] KaehlerDifferent
ial.D R P.Ring x : _) i = r * aeval P.…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cotangentSpaceBasis_repr_one_tmul (x i) :
    P.cotangentSpaceBasis.repr (1 ⊗ₜ .D _ _ x) i = aeval P.val (pderiv i x) := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.cotangentSpaceBasis_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
a.Generators`。
形式化陈述：cotangentSpaceBasis_apply (i) : P.cotangentSpaceBasis i = ((1 : S) otimesₜ
[P.Ring] D R P.Ring (.X i) :)
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Basis.baseChange_apply`：baseChange_apply (b : Basis ι R M) (i) : 
b.baseChange S i = 1 otimesₜ b i
· 使用引理 `KaehlerDifferential.mvPolynomialBasis_apply`：KaehlerDifferential.mvPolyn
omialBasis_apply (σ) (i) : mvPolynomialBasis R σ i = D R (MvPolynomial σ R) (.X 
i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cotangentSpaceBasis_apply (i) :
    P.cotangentSpaceBasis i = ((1 : S) ⊗ₜ[P.Ring] D R P.Ring (.X i) :) := by
  simp [cotangentSpaceBasis, toExtension]
/-
**Algebra.Generators.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Generators`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : Generators R S ι) : Module.Free S P.toExtension.CotangentSpace :=
  .of_basis P.cotangentSpaceBasis

/-- Given generators `R[xᵢ] → S` and an injective map `σ → ι`, this is the
composition `I/I² → ⊕ S dxᵢ → ⊕ S dxᵢ` where the second `i` only runs over `σ`. -/
/-
**Algebra.Generators.cotangentRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Genera
tors`。
形式化陈述：cotangentRestrict {σ : Type*} {u : σ -> ι} (hu : Function.Injective u) : P
.toExtension.Cotangent ->ₗ[S] (σ ->₀ S)
参数：hu : Function.Injective u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given generators `R[xᵢ] → S` and an injective map `σ → ι`, this is the
composition `I/I² → ⊕ S dxᵢ → ⊕ S dxᵢ` where the second `i` only runs over `σ`.
-/
def cotangentRestrict {σ : Type*} {u : σ → ι} (hu : Function.Injective u) :
    P.toExtension.Cotangent →ₗ[S] (σ →₀ S) :=
  Finsupp.lcomapDomain u hu ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ
    P.toExtension.cotangentComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.cotangentRestrict_mk** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Gen
erators`。
形式化陈述：cotangentRestrict_mk {σ : Type*} {u : σ -> ι} (hu : Function.Injective u) 
(x : P.ker) : cotangentRestrict P hu (Extension.Cotangent.mk x) = fun j => (aeva
l P.val) pderiv (u j) x.val
参数：hu : Function.Injective u；x : P.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.Generators.cotangentSpaceBasis_repr_tmul`：cotangentSpaceBasis_re
pr_tmul (r x i) : P.cotangentSpaceBasis.repr (r otimesₜ[P.Ring] KaehlerDifferent
ial.D R P.Ring x : _) i = r * aeval P.…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cotangentRestrict_mk {σ : Type*} {u : σ → ι} (hu : Function.Injective u) (x : P.ker) :
    cotangentRestrict P hu (Extension.Cotangent.mk x) =
      fun j ↦ (aeval P.val) <| pderiv (u j) x.val := by
  ext j
  simp only [cotangentRestrict, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    Finsupp.lcomapDomain_apply, Finsupp.comapDomain_apply, Extension.cotangentComplex_mk]
  simp only [toExtension_Ring, P.cotangentSpaceBasis_repr_tmul, one_mul]

universe w' u' v'

variable {R' : Type u'} {S' : Type v'} {ι' : Type w'} [CommRing R'] [CommRing S'] [Algebra R' S']
variable (P' : Generators R' S' ι')
variable [Algebra R R'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']

attribute [local instance] SMulCommClass.of_commMonoid

variable {P P'}

universe w'' u'' v''

variable {R'' : Type u''} {S'' : Type v''} {ι'' : Type w''}
  [CommRing R''] [CommRing S''] [Algebra R'' S''] {P'' : Generators R'' S'' ι''}
variable [Algebra R R''] [Algebra S S''] [Algebra R S'']
  [IsScalarTower R R'' S''] [IsScalarTower R S S'']
variable [Algebra R' R''] [Algebra S' S''] [Algebra R' S'']
  [IsScalarTower R' R'' S''] [IsScalarTower R' S' S'']
variable [IsScalarTower S S' S'']

open Extension

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Algebra.Generators.repr_CotangentSpaceMap** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.G
enerators`。
形式化陈述：repr_CotangentSpaceMap (f : Hom P P') (i j) : P'.cotangentSpaceBasis.repr 
(CotangentSpace.map f.toExtensionHom (P.cotangentSpaceBasis i)) j = aeval P'.val
 (pderiv j (f.val i))
参数：f : Hom P P'；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.Generators.cotangentSpaceBasis_apply`：cotangentSpaceBasis_apply 
(i) : P.cotangentSpaceBasis i = ((1 : S) otimesₜ[P.Ring] D R P.Ring (.X i) :)
· 使用引理 `Algebra.Extension.CotangentSpace.map_tmul`：map_tmul (f : Hom P P') (x y)
 : CotangentSpace.map f (x otimesₜ .D _ _ y) = (algebraMap _ _ x) otimesₜ .D _ _
 (f.toAlgHom y)
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
· 使用引理 `Algebra.Generators.cotangentSpaceBasis_repr_one_tmul`：cotangentSpaceBasi
s_repr_one_tmul (x i) : P.cotangentSpaceBasis.repr (1 otimesₜ .D _ _ x) i = aeva
l P.val (pderiv i x)
· 使用定理 `Algebra.Generators.Hom.toAlgHom_X`：∀ {R : Type u} {S : Type v} {ι : Type
 w} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Alge
bra.Generators R S ι} {…
-/
lemma repr_CotangentSpaceMap (f : Hom P P') (i j) :
    P'.cotangentSpaceBasis.repr (CotangentSpace.map f.toExtensionHom (P.cotangentSpaceBasis i)) j =
      aeval P'.val (pderiv j (f.val i)) := by
  rw [cotangentSpaceBasis_apply]
  simp only [toExtension]
  rw [CotangentSpace.map_tmul, map_one]
  erw [cotangentSpaceBasis_repr_one_tmul, Hom.toAlgHom_X]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.toKaehler_tmul_D** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generat
ors`。
形式化陈述：toKaehler_tmul_D (i) : P.toExtension.toKaehler (1 otimesₜ D R P.Ring (X i)
) = D _ _ (P.val i)
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `KaehlerDifferential.mapBaseChange_tmul`：KaehlerDifferential.mapBaseChang
e_tmul (x : B) (y : Ω[A⁄R]) : KaehlerDifferential.mapBaseChange R A B (x otimesₜ
 y) = x • KaehlerDifferentia…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `KaehlerDifferential.map_D`：KaehlerDifferential.map_D (x : A) : KaehlerDi
fferential.map R S A B (KaehlerDifferential.D R A x) = KaehlerDifferential.D S B
 (algebraMap A …
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toKaehler_tmul_D (i) :
    P.toExtension.toKaehler (1 ⊗ₜ D R P.Ring (X i)) = D _ _ (P.val i) :=
  (KaehlerDifferential.mapBaseChange_tmul ..).trans (by simp)

@[simp]
/-
**Algebra.Generators.toKaehler_cotangentSpaceBasis** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebra.Generators`。
形式化陈述：toKaehler_cotangentSpaceBasis (i) : P.toExtension.toKaehler (P.cotangentSp
aceBasis i) = D R S (P.val i)
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.Generators.cotangentSpaceBasis_apply`：cotangentSpaceBasis_apply 
(i) : P.cotangentSpaceBasis i = ((1 : S) otimesₜ[P.Ring] D R P.Ring (.X i) :)
· 使用引理 `Algebra.Generators.toKaehler_tmul_D`：toKaehler_tmul_D (i) : P.toExtensio
n.toKaehler (1 otimesₜ D R P.Ring (X i)) = D _ _ (P.val i)
-/
lemma toKaehler_cotangentSpaceBasis (i) :
    P.toExtension.toKaehler (P.cotangentSpaceBasis i) = D R S (P.val i) := by
  rw [cotangentSpaceBasis_apply]
  exact toKaehler_tmul_D i

end Generators

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
-- TODO: generalize to essentially of finite presentation algebras
open KaehlerDifferential in
attribute [local instance] Module.finitePresentation_of_projective in
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra.FinitePresentation R S] : Module.FinitePresentation S Ω[S⁄R] := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have : Algebra.FiniteType R P.toExtension.Ring := by simp [P]; infer_instance
  refine Module.finitePresentation_of_surjective _ P.toExtension.toKaehler_surjective ?_
  rw [LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler, ← Submodule.map_top]
  exact (Extension.Cotangent.finite P.fg_ker).1.map P.toExtension.cotangentComplex

variable {ι : Type w} {ι' : Type*} {P : Generators R S ι}

open Extension.H1Cotangent in
/-- `H¹(L_{S/R})` is independent of the presentation chosen. -/
@[simps! apply]
/-
**Algebra.Generators.H1Cotangent.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Genera
tors.H1Cotangent`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {ι : Type w} →         
    {ι' : Type u_1} →               (P : Algebra.Generators R S ι) →            
     (P' : Algebra.Generators R S ι') → P.toExtension.H1Cotangent ≃ₗ[S] P'.toExt
ension.H1Cotangent
参数：P : Algebra.Generators R S ι；P' : Algebra.Generators R S ι'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`H¹(L_{S/R})` is independent of the presentation chosen.
-/
def Generators.H1Cotangent.equiv (P : Generators R S ι) (P' : Generators R S ι') :
    P.toExtension.H1Cotangent ≃ₗ[S] P'.toExtension.H1Cotangent :=
  Extension.H1Cotangent.equiv
    (Generators.defaultHom P P').toExtensionHom (Generators.defaultHom P' P).toExtensionHom

variable {S' : Type*} [CommRing S'] [Algebra R S']
variable {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Algebra S' T] [IsScalarTower R S' T]

variable (R S S' T)

/-- `H¹(L_{S/R})`, the first homology of the (naive) cotangent complex of `S` over `R`. -/
/-
**Algebra.H1Cotangent** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：H1Cotangent : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`H¹(L_{S/R})`, the first homology of the (naive) cotangent complex of `S` over `
R`.
-/
abbrev H1Cotangent : Type _ := (Generators.self R S).toExtension.H1Cotangent

/-- The induced map on the first homology of the (naive) cotangent complex of `S` over `R`. -/
/-
**Algebra.H1Cotangent.map** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.H1Cotangent`。
形式化陈述：(R : Type u) →   (S : Type v) →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           (S' : Type u_2) →      
       [inst_3 : CommRing S'] →               [inst_4 : Algebra R S'] →         
        (T : Type w) →                   [inst_5 : CommRing T] →                
     [inst_6 : Algebra R T] →                       [inst_7 : Algebra S T] →    
                     [IsScalarTower R S T] →                           [inst_9 :
 Algebra S' T] →                             [IsScalarTower R S' T] → Algebra.H1
Cotangent R S' →ₗ[S'] Algebra.H1Cotangent S T
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced map on the first homology of the (naive) cotangent complex of `S` ov
er `R`.
-/
def H1Cotangent.map : H1Cotangent R S' →ₗ[S'] H1Cotangent S T :=
  Extension.H1Cotangent.map (Generators.defaultHom _ _).toExtensionHom

/-- Isomorphic algebras induce isomorphic `H¹(L_{S/R})`. -/
/-
**Algebra.H1Cotangent.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.H1Cotangent`。
形式化陈述：(R : Type u) →   (S : Type v) →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           (S' : Type u_2) →      
       [inst_3 : CommRing S'] →               [inst_4 : Algebra R S'] → (S ≃ₐ[R]
 S') → Algebra.H1Cotangent R S ≃ₗ[R] Algebra.H1Cotangent R S'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic algebras induce isomorphic `H¹(L_{S/R})`.
-/
def H1Cotangent.mapEquiv (e : S ≃ₐ[R] S') :
    H1Cotangent R S ≃ₗ[R] H1Cotangent R S' :=
  -- we are constructing data, so we do not use `algebraize`
  letI := e.toRingHom.toAlgebra
  letI := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R S S' := .of_algebraMap_eq' e.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower R S' S := .of_algebraMap_eq' e.symm.toAlgHom.comp_algebraMap.symm
  have : IsScalarTower S S' S := .of_algebraMap_eq fun _ ↦ (e.symm_apply_apply _).symm
  have : IsScalarTower S' S S' := .of_algebraMap_eq fun _ ↦ (e.apply_symm_apply _).symm
  { toFun := map R R S S'
    invFun := map R R S' S
    left_inv x := by
      change ((map R R S' S).restrictScalars S ∘ₗ map R R S S') x = x
      rw [map, map, ← Extension.H1Cotangent.map_comp, Extension.H1Cotangent.map_eq,
        Extension.H1Cotangent.map_id, LinearMap.id_apply]
    right_inv x := by
      change ((map R R S S').restrictScalars S' ∘ₗ map R R S' S) x = x
      rw [map, map, ← Extension.H1Cotangent.map_comp, Extension.H1Cotangent.map_eq,
        Extension.H1Cotangent.map_id, LinearMap.id_apply]
    map_add' := map_add (map R R S S')
    map_smul' := LinearMap.CompatibleSMul.map_smul (map R R S S') }

variable {R S S' T}

/-- `H¹(L_{S/R})` is independent of the presentation chosen. -/
/-
**Algebra.Generators.equivH1Cotangent** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Generat
ors`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {ι : Type w} → (P : Alg
ebra.Generators R S ι) → P.toExtension.H1Cotangent ≃ₗ[S] Algebra.H1Cotangent R S
参数：P : Algebra.Generators R S ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`H¹(L_{S/R})` is independent of the presentation chosen.
-/
abbrev Generators.equivH1Cotangent (P : Generators R S ι) :
    P.toExtension.H1Cotangent ≃ₗ[S] H1Cotangent R S :=
  Generators.H1Cotangent.equiv _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
attribute [local instance] Module.finitePresentation_of_projective in
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FinitePresentation R S] [Module.Projective S Ω[S⁄R]] :
    Module.Finite S (H1Cotangent R S) := by
  let P := Algebra.Presentation.ofFinitePresentation R S
  have : Algebra.FiniteType R P.toExtension.Ring := by simp [P]; infer_instance
  suffices Module.Finite S P.toExtension.H1Cotangent from
    .of_surjective P.equivH1Cotangent.toLinearMap P.equivH1Cotangent.surjective
  rw [Module.finite_def, Submodule.fg_top, ← LinearMap.ker_rangeRestrict]
  have := Extension.Cotangent.finite P.fg_ker
  have : Module.FinitePresentation S (LinearMap.range P.toExtension.cotangentComplex) := by
    rw [← LinearMap.exact_iff.mp P.toExtension.exact_cotangentComplex_toKaehler]
    exact Module.finitePresentation_of_projective_of_exact
      _ _ (Subtype.val_injective) P.toExtension.toKaehler_surjective
      (LinearMap.exact_subtype_ker_map _)
  exact Module.FinitePresentation.fg_ker (N := LinearMap.range P.toExtension.cotangentComplex)
    _ P.toExtension.cotangentComplex.surjective_rangeRestrict

end Algebra

