/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Formally smooth local algebras
-/

public section

open TensorProduct IsLocalRing KaehlerDifferential

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]

namespace Algebra

/--
The **Jacobian criterion** for smoothness of local algebras.
Suppose `S` is a local `R`-algebra, and `0 → I → P → S → 0` is a presentation such that
`P` is formally-smooth over `R`, `Ω[P⁄R]` is finite free over `P`,
(typically satisfied when `P` is the localization of a polynomial ring of finite type)
and `I` is finitely generated.
Then `S` is formally smooth iff `k ⊗ₛ I/I² → k ⊗ₚ Ω[P/R]` is injective,
where `k` is the residue field of `S`.
-/
/-
**Algebra.FormallySmooth.iff_injective_lTensor_residueField.** 是 Mathlib 中的一个定理，
位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Jacobian criterion** for smoothness of local algebras.
Suppose `S` is a local `R`-algebra, and `0 → I → P → S → 0` is a presentation su
ch that
`P` is formally-smooth over `R`, `Ω[P⁄R]` is finite free over `P`,
(typically satisfied when `P` is the localization of a polynomial ring of finite
 type)
and `I` is finitely generated.
Then `S` is formally smooth iff `k ⊗ₛ I/I² → k ⊗ₚ Ω[P/R]` is injective,
where `k` is the residue field of `S`.
-/
theorem FormallySmooth.iff_injective_lTensor_residueField.{u}
    (P : Algebra.Extension.{u} R S)
    [FormallySmooth R P.Ring]
    [Module.Free P.Ring Ω[P.Ring⁄R]] [Module.Finite P.Ring Ω[P.Ring⁄R]]
    (h' : P.ker.FG) :
    Algebra.FormallySmooth R S ↔
      Function.Injective (P.cotangentComplex.lTensor (ResidueField S)) := by
  have : Module.Finite P.Ring P.Cotangent :=
    have : Module.Finite P.Ring P.ker := .of_fg h'
    .of_surjective _ Extension.Cotangent.mk_surjective
  have : Module.Finite S P.Cotangent := Module.Finite.of_restrictScalars_finite P.Ring _ _
  rw [← IsLocalRing.split_injective_iff_lTensor_residueField_injective,
    P.formallySmooth_iff_split_injection]
/-
**Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField**
 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallySmooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : IsLocalRing S]   [inst_3 : Algebra R S] (P : Type u_3) [inst_4 : CommR
ing P] [inst_5 : Algebra R P] [inst_6 : Algebra P S]   [IsScalarTower R P S] [Al
gebra.FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]],   Fun
ction.Surjective ⇑(algebraMap P S) →     (RingHom.ker (algebraMap P S)).FG →    
   (Algebra.FormallySmooth R S ↔         Function.Injective ⇑(KaehlerDifferentia
l.cotangentComplexBaseChange R S P (IsLocalRing.ResidueField S)))
参数：P : Type u_3；algebraMap P S；RingHom.ker (algebraMap P S)；Algebra.FormallySmoo
th R S ↔         Function.Injective ⇑(KaehlerDifferential.cotangentComplexBaseCh
ange R S P (IsLocalRing.ResidueField S))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallySmooth.iff_injective_lTensor_residueField`：∀ {R : Type u
_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : IsLocalRi
ng S]   [inst_3 : Algebra R S] (P : Algebra.Ext…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用引理 `Algebra.Extension.cotangentComplexBaseChange_eq_lTensor_cotangentComplex
`：cotangentComplexBaseChange_eq_lTensor_cotangentComplex : cotangentComplexBaseC
hange R S P.Ring A = AlgebraTensorModule.cancelBaseChange P.Ri…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
-/
theorem FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
    (P : Type*) [CommRing P] [Algebra R P] [Algebra P S]
    [IsScalarTower R P S] [FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG) :
    Algebra.FormallySmooth R S ↔
      Function.Injective (cotangentComplexBaseChange R S P (ResidueField S)) := by
  let P' : Extension R S := { Ring := P, σ := _, algebraMap_σ := Function.surjInv_eq h₁ }
  rw [Algebra.FormallySmooth.iff_injective_lTensor_residueField P' h₂]
  rw [P'.cotangentComplexBaseChange_eq_lTensor_cotangentComplex (ResidueField S)]
  refine .trans ?_ ((AlgebraTensorModule.cancelBaseChange P'.Ring S _ _
    Ω[P'.Ring⁄R]).comp_injective _).symm
  exact (((AlgebraTensorModule.cancelBaseChange P'.Ring S _ _ P'.ker).symm ≪≫ₗ
    P'.cotangentEquiv.baseChange (A := _)).injective_comp _).symm

/--
The **Jacobian criterion** for smoothness of local algebras.
Suppose `S` is a local `R`-algebra, and `0 → I → P → S → 0` is a presentation such that
`P` is formally-smooth over `R`, `Ω[P⁄R]` is finite free over `P`,
(typically satisfied when `P` is the localization of a polynomial ring of finite type)
and `I` is finitely generated.
Then `S` is formally smooth iff `k ⊗ₛ I → k ⊗ₚ Ω[P/R]` is injective,
where `k` any field extension of the residue field of `S`.
-/
/-
**Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange** 是 Mathlib 中的
一个定理，位于命名空间 `Algebra.FormallySmooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : IsLocalRing S]   [inst_3 : Algebra R S] (P : Type u_3) (K : Type u_4) 
[inst_4 : Field K] [inst_5 : CommRing P] [inst_6 : Algebra R P]   [inst_7 : Alge
bra P S] [IsScalarTower R P S] [inst_9 : Algebra S K] [inst_10 : Algebra P K]   
[inst_11 : IsScalarTower P S K] [Algebra.FormallySmooth R P] [Module.Free P Ω[P⁄
R]] [Module.Finite P Ω[P⁄R]],   Function.Surjective ⇑(algebraMap P S) →     (Rin
gHom.ker (algebraMap P S)).FG →       IsLocalRing.maximalIdeal S ≤ RingHom.ker (
algebraMap S K) →         (Algebra.FormallySmooth R S ↔ Function.Injective ⇑(Kae
hlerDifferential.cotangentComplexBaseChange R S P K))
参数：P : Type u_3；K : Type u_4；algebraMap P S；RingHom.ker (algebraMap P S)；algebra
Map S K；Algebra.FormallySmooth R S ↔ Function.Injective ⇑(KaehlerDifferential.co
tangentComplexBaseChange R S P K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `IsScalarTower.to₁₃₄`：∀ (M : Type u_9) (N : Type u_10) (P : Type u_11) (Q
 : Type u_12) [inst : SMul M N] [inst_1 : SMul M P]   [inst_2 : SMul M Q] [inst_
3 : SMul …
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueF
ield`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : IsLocalRing S]   [inst_3 : Algebra R S] (P : Type u_3) […
· 使用引理 `Module.FaithfullyFlat.lTensor_injective_iff_injective`：lTensor_injective
_iff_injective [Module.FaithfullyFlat R M] : Function.Injective (f.lTensor M) ↔ 
Function.Injective f
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `KaehlerDifferential.kerToTensor_apply`：∀ (R : Type u) [inst : CommRing R
] (A : Type u_2) (B : Type u_3) [inst_1 : CommRing A] [inst_2 : CommRing B]   [i
nst_3 : Algebra R A] [inst_…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The **Jacobian criterion** for smoothness of local algebras.
Suppose `S` is a local `R`-algebra, and `0 → I → P → S → 0` is a presentation su
ch that
`P` is formally-smooth over `R`, `Ω[P⁄R]` is finite free over `P`,
(typically satisfied when `P` is the localization of a polynomial ring of finite
 type)
and `I` is finitely generated.
Then `S` is formally smooth iff `k ⊗ₛ I → k ⊗ₚ Ω[P/R]` is injective,
where `k` any field extension of the residue field of `S`.
-/
theorem FormallySmooth.iff_injective_cotangentComplexBaseChange
    (P K : Type*) [Field K] [CommRing P] [Algebra R P] [Algebra P S]
    [IsScalarTower R P S] [Algebra S K] [Algebra P K] [IsScalarTower P S K]
    [FormallySmooth R P] [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    (h₁ : Function.Surjective (algebraMap P S)) (h₂ : (RingHom.ker (algebraMap P S)).FG)
    (h₃ : maximalIdeal S ≤ RingHom.ker (algebraMap S K)) :
    Algebra.FormallySmooth R S ↔ Function.Injective (cotangentComplexBaseChange R S P K) := by
  let f : ResidueField S →ₐ[S] K := Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) h₃
  let := f.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower P (ResidueField S) K := .to₁₃₄ _ S _ _
  rw [FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField P h₁ h₂,
    ← Module.FaithfullyFlat.lTensor_injective_iff_injective _ K]
  have : (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).toLinearMap ∘ₗ
      (cotangentComplexBaseChange R S P (ResidueField S)).baseChange K ∘ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm.toLinearMap =
      (cotangentComplexBaseChange R S P K) := by
    ext
    #adaptation_note /-- Prior to nightly-2026-04-06, this was just `simp`. -/
    simp_rw [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp, curry_apply,
      LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, Function.comp_apply,
      AlgebraTensorModule.cancelBaseChange_symm_tmul, LinearMap.baseChange_tmul,
      cotangentComplexBaseChange_tmul, kerToTensor_apply, one_smul,
      AlgebraTensorModule.cancelBaseChange_tmul]
    simp
  rw [← this]
  refine .trans ?_ ((AlgebraTensorModule.cancelBaseChange _ _ _ _ _).comp_injective _).symm
  exact ((AlgebraTensorModule.cancelBaseChange _ _ _ _ _).symm.injective_comp _).symm

end Algebra

