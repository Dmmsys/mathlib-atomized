/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Smooth base change commutes with integral closure

In this file we aim to prove that smooth base change commutes with integral closure.
We define the map
`TensorProduct.toIntegralClosure : S ⊗[R] integralClosure R B →ₐ[S] integralClosure S (S ⊗[R] B)`
and show that it is bijective when `S` is `R`-smooth.

## Main results
- `TensorProduct.toIntegralClosure_injective_of_flat`:
  If `S` is `R`-flat, then `TensorProduct.toIntegralClosure` is injective.
- `TensorProduct.toIntegralClosure_mvPolynomial_bijective`:
  If `S = MvPolynomial σ R`, then `TensorProduct.toIntegralClosure` is bijective.
- `TensorProduct.toIntegralClosure_bijective_of_isLocalization`:
  If `S = Localization M`, then `TensorProduct.toIntegralClosure` is bijective.
- `TensorProduct.toIntegralClosure_bijective_of_smooth`:
  If `S` is `R`-smooth, then `TensorProduct.toIntegralClosure` is bijective.
-/

@[expose] public section

open Polynomial TensorProduct

variable {R S B : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]

variable (R S) in
/-- The comparison map from `S ⊗[R] integralClosure R B` to `integralClosure S (S ⊗[R] B)`.
This is injective when `S` is `R`-flat, and (TODO) bijective when `S` is `R`-smooth. -/
/-
**TensorProduct.toIntegralClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TensorProduct.toIntegralClosure (B : Type*) [CommRing B] [Algebra R B] : S
 otimes[R] integralClosure R B ->ₐ[S] integralClosure S (S otimes[R] B)
参数：B : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison map from `S ⊗[R] integralClosure R B` to `integralClosure S (S ⊗[
R] B)`.
This is injective when `S` is `R`-flat, and (TODO) bijective when `S` is `R`-smo
oth.
-/
def TensorProduct.toIntegralClosure
    (B : Type*) [CommRing B] [Algebra R B] :
    S ⊗[R] integralClosure R B →ₐ[S] integralClosure S (S ⊗[R] B) :=
    (Algebra.TensorProduct.map (.id _ _) (integralClosure R B).val).codRestrict _ fun x ↦ by
  induction x with
  | zero => simp
  | add x y _ _ => rw [map_add]; exact add_mem ‹_› ‹_›
  | tmul x y =>
    convert!
      ((y.2.map (Algebra.TensorProduct.includeRight (R := R) (A := S))).tower_top (A := S)).smul x
    simp [smul_tmul']
/-
**TensorProduct.toIntegralClosure_injective_of_flat** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：TensorProduct.toIntegralClosure_injective_of_flat [Module.Flat R S] : Func
tion.Injective (toIntegralClosure R S B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_comp`：coe_comp (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) : ⇑(φ₁.com
p φ₂) = φ₁ ∘ φ₂
· 使用定理 `TensorProduct.toIntegralClosure.eq_1`：∀ (R : Type u_1) (S : Type u_2) [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (B : Type u_4)   
[inst_3 : CommRing B] [ins…
· 使用定理 `AlgHom.val_comp_codRestrict`：val_comp_codRestrict (f : A ->ₐ[R] B) (S : 
Subalgebra R B) (hf : forall x, f x in S) : S.val.comp (f.codRestrict S hf) = f
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma TensorProduct.toIntegralClosure_injective_of_flat [Module.Flat R S] :
    Function.Injective (toIntegralClosure R S B) := by
  refine Function.Injective.of_comp (f := (integralClosure _ _).val) ?_
  rw [← AlgHom.coe_comp, toIntegralClosure, AlgHom.val_comp_codRestrict]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (integralClosure R B).val.toLinearMap Subtype.val_injective

/-- "Base change preserves integral closure" is stable under composition. -/
/-
**TensorProduct.toIntegralClosure_bijective_of_tower** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：TensorProduct.toIntegralClosure_bijective_of_tower {T : Type*} [CommRing T
] [Algebra R T] [Algebra S T] [IsScalarTower R S T] (H : Function.Bijective (toI
ntegralClosure R S B)) (H' : Function.Bijective (toIntegralClosure S T (S otimes
[R] B))) : Function.Bijective (toIntegralClosure R T B)
参数：H : Function.Bijective (toIntegralClosure R S B)；H' : Function.Bijective (toI
ntegralClosure S T (S otimes[R] B))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.coe_toAlgHom`：coe_toAlgHom : DFunLike.coe e.toAlgHom = e
· 使用定理 `Algebra.TensorProduct.ext_ring`：∀ {R : Type u_4} {S : Type u_5} {A : Typ
e u_6} {B : Type u_7} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_
2 : Semiring A] [ins…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Algebra.TensorProduct.cancelBaseChange_symm_tmul`：cancelBaseChange_symm_
tmul (a : A) (b : B) : (Algebra.TensorProduct.cancelBaseChange R S T A B).symm (
a otimesₜ b) = a otimesₜ (1 otimesₜ b)
· 使用引理 `Algebra.TensorProduct.cancelBaseChange_tmul`：cancelBaseChange_tmul (a : 
A) (s : S) (b : B) : Algebra.TensorProduct.cancelBaseChange R S T A B (a otimesₜ
 (s otimesₜ b)) = (s • a) otimesₜ…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …

--- 原说明 ---
"Base change preserves integral closure" is stable under composition.
-/
lemma TensorProduct.toIntegralClosure_bijective_of_tower
    {T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (H : Function.Bijective (toIntegralClosure R S B))
    (H' : Function.Bijective (toIntegralClosure S T (S ⊗[R] B))) :
    Function.Bijective (toIntegralClosure R T B) := by
  let e := (Algebra.TensorProduct.cancelBaseChange ..).symm.trans <|
      (Algebra.TensorProduct.congr (.refl (R := T) (A₁ := T)) (.ofBijective _ H)).trans <|
      (AlgEquiv.ofBijective _ H').trans <|
      (AlgEquiv.mapIntegralClosure (Algebra.TensorProduct.cancelBaseChange ..))
  convert! e.bijective
  rw [← e.coe_toAlgHom]
  congr 1
  ext; simp [e, toIntegralClosure]

/-- "Base change preserves integral closure" can be checked Zariski-locally. -/
/-
**TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway** 是 Mathlib 中的
一个引理，位于命名空间 ``。
形式化陈述：TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway {s : Set S
} (hs : Ideal.span s = ⊤) (Sᵣ : s -> Type*) [forall r, CommRing (Sᵣ r)] [forall 
r, Algebra S (Sᵣ r)] [forall r, Algebra R (Sᵣ r)] [forall r, IsScalarTower R S (
Sᵣ r)] [forall r, IsLocalization.Away r.1 (Sᵣ r)] (H : forall r, Function.Biject
ive (toIntegralClosure R (Sᵣ r) B)) : Function.Bijective (toIntegralClosure R S 
B)
参数：hs : Ideal.span s = ⊤；Sᵣ : s -> Type*；Sᵣ r；Sᵣ r；Sᵣ r；Sᵣ r；Sᵣ r；H : forall r, 
Function.Bijective (toIntegralClosure R (Sᵣ r) B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `isLocalizedModule_iff_isLocalization`：isLocalizedModule_iff_isLocalizati
on : IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔ IsLocaliz
ation (Algebra.algebraMapS…
· 使用引理 `IsLocalization.tensorProduct_tensorProduct`：IsLocalization.tensorProduct
_tensorProduct (M : Submonoid A) (B : Type*) [CommSemiring B] [Algebra R B] [Alg
ebra A B] [IsScalarTower R A B] …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsLocalization.integralClosure`：∀ {R : Type u_1} [inst : CommRing R] {S 
: Type u_2} [inst_1 : CommRing S] [inst_2 : Algebra R S] {Rf : Type u_5}   {Sf :
 Type u_6} [inst_3 :…
· 使用定理 `bijective_of_isLocalized_span`：bijective_of_isLocalized_span (H : forall
 r : s, Function.Bijective (map (.powers r.1) (f r) (g r) F)) : Function.Bijecti
ve F
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.ext`：ext (map_unit : forall x : S, IsUnit ((algebraMap
 R (Module.End R M'')) x)) ⦃j k : M' ->ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j =
 k
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
"Base change preserves integral closure" can be checked Zariski-locally.
-/
lemma TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway
    {s : Set S} (hs : Ideal.span s = ⊤) (Sᵣ : s → Type*) [∀ r, CommRing (Sᵣ r)]
    [∀ r, Algebra S (Sᵣ r)] [∀ r, Algebra R (Sᵣ r)] [∀ r, IsScalarTower R S (Sᵣ r)]
    [∀ r, IsLocalization.Away r.1 (Sᵣ r)]
    (H : ∀ r, Function.Bijective (toIntegralClosure R (Sᵣ r) B)) :
    Function.Bijective (toIntegralClosure R S B) := by
  have (r : s) : IsLocalizedModule.Away r.1
      (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
        (AlgHom.id R (integralClosure R B))).toLinearMap := by
    let := (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
      (AlgHom.id R (integralClosure R B))).toAlgebra
    refine isLocalizedModule_iff_isLocalization.mpr ?_
    refine IsLocalization.tensorProduct_tensorProduct _ _ (.powers r.1) _ ?_
    ext; simp [RingHom.algebraMap_toAlgebra]
  let φ (r : s) : integralClosure S (S ⊗[R] B) →ₐ[S] integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B) :=
    ((Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)).comp
      (integralClosure S (S ⊗[R] B)).val).codRestrict
        ((integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B)).restrictScalars S) <| by
    simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply,
      Subalgebra.mem_restrictScalars, Subtype.forall, mem_integralClosure_iff]
    exact fun a ha ↦ (ha.map _).tower_top
  have (r : s) : IsLocalizedModule.Away r.1 (φ r).toLinearMap := by
    let := (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
          (AlgHom.id R B)).toAlgebra
    let := (φ r).toAlgebra
    have : IsScalarTower (integralClosure S (S ⊗[R] B)) (integralClosure (Sᵣ r) (Sᵣ r ⊗[R] B))
        (Sᵣ r ⊗[R] B) := .of_algebraMap_eq' rfl
    have : IsLocalization (Algebra.algebraMapSubmonoid (S ⊗[R] B) (Submonoid.powers r.1))
        (Sᵣ r ⊗[R] B) := by
      refine IsLocalization.tensorProduct_tensorProduct _ _ (.powers r.1) _ ?_
      ext; simp [RingHom.algebraMap_toAlgebra]
    refine isLocalizedModule_iff_isLocalization.mpr ?_
    exact IsLocalization.integralClosure ..
  refine bijective_of_isLocalized_span s hs (F := (toIntegralClosure R S B).toLinearMap)
    (fun r ↦ (Sᵣ r) ⊗[R] integralClosure R B)
    (fun r ↦ (Algebra.TensorProduct.map (Algebra.ofId _ _) (.id _ _)).toLinearMap)
    (fun r ↦ integralClosure (Sᵣ r) ((Sᵣ r) ⊗[R] B))
    (fun r ↦ (φ r).toLinearMap) fun r ↦ ?_
  convert!
    show Function.Bijective ((toIntegralClosure R (Sᵣ r) B).toLinearMap.restrictScalars S) from
      H r using 1
  congr!
  refine IsLocalizedModule.ext (.powers r.1) (Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
    (AlgHom.id R (integralClosure R B))).toLinearMap
    (IsLocalizedModule.map_units (S := .powers r.1) (φ r).toLinearMap) ?_
  ext x
  exact congr($(IsLocalizedModule.map_apply (.powers r.1)
      ((Algebra.TensorProduct.map (Algebra.ofId S (Sᵣ r))
        (AlgHom.id R (integralClosure R B))).toLinearMap)
      (φ r).toLinearMap (toIntegralClosure R S B).toLinearMap (1 ⊗ₜ x)).1)

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] MvPolynomial.algebraMvPolynomial in
/-- Base changing to `MvPolynomial σ R` preserves integral closure. -/
/-
**TensorProduct.toIntegralClosure_mvPolynomial_bijective** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：TensorProduct.toIntegralClosure_mvPolynomial_bijective {σ : Type*} : Funct
ion.Bijective (toIntegralClosure R (MvPolynomial σ R) B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `TensorProduct.toIntegralClosure_injective_of_flat`：TensorProduct.toInteg
ralClosure_injective_of_flat [Module.Flat R S] : Function.Injective (toIntegralC
losure R S B)
· 使用定理 `MvPolynomial.instFree`：∀ (σ : Type u) (R : Type v) [inst : CommSemiring 
R], Module.Free R (MvPolynomial σ R)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用引理 `MvPolynomial.algebraTensorAlgEquiv_tmul`：algebraTensorAlgEquiv_tmul (a :
 A) (p : MvPolynomial σ R) : algebraTensorAlgEquiv R A (a otimesₜ p) = a • MvPol
ynomial.map (algebraMap R A) …
· 使用定理 `MvPolynomial.map_C`：map_C : forall a : R, map f (C a : MvPolynomial σ R)
 = C (f a)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `MvPolynomial.map_comp_C`：map_comp_C (f : R ->+* S) : (map f).comp (C : R
 ->+* MvPolynomial σ R) = C.comp f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `MvPolynomial.coeff_X`：coeff_X [DecidableEq σ] (i : σ) (m) : coeff m (X i
 : MvPolynomial σ R) = if Finsupp.single i 1 = m then 1 else 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.isIntegral_iff_isIntegral_coeff`：MvPolynomial.isIntegral_if
f_isIntegral_coeff.{w} {σ : Type w} {f : MvPolynomial σ S} : IsIntegral (MvPolyn
omial σ R) f ↔ forall n, IsIntegra…
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
Base changing to `MvPolynomial σ R` preserves integral closure.
-/
lemma TensorProduct.toIntegralClosure_mvPolynomial_bijective {σ : Type*} :
    Function.Bijective (toIntegralClosure R (MvPolynomial σ R) B) := by
  classical
  refine ⟨toIntegralClosure_injective_of_flat, ?_⟩
  rintro ⟨x, hx⟩
  let e₀ : MvPolynomial σ R ⊗[R] B ≃ₐ[R] MvPolynomial σ B :=
    (Algebra.TensorProduct.comm R _ _).trans
      ((MvPolynomial.algebraTensorAlgEquiv R B).restrictScalars R)
  let e₁ := (Algebra.TensorProduct.comm R (MvPolynomial σ R) (integralClosure R B)).trans
    ((MvPolynomial.algebraTensorAlgEquiv R (integralClosure R B)).restrictScalars R)
  let e : MvPolynomial σ R ⊗[R] B ≃ₐ[MvPolynomial σ R] MvPolynomial σ B :=
    { toRingEquiv := e₀.toRingEquiv, commutes' r := by
        change e₀.toRingHom.comp (algebraMap _ _) r = _
        congr 1
        ext <;> simp [e₀, MvPolynomial.coeff_X] }
  have := MvPolynomial.isIntegral_iff_isIntegral_coeff.mp (hx.map e)
  obtain ⟨y, hy⟩ : e x ∈ RingHom.range (MvPolynomial.map (integralClosure R B).val.toRingHom) := by
    refine MvPolynomial.mem_range_map_iff_coeffs_subset.mpr ?_
    simp [Set.subset_def, mem_integralClosure_iff, MvPolynomial.mem_coeffs_iff,
      @forall_comm B, this]
  refine ⟨e₁.symm y, Subtype.ext <| e.injective (.trans ?_ hy)⟩
  obtain ⟨y, rfl⟩ := e₁.surjective y
  dsimp [TensorProduct.toIntegralClosure, e]
  simp only [AlgEquiv.symm_apply_apply]
  have : e₀.toAlgHom.comp
      (Algebra.TensorProduct.map (AlgHom.id R (MvPolynomial σ R)) (integralClosure R B).val) =
      (MvPolynomial.mapAlgHom (integralClosure R B).val).comp e₁.toAlgHom := by
    ext <;> simp [e₀, e₁, MvPolynomial.coeff_map, MvPolynomial.coeff_one,
      apply_ite ((↑) : (integralClosure R B) → B)]
  exact congr($this y)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Localization preserves integral closure. -/
/-
**TensorProduct.toIntegralClosure_bijective_of_isLocalization** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：TensorProduct.toIntegralClosure_bijective_of_isLocalization (M : Submonoid
 R) [IsLocalization M S] : Function.Bijective (toIntegralClosure R S B)
参数：M : Submonoid R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `RingHom.IsIntegralElem.of_comp`：RingHom.IsIntegralElem.of_comp {g : S ->
+* T} {x : T} (hx : (g.comp f).IsIntegralElem x) : g.IsIntegralElem x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.comp_algebraMap_of_tower`：∀ (R : Type u) {S : Type v} {A : Type w
} {B : Type u₁} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Se
miring A] [inst_3 : S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RingHom.IsIntegralElem.map`：RingHom.IsIntegralElem.map {x : S} (hx : f.I
sIntegralElem x) (g : S ->+* T) : (g.comp f).IsIntegralElem (g x)
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `IsLocalization.integralClosure`：∀ {R : Type u_1} [inst : CommRing R] {S 
: Type u_2} [inst_1 : CommRing S] [inst_2 : Algebra R S] {Rf : Type u_5}   {Sf :
 Type u_6} [inst_3 :…
· 使用定理 `Subalgebra.instIsScalarTowerSubtypeMem`：∀ {R' : Type u'} {R : Type u} {A
 : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] 
  (S : Subalgebra R A) [inst…
· 使用定理 `AlgHom.coe_restrictScalars'`：coe_restrictScalars' (f : A ->ₐ[S] B) : (re
strictScalars R f : A -> B) = f
· 使用定理 `AlgEquiv.coe_restrictScalars`：coe_restrictScalars (f : A ≃ₐ[S] B) : (res
trictScalars R f : A -> B) = f
· 使用定理 `AlgEquiv.coe_toAlgHom`：coe_toAlgHom : DFunLike.coe e.toAlgHom = e
· 使用定理 `Algebra.TensorProduct.ext`：ext ⦃f g : (A otimes[R] B) ->ₐ[S] C⦄ (ha : f.
comp includeLeft = g.comp includeLeft) (hb : (f.restrictScalars R).comp includeR
ight = (g.restr…
· 使用定理 `IsLocalization.algHom_ext`：IsLocalization.algHom_ext {R A L B : Type*} [
CommSemiring R] [CommSemiring A] [CommSemiring L] [Semiring B] (W : Submonoid A)
 [Algebra A L] …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.ext_id`：ext_id (f g : R ->ₐ[R] A) : f = g
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …

--- 原说明 ---
Localization preserves integral closure.
-/
lemma TensorProduct.toIntegralClosure_bijective_of_isLocalization
    (M : Submonoid R) [IsLocalization M S] :
    Function.Bijective (toIntegralClosure R S B) := by
  let φ : integralClosure R B →ₐ[R] integralClosure S (S ⊗[R] B) :=
    AlgHom.codRestrict (Algebra.TensorProduct.includeRight.comp (integralClosure R B).val)
      ((integralClosure S (S ⊗[R] B)).restrictScalars R) fun ⟨x, hx⟩ ↦ by
    refine .of_comp (f := algebraMap R S) ?_
    convert!
      RingHom.IsIntegralElem.map hx
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom
    simp [← IsScalarTower.algebraMap_eq]
  let := φ.toAlgebra
  have := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  have : IsScalarTower (integralClosure R B) (integralClosure S (S ⊗[R] B)) (S ⊗[R] B) :=
    .of_algebraMap_eq' rfl
  have := IsLocalization.integralClosure (S := B) M (Rf := S) (Sf := S ⊗[R] B)
  convert!
    (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (integralClosure R B) M)
        (S ⊗[R] integralClosure R B) (integralClosure S (S ⊗[R] B))).bijective
  rw [← AlgHom.coe_restrictScalars' R, ← AlgEquiv.coe_restrictScalars R, ← AlgEquiv.coe_toAlgHom]
  congr 1
  ext1
  · apply IsLocalization.algHom_ext M; ext
  · ext x
    dsimp [toIntegralClosure]
    simp [← Algebra.TensorProduct.right_algebraMap_apply]
    rfl

section IsStandardEtale

attribute [local instance] Polynomial.algebra in
/-- Let `S` be an `R`-algebra and `f : S[X]` be a monic polynomial with `R`-integral coefficients.
Suppose `y` in `B = S[X]/f` is `R`-integral, then `f' * y` is the image of some `g : S[X]` with
`R`-integral coefficients. -/
-- We can also know that `deg g = deg f - 1`. Upgrade the lemma if we care.
@[stacks 03GD]
/-
**exists_derivative_mul_eq_and_isIntegral_coeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_derivative_mul_eq_and_isIntegral_coeff {φ : S[X] ->ₐ[R] B} (hφ : Fu
nction.Surjective φ) {f : S[X]} (hf : f.Monic) (hf' : forall i, IsIntegral R (f.
coeff i)) (hfx : RingHom.ker φ.toRingHom = .span {f}) {y : B} (hy : IsIntegral R
 y) : exists (g : S[X]), φ f.derivative * y = φ g ∧ forall i, IsIntegral R (g.co
eff i)
参数：hφ : Function.Surjective φ；hf : f.Monic；hf' : forall i, IsIntegral R (f.coeff
 i)；hfx : RingHom.ker φ.toRingHom = .span {f}；hy : IsIntegral R y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.Monic.natDegree_eq_zero`：∀ {R : Type u} [inst : Semiring R] {
p : Polynomial R}, p.Monic → (p.natDegree = 0 ↔ p = 1)
· 使用定理 `Ideal.span_singleton_one`：span_singleton_one : span ({1} : Set α) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Ne.trans_eq`：∀ {α : Sort u_1} {a b c : α}, a ≠ b → b = c → a ≠ c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `RingHom.ker_ne_top`：ker_ne_top [Nontrivial S] (f : F) : ker f != ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用引理 `Polynomial.Monic.exists_splits_map`：Polynomial.Monic.exists_splits_map.{
u} {R : Type u} [CommRing R] [Nontrivial R] {p : R[X]} (hp : p.Monic) : exists (
S : Type u) (_ : CommRin…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.splits_iff_exists_multiset`：splits_iff_exists_multiset : Spli
ts f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用引理 `IsIntegral.of_aeval_monic_of_isIntegral_coeff`：IsIntegral.of_aeval_monic
_of_isIntegral_coeff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {x : 
A} {p : A[X]} (monic : p.Monic) (de…
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
（共 115 条，此处仅展示前 30 条）
-/
lemma exists_derivative_mul_eq_and_isIntegral_coeff
    {φ : S[X] →ₐ[R] B} (hφ : Function.Surjective φ) {f : S[X]} (hf : f.Monic)
    (hf' : ∀ i, IsIntegral R (f.coeff i))
    (hfx : RingHom.ker φ.toRingHom = .span {f}) {y : B} (hy : IsIntegral R y) :
    ∃ (g : S[X]), φ f.derivative * y = φ g ∧ ∀ i, IsIntegral R (g.coeff i) := by
  cases subsingleton_or_nontrivial B
  · exact ⟨0, Subsingleton.elim _ _, by simp [isIntegral_zero]⟩
  have hfd : f.natDegree ≠ 0 := by
    rw [ne_eq, hf.natDegree_eq_zero]
    rintro rfl
    simpa using (RingHom.ker_ne_top φ.toRingHom).symm.trans_eq hfx
  classical
  algebraize [φ.toRingHom.comp C]
  have := (algebraMap S B).domain_nontrivial
  obtain ⟨y, rfl⟩ := hφ y
  -- Consider the universal extension `S'` of `S` that splits `f`, so that `f = ∏ᵢ X - aᵢ`.
  obtain ⟨S', _, _, _, _, _, hS'⟩ := hf.exists_splits_map
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hS'
  simp only [hf.map _, Monic.leadingCoeff, map_one, one_mul] at hm
  algebraize [(algebraMap S S').comp (algebraMap R S)]
  -- Each `aᵢ` is integral since `f` is still monic in `S'`.
  have hm' : ∀ a ∈ m, IsIntegral R a := by
    refine fun a ham ↦ .of_aeval_monic_of_isIntegral_coeff (hf.map (algebraMap _ _)) ?_ ?_ ?_
    · rwa [hf.natDegree_map]
    · rw [hm, eval_multiset_prod, Multiset.prod_eq_zero]
      · exact isIntegral_zero
      · simpa using ⟨a, ham, by simp⟩
    · simp only [coeff_map]
      exact fun _ ↦ (hf' _).algebraMap
  have hmc : m.card = f.natDegree := by
    simpa [hf.natDegree_map, natDegree_multiset_prod_of_monic] using congr(($hm).natDegree).symm
  -- The key identity is `y * f' ≡ ∑ᵢ y(aᵢ) * ∏_{j ≠ i} X - aⱼ (mod f)`.
  have H : (f.derivative * y %ₘ f).map (algebraMap S S') =
        (m.map fun x ↦ ((m.erase x).map (X - C ·)).prod * C (aeval x y)).sum := by
    have ⟨g, hg⟩ : f.map (algebraMap _ _) ∣ (f.derivative * y).map (algebraMap S S') -
        (m.map fun x ↦ ((m.erase x).map (X - C ·)).prod * C (aeval x y)).sum := by
      rw [Polynomial.map_mul, ← Polynomial.derivative_map, hm, derivative_prod,
        ← Multiset.sum_map_mul_right, ← Multiset.sum_map_sub]
      refine Multiset.dvd_sum ?_
      simp only [derivative_sub, derivative_X, derivative_C, sub_zero, mul_one, ← mul_sub,
        Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro a ham
      conv_lhs => rw [← Multiset.cons_erase ham]
      rw [Multiset.map_cons, Multiset.prod_cons, mul_comm]
      refine mul_dvd_mul_left _ ?_
      simp [Polynomial.dvd_iff_isRoot]
    rw [map_modByMonic _ hf]
    refine (div_modByMonic_unique g _ (hf.map _) ⟨(sub_eq_iff_eq_add'.mp hg).symm, ?_⟩).2
    refine degree_lt_degree ?_
    rw [hf.natDegree_map, ← Nat.le_sub_one_iff_lt (Ne.bot_lt hfd)]
    refine (natDegree_multiset_sum_le _).trans (Multiset.max_le_of_forall_le _ _ ?_)
    simp only [Multiset.map_map, Function.comp_apply, Multiset.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    refine fun a ha ↦ (natDegree_mul_C_le _ _).trans ((natDegree_multiset_prod_le _).trans ?_)
    simp [ha, hmc]
  -- Every `y(aᵢ)` is `R`-integral as y is also `R`-integral by assumption.
  have H' (a : S') (ham : a ∈ m) : IsIntegral R (aeval a y) := by
    let ψ : B →ₐ[R] S' := AlgHom.liftOfSurjective _ hφ ((aeval a).restrictScalars R) <| by
      rw [hfx, Ideal.span_le]
      suffices (m.map (a - ·)).prod = 0 by simpa [← eval_map_algebraMap, hm, eval_multiset_prod]
      rw [Multiset.prod_eq_zero]
      simpa using ⟨a, ham, by simp⟩
    simpa [ψ] using hy.map ψ
  -- So `y * f' mod f` is integral over `R[X]` (i.e. its coefficients are `R`-integral)
  -- as a sum of products of integral elements.
  have H'' : IsIntegral R[X] (f.derivative * y %ₘ f) := by
    refine .tower_bot (B := S'[X]) (map_injective _ (FaithfulSMul.algebraMap_injective S S')) ?_
    simp only [algebraMap_def, coe_mapRingHom, H]
    refine .multiset_sum ?_
    simp only [Multiset.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    refine fun a ham ↦ .mul (.multiset_prod ?_) ?_
    · simp only [Multiset.mem_map, Polynomial.isIntegral_iff_isIntegral_coeff, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, coeff_sub]
      exact fun b hbm n ↦ .sub (by simp [coeff_X, apply_ite, isIntegral_one, isIntegral_zero])
        (by simp [coeff_C, apply_ite, isIntegral_zero, hm' b (Multiset.mem_of_mem_erase hbm)])
    · simpa [isIntegral_iff_isIntegral_coeff, coeff_C, apply_ite, isIntegral_zero] using H' a ham
  refine ⟨_, ?_, Polynomial.isIntegral_iff_isIntegral_coeff.mp H''⟩
  rw [modByMonic_eq_sub_mul_div, map_sub, map_mul, map_mul,
    show φ f = 0 from hfx.ge (Ideal.mem_span_singleton_self _), zero_mul, sub_zero]

open TensorProduct

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Polynomial.algebra in
@[stacks 03GE "without the generalization to arbitrary etale algebra"]
/-
**mem_adjoin_map_integralClosure_of_isStandardEtale** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：mem_adjoin_map_integralClosure_of_isStandardEtale [Algebra.IsStandardEtale
 R S] (a : S otimes[R] B) (hx : IsIntegral S a) : a in Algebra.adjoin S ((integr
alClosure R B).map Algebra.TensorProduct.includeRight : Subalgebra R (S otimes[R
] B))
参数：a : S otimes[R] B；hx : IsIntegral S a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsStandardEtale.nonempty_standardEtalePresentation`：∀ {R : Type 
u_4} {S : Type u_5} {inst : CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra 
R S}   [self : Algebra.IsStandardEtale R S], Non…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.isLocalization_of_algEquiv`：isLocalization_of_algEquiv [A
lgebra R P] [IsLocalization M S] (h : S ≃ₐ[R] P) : IsLocalization M P
· 使用定理 `RingEquiv.map_mul'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `RingEquiv.map_add'`：∀ {R : Type u_7} {S : Type u_8} [inst : Mul R] [inst
_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (self : R ≃+* S)   (x y : R), self
.toFun (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `IsIntegral.exists_multiple_integral_of_isLocalization`：IsIntegral.exists
_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsScalarTower R Rₘ S] (x : 
S) (hx : IsIntegral Rₘ x) : exists m : M, I…
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `isIntegral_algebraMap`：isIntegral_algebraMap {x : R} : IsIntegral R (alg
ebraMap R A x)
· 使用定理 `Polynomial.Monic.finite_adjoinRoot`：∀ {R : Type u_1} [inst : CommRing R]
 {g : Polynomial R}, g.Monic → Module.Finite R (AdjoinRoot g)
· 使用定理 `StandardEtalePair.monic_f`：∀ {R : Type u_1} [inst : CommRing R] (self : 
StandardEtalePair R), self.f.Monic
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_symm_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `IsLocalization.Away.lift_eq`：lift_eq (hg : IsUnit (g x)) (a : R) : lift 
x hg (algebraMap R S a) = g a
· 使用定理 `AdjoinRoot.lift_mk`：lift_mk (g : R[X]) : lift i a h (mk f g) = g.eval₂ i
 a
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `StandardEtalePresentation.equivRing_symm_X`：StandardEtalePresentation.eq
uivRing_symm_X : P.equivRing.symm P.X = P.x
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
（共 125 条，此处仅展示前 30 条）
-/
theorem mem_adjoin_map_integralClosure_of_isStandardEtale [Algebra.IsStandardEtale R S]
    (a : S ⊗[R] B) (hx : IsIntegral S a) :
    a ∈ Algebra.adjoin S
      ((integralClosure R B).map Algebra.TensorProduct.includeRight : Subalgebra R (S ⊗[R] B)) := by
  -- By assumption, `S = (R[X]/f)[1/g]` for some `f g : R[X]`. Let `x : S` denote the image of `X`.
  have 𝓟 := Classical.ofNonempty (α := StandardEtalePresentation R S)
  -- Since `a` is integral over `S = (R[X]/f)[1/g]`, `gⁿ • a` is `R`-integral for `n` large enough.
  obtain ⟨n, hx⟩ : ∃ n, ∀ m, IsIntegral R ((aeval 𝓟.x 𝓟.g) ^ (n + m) • a) := by
    let e := 𝓟.equivRing.trans 𝓟.equivAwayAdjoinRoot
    algebraize [(e.symm.toAlgHom.comp (IsScalarTower.toAlgHom R (AdjoinRoot 𝓟.f) _)).toRingHom]
    have := IsLocalization.isLocalization_of_algEquiv (R := AdjoinRoot 𝓟.f) (.powers (.mk _ 𝓟.g))
      { toRingEquiv := e.symm.toRingEquiv, commutes' := by simp [RingHom.algebraMap_toAlgebra] }
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := AdjoinRoot 𝓟.f) (.powers (.mk _ 𝓟.g)) _ hx
    replace hm := fun k : ℕ ↦ (isIntegral_algebraMap (x := AdjoinRoot.mk 𝓟.f 𝓟.g ^ k)).mul hm
    simp only [Submonoid.smul_def, ← @IsScalarTower.algebraMap_smul (AdjoinRoot 𝓟.f) S,
      ← map_pow, ← Algebra.smul_def, ← mul_smul, ← map_mul, ← pow_add, add_comm _ m] at hm
    simp_rw [map_pow] at hm
    have := 𝓟.monic_f.finite_adjoinRoot
    suffices algebraMap (AdjoinRoot 𝓟.f) S (.mk _ 𝓟.g) = aeval 𝓟.x 𝓟.g from
      ⟨m, fun k ↦ this ▸ isIntegral_trans (R := R) _ (hm k)⟩
    simp [RingHom.algebraMap_toAlgebra, e, StandardEtalePair.equivAwayAdjoinRoot,
      ← aeval_def, ← aeval_algHom_apply]
  -- Under `S ⊗[R] B ≃ (B[X]/f)[1/g]`, we may write `a` as `a/gᵐ` with `a` now living in `B[X]/f`.
  let 𝓟' := 𝓟.baseChange (T := B)
  let e := 𝓟'.equivRing.trans 𝓟'.equivAwayAdjoinRoot
  obtain ⟨a, rfl⟩ := (Algebra.TensorProduct.comm _ _ _).surjective a
  obtain ⟨a, rfl⟩ := e.symm.surjective a
  obtain ⟨a, ⟨_, m, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq
    (R := AdjoinRoot 𝓟'.f) (.powers (.mk _ 𝓟'.g)) a
  have hfg : IsIntegral R (AdjoinRoot.mk 𝓟'.f 𝓟'.g) := by
    have := 𝓟.monic_f.finite_adjoinRoot
    let e : AdjoinRoot 𝓟.f →ₐ[R] AdjoinRoot 𝓟'.f :=
      AdjoinRoot.mapAlgHom (Algebra.ofId _ _) _ _ (dvd_refl _)
    convert! (Algebra.IsIntegral.isIntegral (R := R) (AdjoinRoot.mk 𝓟.f 𝓟.g)).map e
    have : (AdjoinRoot.mk 𝓟'.f).comp (mapRingHom (algebraMap R B)) =
        e.toRingHom.comp (AdjoinRoot.mk _) := by ext <;> simp [e]
    exact congr($this 𝓟.g)
  have heg (g : R[X]) : e (1 ⊗ₜ aeval 𝓟.x g) =
      algebraMap _ _ (AdjoinRoot.mk 𝓟'.f (g.map (algebraMap _ _))) := by
    trans e (aeval (1 ⊗ₜ 𝓟.x) (g.map (algebraMap _ B)))
    · rw [← Algebra.TensorProduct.includeRight_apply, ← aeval_algHom_apply]
      simp [StandardEtalePresentation.baseChange, 𝓟']
    rw [← e.eq_symm_apply]
    simp [e, StandardEtalePair.equivAwayAdjoinRoot, ← aeval_def, ← aeval_algHom_apply]
    rfl
  -- And `gᵏ • a` is still `R`-integral for `k` large enough.
  obtain ⟨k, hk⟩ : ∃ k, IsIntegral R (AdjoinRoot.mk 𝓟'.f 𝓟'.g ^ k * a) := by
    have H : ∀ k, e (1 ⊗ₜ (aeval 𝓟.x 𝓟.g ^ k)) = algebraMap _ _ (AdjoinRoot.mk 𝓟'.f 𝓟'.g ^ k) := by
      intro k; convert! congr($(heg 𝓟.g) ^ k) <;>
        simp [← map_pow, 𝓟', StandardEtalePresentation.baseChange]
    have := ((hx m).map (Algebra.TensorProduct.comm _ _ _).symm).map e
    simp only [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, map_mul, Algebra.TensorProduct.comm_symm_tmul, AlgEquiv.symm_apply_apply,
      AlgEquiv.apply_symm_apply] at this
    rw [H, pow_add, map_mul, mul_assoc, IsLocalization.mk'_spec'_mk, ← map_mul] at this
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap hfg this
    refine ⟨k + n, by convert! hk using 1; ring_nf⟩
  -- We now use the key lemma `exists_derivative_mul_eq_and_isIntegral_coeff` to get a `y : B[X]`
  -- with `R`-integral coefficients such that `f' * gᵏ * a = y` in `S ⊗[R] B`.
  obtain ⟨y, hy, hRy⟩ := exists_derivative_mul_eq_and_isIntegral_coeff
    (φ := (AdjoinRoot.mkₐ 𝓟'.f).restrictScalars R) AdjoinRoot.mk_surjective 𝓟'.monic_f
    (by simp [𝓟', StandardEtalePresentation.baseChange, isIntegral_algebraMap]) Ideal.mk_ker hk
  simp only [AlgHom.coe_restrictScalars', AdjoinRoot.coe_mkₐ] at hy
  -- Since `f' * gᵏ` is invertible in S, to show that `a ∈ S ⊗ B'` (where `B'` is the
  -- integral closure of `R` in `B`), it suffices to show that `y ∈ S ⊗ B'`,
  rw [← Subalgebra.mem_toSubmodule, ← Submodule.smul_mem_iff_of_isUnit _
    (𝓟.hasMap.isUnit_derivative_f.mul <| (𝓟.hasMap.2.pow k).mul (𝓟.hasMap.2.pow m))]
  convert_to eval₂ Algebra.TensorProduct.includeRight.toRingHom (𝓟.x ⊗ₜ[R] 1) y ∈ _ using 1
  · convert! congr(Algebra.TensorProduct.comm _ _ _ <| e.symm (algebraMap _ _ $hy))
    · apply (Algebra.TensorProduct.comm R B S).symm.injective
      apply e.injective
      simp only [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, map_mul, Algebra.TensorProduct.comm_symm_tmul, AlgEquiv.symm_apply_apply,
        AlgEquiv.apply_symm_apply, map_pow, heg]
      simp_rw [mul_assoc, ← map_pow, show 𝓟.g.map (algebraMap R B) = 𝓟'.g from rfl,
        IsLocalization.mk'_spec'_mk, ← derivative_map]; rfl
    · simp only [← AlgEquiv.coe_toAlgHom, ← AlgHom.coe_toRingHom, ← RingHom.comp_apply,
        ← coe_eval₂RingHom]
      congr 1
      ext <;> simp [e, StandardEtalePair.equivAwayAdjoinRoot]; rfl
  -- which follows from the fact that `y` has `R`-integral coefficients.
  rw [eval₂_eq_sum_range]
  exact sum_mem fun i hi ↦ Subalgebra.mul_mem _ (Algebra.subset_adjoin ⟨_, hRy _, rfl⟩)
    (pow_mem (Subalgebra.algebraMap_mem _ _) _)

-- Subsumed by `TensorProduct.toIntegralClosure_bijective_of_smooth`
/-
**TensorProduct.toIntegralClosure_bijective_of_isStandardEtale** 是 Mathlib 中的一个定
理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem TensorProduct.toIntegralClosure_bijective_of_isStandardEtale
    [Algebra.IsStandardEtale R S] : Function.Bijective (toIntegralClosure R S B) := by
  refine ⟨toIntegralClosure_injective_of_flat, ?_⟩
  intro ⟨x, hx⟩
  simp only [toIntegralClosure, Subtype.ext_iff, AlgHom.coe_codRestrict, ← AlgHom.mem_range]
  refine Algebra.adjoin_le ?_ (mem_adjoin_map_integralClosure_of_isStandardEtale x hx)
  rintro _ ⟨y, hy : IsIntegral _ _, rfl⟩
  refine ⟨1 ⊗ₜ ⟨y, hy⟩, by simp⟩

end IsStandardEtale

/-
**TensorProduct.toIntegralClosure_bijective_of_smooth** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：TensorProduct.toIntegralClosure_bijective_of_smooth [Algebra.Smooth R S] :
 Function.Bijective (toIntegralClosure R S B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`：∀ {R : Type u_1}
 {S : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]
 {p : Ideal S}   [inst_3 : p.IsPrime] [Algeb…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.Smooth.finitePresentation`：∀ {R : Type u_4} {inst : CommRing R} 
{A : Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smoo
th R A], Algebra.Finite…
· 使用定理 `Algebra.FormallySmooth.instLocalization`：∀ {R : Type u_4} {A : Type u_5}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.For
mallySmooth R A] (M : Submono…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
· 使用引理 `TensorProduct.toIntegralClosure_bijective_of_tower`：TensorProduct.toInte
gralClosure_bijective_of_tower {T : Type*} [CommRing T] [Algebra R T] [Algebra S
 T] [IsScalarTower R S T] (H : Function.…
· 使用引理 `TensorProduct.toIntegralClosure_mvPolynomial_bijective`：TensorProduct.to
IntegralClosure_mvPolynomial_bijective {σ : Type*} : Function.Bijective (toInteg
ralClosure R (MvPolynomial σ R) B)
· 使用定理 `_private.Mathlib.RingTheory.Smooth.IntegralClosure.0.TensorProduct.toInt
egralClosure_bijective_of_isStandardEtale`：∀ {R : Type u_1} {S : Type u_2} {B : 
Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [in
st_3 : CommRing B] [ins…
· 使用引理 `TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway`：TensorP
roduct.toIntegralClosure_bijective_of_isLocalizationAway {s : Set S} (hs : Ideal
.span s = ⊤) (Sᵣ : s -> Type*) [forall r, CommRing (S…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_subtype_range_iff`：forall_subtype_range_iff {p : range f -> P
rop} : (forall a : range f, p a) ↔ forall i, p ⟨f i, mem_range_self _⟩
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem TensorProduct.toIntegralClosure_bijective_of_smooth [Algebra.Smooth R S] :
    Function.Bijective (toIntegralClosure R S B) := by
  have (m : PrimeSpectrum S) : ∃ f ∉ m.asIdeal,
      Function.Bijective (toIntegralClosure R (Localization.Away f) B) := by
    obtain ⟨f, hfm, n, _, _, _⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := m.asIdeal)
    exact ⟨f, hfm, toIntegralClosure_bijective_of_tower (S := MvPolynomial (Fin n) R)
      toIntegralClosure_mvPolynomial_bijective toIntegralClosure_bijective_of_isStandardEtale⟩
  choose f hfm hf using this
  refine TensorProduct.toIntegralClosure_bijective_of_isLocalizationAway (R := R)
    (s := Set.range f) (B := B) ?_ (Localization.Away ·.1) (Set.forall_subtype_range_iff.mpr hf)
  by_contra H
  obtain ⟨m, hm, e⟩ := Ideal.exists_le_maximal _ H
  exact hfm ⟨m, inferInstance⟩ (e (Ideal.subset_span (Set.mem_range_self ⟨m, inferInstance⟩)) :)
