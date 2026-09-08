/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Flat.Localization

/-!
# The differential module and étale algebras

## Main results
- `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`:
  The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally étale `S`-algebra.
- `Algebra.tensorH1CotangentOfIsLocalization`:
  The canonical isomorphism `T ⊗[S] H¹(L_{S⁄R}) ≃ₗ[T] H¹(L_{T⁄R})` for `T` a localization of `S`.
-/

@[expose] public section

universe u

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

open TensorProduct

/--
The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally étale `S`-algebra.
Also see `S ⊗[R] Ω[A⁄R] ≃ₗ[S] Ω[S ⊗[R] A⁄S]` at `KaehlerDifferential.tensorKaehlerEquiv`.
-/
@[simps! apply] noncomputable
/-
**KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale** 是 Mathlib 中的一个定义，位于命名空
间 ``。
形式化陈述：KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale [Algebra.FormallyEta
le S T] : T otimes[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally étale 
`S`-algebra.
Also see `S ⊗[R] Ω[A⁄R] ≃ₗ[S] Ω[S ⊗[R] A⁄S]` at `KaehlerDifferential.tensorKaehl
erEquiv`.
-/
def KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale [Algebra.FormallyEtale S T] :
    T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R] := by
  refine LinearEquiv.ofBijective (mapBaseChange R S T)
    ⟨?_, fun x ↦ (KaehlerDifferential.exact_mapBaseChange_map R S T x).mp (Subsingleton.elim _ _)⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T x).mp hx
  rw [Subsingleton.elim x 0, map_zero]
/-
**KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap** 是 Ma
thlib 中的一个引理，位于命名空间 ``。
形式化陈述：KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap [A
lgebra.FormallyEtale S T] (s : S) : (tensorKaehlerEquivOfFormallyEtale R S T).sy
mm (D R T (algebraMap S T s)) = 1 otimesₜ D R S s
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply`：∀ (R : Type
 u_1) (S : Type u_2) (T : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : CommRing T]   [inst_3 : Algebra R S] [ins…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `KaehlerDifferential.mapBaseChange_tmul`：KaehlerDifferential.mapBaseChang
e_tmul (x : B) (y : Ω[A⁄R]) : KaehlerDifferential.mapBaseChange R A B (x otimesₜ
 y) = x • KaehlerDifferentia…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `KaehlerDifferential.map_D`：KaehlerDifferential.map_D (x : A) : KaehlerDi
fferential.map R S A B (KaehlerDifferential.D R A x) = KaehlerDifferential.D S B
 (algebraMap A …
-/
lemma KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
    [Algebra.FormallyEtale S T] (s : S) :
    (tensorKaehlerEquivOfFormallyEtale R S T).symm (D R T (algebraMap S T s)) = 1 ⊗ₜ D R S s := by
  rw [LinearEquiv.symm_apply_eq, tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul,
    one_smul, map_D]
/-
**KaehlerDifferential.isBaseChange_of_formallyEtale** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：KaehlerDifferential.isBaseChange_of_formallyEtale [Algebra.FormallyEtale S
 T] : IsBaseChange T (map R R S T)
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
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Derivation.liftKaehlerDifferential_unique`：Derivation.liftKaehlerDiffere
ntial_unique (f f' : Ω[S⁄R] ->ₗ[S] M) (hf : f.compDer (KaehlerDifferential.D R S
) = f'.compDer (KaehlerDifferen…
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
· 使用定理 `KaehlerDifferential.map_D`：KaehlerDifferential.map_D (x : A) : KaehlerDi
fferential.map R S A B (KaehlerDifferential.D R A x) = KaehlerDifferential.D S B
 (algebraMap A …
· 使用定理 `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply`：∀ (R : Type
 u_1) (S : Type u_2) (T : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [i
nst_2 : CommRing T]   [inst_3 : Algebra R S] [ins…
· 使用定理 `KaehlerDifferential.mapBaseChange_tmul`：KaehlerDifferential.mapBaseChang
e_tmul (x : B) (y : Ω[A⁄R]) : KaehlerDifferential.mapBaseChange R A B (x otimesₜ
 y) = x • KaehlerDifferentia…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
lemma KaehlerDifferential.isBaseChange_of_formallyEtale [Algebra.FormallyEtale S T] :
    IsBaseChange T (map R R S T) := by
  change Function.Bijective _
  convert! (tensorKaehlerEquivOfFormallyEtale R S T).bijective using 1
  change _ = ((tensorKaehlerEquivOfFormallyEtale
    R S T).toLinearMap.restrictScalars S : T ⊗[S] Ω[S⁄R] → _)
  congr!
  ext
  simp
/-
**KaehlerDifferential.isLocalizedModule_map** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：KaehlerDifferential.isLocalizedModule_map (M : Submonoid S) [IsLocalizatio
n M T] : IsLocalizedModule M (map R R S T)
参数：M : Submonoid S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FormallyEtale.of_isLocalization`：of_isLocalization : FormallyEta
le R Rₘ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用引理 `KaehlerDifferential.isBaseChange_of_formallyEtale`：KaehlerDifferential.i
sBaseChange_of_formallyEtale [Algebra.FormallyEtale S T] : IsBaseChange T (map R
 R S T)
-/
instance KaehlerDifferential.isLocalizedModule_map (M : Submonoid S) [IsLocalization M T] :
    IsLocalizedModule M (map R R S T) :=
  have := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  (isLocalizedModule_iff_isBaseChange M T _).mpr (isBaseChange_of_formallyEtale R S T)
/-
**KaehlerDifferential.span_range_map_derivation_of_isLocalization** 是 Mathlib 中的
一个引理，位于命名空间 ``。
形式化陈述：KaehlerDifferential.span_range_map_derivation_of_isLocalization (M : Submo
noid S) [IsLocalization M T] : Submodule.span T (Set.range <| map R R S T ∘ D R 
S) = ⊤
参数：M : Submonoid S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `span_eq_top_of_isLocalizedModule`：span_eq_top_of_isLocalizedModule {v : 
Set M} (hv : span R v = ⊤) : span Rₛ (f '' v) = ⊤
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `KaehlerDifferential.span_range_derivation`：KaehlerDifferential.span_rang
e_derivation : Submodule.span S (Set.range <| KaehlerDifferential.D R S) = ⊤
-/
lemma KaehlerDifferential.span_range_map_derivation_of_isLocalization
    (M : Submonoid S) [IsLocalization M T] :
    Submodule.span T (Set.range <| map R R S T ∘ D R S) = ⊤ := by
  convert!
    span_eq_top_of_isLocalizedModule T M (map R R S T) (v := Set.range <| D R S)
      (span_range_derivation R S)
  rw [← Set.range_comp, Function.comp_def]

namespace Algebra.Extension

open KaehlerDifferential

attribute [local instance] SMulCommClass.of_commMonoid

variable {R S T}

/-!
Suppose we have a morphism of extensions of `R`-algebras
```
0 → J → Q → T → 0
    ↑   ↑   ↑
0 → I → P → S → 0
```
-/
variable {P : Extension.{u} R S} {Q : Extension.{u} R T} (f : P.Hom Q)

set_option backward.defeqAttrib.useBackward true in
/-- If `P → Q` is formally étale, then `T ⊗ₛ (S ⊗ₚ Ω[P/R]) ≃ T ⊗_Q Ω[Q/R]`. -/
noncomputable
/-
**Algebra.Extension.tensorCotangentSpaceOfFormallyEtale** 是 Mathlib 中的一个定义，位于命名空
间 `Algebra.Extension`。
形式化陈述：tensorCotangentSpaceOfFormallyEtale (H : f.toRingHom.FormallyEtale) : T ot
imes[S] P.CotangentSpace ≃ₗ[T] Q.CotangentSpace
参数：H : f.toRingHom.FormallyEtale。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def tensorCotangentSpaceOfFormallyEtale
    (H : f.toRingHom.FormallyEtale) :
    T ⊗[S] P.CotangentSpace ≃ₗ[T] Q.CotangentSpace :=
  letI := f.toRingHom.toAlgebra
  haveI : IsScalarTower R P.Ring Q.Ring :=
    .of_algebraMap_eq fun r ↦ (f.toRingHom_algebraMap r).symm
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r ↦ (f.algebraMap_toRingHom r).symm
  haveI : FormallyEtale P.Ring Q.Ring := ‹_›
  { __ := (CotangentSpace.map f).liftBaseChange T
    invFun := LinearMap.liftBaseChange T (by
      refine LinearMap.liftBaseChange _ ?_ ∘ₗ
        (tensorKaehlerEquivOfFormallyEtale R P.Ring Q.Ring).symm.toLinearMap
      exact (TensorProduct.mk _ _ _ 1).restrictScalars P.Ring ∘ₗ
        (TensorProduct.mk _ _ _ 1).restrictScalars P.Ring)
    left_inv x := by
      change (LinearMap.liftBaseChange _ _ ∘ₗ LinearMap.liftBaseChange _ _) x =
        LinearMap.id (R := T) x
      congr 1
      ext : 4
      refine Derivation.liftKaehlerDifferential_unique
        (R := R) (S := P.Ring) (M := T ⊗[S] P.CotangentSpace) _ _ ?_
      ext a
      have : (tensorKaehlerEquivOfFormallyEtale R P.Ring Q.Ring).symm
          ((D R Q.Ring) (f.toRingHom a)) = 1 ⊗ₜ D _ _ a :=
        tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap R P.Ring Q.Ring a
      simp [this]
    right_inv x := by
      change (LinearMap.liftBaseChange _ _ ∘ₗ LinearMap.liftBaseChange _ _) x =
        LinearMap.id (R := T) x
      congr 1
      ext a
      dsimp
      obtain ⟨x, hx⟩ := (tensorKaehlerEquivOfFormallyEtale R P.Ring _).surjective (D R Q.Ring a)
      simp only [one_smul, ← hx, LinearEquiv.symm_apply_apply]
      change (((CotangentSpace.map f).liftBaseChange T).restrictScalars Q.Ring ∘ₗ
        LinearMap.liftBaseChange _ _) x = ((TensorProduct.mk _ _ _ 1) ∘ₗ
          (tensorKaehlerEquivOfFormallyEtale R P.Ring Q.Ring).toLinearMap) x
      congr 1
      ext a
      simp; rfl }

/-- (Implementation)
If `J ≃ Q ⊗ₚ I` (e.g. when `T = Q ⊗ₚ S` and `P → Q` is flat), then `T ⊗ₛ I/I² ≃ J/J²`.
This is the inverse. -/
noncomputable
/-
**Algebra.Extension.tensorCotangentInvFun** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Ext
ension`。
形式化陈述：tensorCotangentInvFun [alg : Algebra P.Ring Q.Ring] (halg : algebraMap P.R
ing Q.Ring = f.toRingHom) (H : Function.Bijective ((f.mapKer halg).liftBaseChang
e Q.Ring)) : Q.Cotangent ->+ T otimes[S] P.Cotangent
参数：halg : algebraMap P.Ring Q.Ring = f.toRingHom；H : Function.Bijective ((f.mapK
er halg).liftBaseChange Q.Ring)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def tensorCotangentInvFun
    [alg : Algebra P.Ring Q.Ring] (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) :
    Q.Cotangent →+ T ⊗[S] P.Cotangent :=
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r ↦ halg ▸ (f.algebraMap_toRingHom r).symm
  letI e := LinearEquiv.ofBijective _ H
  letI f' : Q.ker →ₗ[Q.Ring] T ⊗[S] P.Cotangent :=
    (LinearMap.liftBaseChange _
      ((TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ Cotangent.mk)) ∘ₗ e.symm.toLinearMap
  QuotientAddGroup.lift _ f' <| by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ fun _ _ ↦ add_mem
    clear x hx
    rintro a ha b -
    obtain ⟨x, hx⟩ := e.surjective ⟨a, ha⟩
    obtain rfl : (e x).1 = a := congr_arg Subtype.val hx
    obtain ⟨y, rfl⟩ := e.surjective b
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_coe, map_smul,
      LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, f']
    clear hx ha
    induction x with
    | zero => simp only [map_zero, ZeroMemClass.coe_zero, zero_smul]
    | add x y _ _ =>
      simp only [map_add, Submodule.coe_add, add_smul, zero_add, *]
    | tmul a b =>
      induction y with
      | zero => simp only [map_zero, smul_zero]
      | add x y hx hy => simp only [LinearMap.map_add, smul_add, hx, hy, zero_add]
      | tmul c d =>
        simp only [LinearMap.liftBaseChange_tmul, LinearMap.coe_comp, SetLike.val_smul,
          LinearMap.coe_restrictScalars, Function.comp_apply, mk_apply, smul_eq_mul, e,
          LinearMap.liftBaseChange_tmul, LinearEquiv.ofBijective_apply]
        have h₂ : b.1 • Cotangent.mk d = 0 := by ext; simp [Cotangent.smul_eq_zero_of_mem _ b.2]
        rw [TensorProduct.smul_tmul', mul_smul, f.mapKer_apply_coe, ← halg,
          algebraMap_smul, ← TensorProduct.tmul_smul, h₂, tmul_zero, smul_zero]

omit [IsScalarTower R S T] in
/-
**Algebra.Extension.tensorCotangentInvFun_smul_mk** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebra.Extension`。
形式化陈述：tensorCotangentInvFun_smul_mk [alg : Algebra P.Ring Q.Ring] (halg : algebr
aMap P.Ring Q.Ring = f.toRingHom) (H : Function.Bijective ((f.mapKer halg).liftB
aseChange Q.Ring)) (x : Q.Ring) (y : P.ker) : tensorCotangentInvFun f halg H (x 
• .mk ⟨f.toRingHom y, (f.mapKer halg y).2⟩) = x • 1 otimesₜ .mk y
参数：halg : algebraMap P.Ring Q.Ring = f.toRingHom；H : Function.Bijective ((f.mapK
er halg).liftBaseChange Q.Ring)；x : Q.Ring；y : P.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.Extension.Hom.algebraMap_toRingHom`：∀ {R : Type u} {S : Type v} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Ex
tension R S}   {R' : Type u_1} {…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tensorCotangentInvFun_smul_mk
    [alg : Algebra P.Ring Q.Ring] (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) (x : Q.Ring) (y : P.ker) :
    tensorCotangentInvFun f halg H (x • .mk ⟨f.toRingHom y, (f.mapKer halg y).2⟩) =
      x • 1 ⊗ₜ .mk y := by
  let := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  have : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  have : IsScalarTower P.Ring Q.Ring T :=
    .of_algebraMap_eq fun r ↦ halg ▸ (f.algebraMap_toRingHom r).symm
  let e := LinearEquiv.ofBijective _ H
  trans tensorCotangentInvFun f halg H (.mk ((f.mapKer halg).liftBaseChange Q.Ring (x ⊗ₜ y)))
  · simp; rfl
  change ((TensorProduct.mk _ _ _ 1).restrictScalars _ ∘ₗ Cotangent.mk).liftBaseChange _
    (e.symm (e (x ⊗ₜ y))) = _
  rw [e.symm_apply_apply]
  simp

/-- If `J ≃ Q ⊗ₚ I` (e.g. when `T = Q ⊗ₚ S` and `P → Q` is flat), then `T ⊗ₛ I/I² ≃ J/J²`. -/
noncomputable
/-
**Algebra.Extension.tensorCotangent** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension
`。
形式化陈述：tensorCotangent [alg : Algebra P.Ring Q.Ring] (halg : algebraMap P.Ring Q.
Ring = f.toRingHom) (H : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ri
ng)) : T otimes[S] P.Cotangent ≃ₗ[T] Q.Cotangent
参数：halg : algebraMap P.Ring Q.Ring = f.toRingHom；H : Function.Bijective ((f.mapK
er halg).liftBaseChange Q.Ring)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def tensorCotangent [alg : Algebra P.Ring Q.Ring] (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (H : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) :
    T ⊗[S] P.Cotangent ≃ₗ[T] Q.Cotangent :=
  { __ := (Cotangent.map f).liftBaseChange T
    invFun := tensorCotangentInvFun f halg H
    left_inv x := by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      induction x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul a b =>
        obtain ⟨b, rfl⟩ := Cotangent.mk_surjective b
        obtain ⟨a, rfl⟩ := Q.algebraMap_surjective a
        simp only [LinearMap.liftBaseChange_tmul, Cotangent.map_mk, Hom.toAlgHom_apply,
          algebraMap_smul]
        refine (tensorCotangentInvFun_smul_mk f halg H a b).trans ?_
        simp [algebraMap_eq_smul_one, TensorProduct.smul_tmul']
    right_inv x := by
      obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
      obtain ⟨x, rfl⟩ := H.surjective x
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      induction x with
      | zero => simp only [map_zero]
      | add x y _ _ => simp only [map_add, *]
      | tmul a b =>
        simp only [LinearMap.liftBaseChange_tmul, map_smul]
        simp [Hom.mapKer, tensorCotangentInvFun_smul_mk] }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `J ≃ Q ⊗ₚ I`, `S → T` is flat and `P → Q` is formally étale, then `T ⊗ H¹(L_P) ≃ H¹(L_Q)`. -/
noncomputable
/-
**Algebra.Extension.tensorH1CotangentOfFormallyEtale** 是 Mathlib 中的一个定义，位于命名空间 `
Algebra.Extension`。
形式化陈述：tensorH1CotangentOfFormallyEtale [alg : Algebra P.Ring Q.Ring] (halg : alg
ebraMap P.Ring Q.Ring = f.toRingHom) [Module.Flat S T] (H₁ : f.toRingHom.Formall
yEtale) (H₂ : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) : T ot
imes[S] P.H1Cotangent ≃ₗ[T] Q.H1Cotangent
参数：halg : algebraMap P.Ring Q.Ring = f.toRingHom；H₁ : f.toRingHom.FormallyEtale；
H₂ : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def tensorH1CotangentOfFormallyEtale [alg : Algebra P.Ring Q.Ring]
    (halg : algebraMap P.Ring Q.Ring = f.toRingHom) [Module.Flat S T]
    (H₁ : f.toRingHom.FormallyEtale)
    (H₂ : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring)) :
    T ⊗[S] P.H1Cotangent ≃ₗ[T] Q.H1Cotangent := by
  refine .ofBijective ((H1Cotangent.map f).liftBaseChange T) ?_
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Module.Flat.lTensor_preserves_injective_linearMap _ h1Cotangentι_injective
    apply (Extension.tensorCotangent f halg H₂).injective
    simp only [map_zero]
    rw [← h1Cotangentι.map_zero, ← hx]
    change ((Cotangent.map f).liftBaseChange T ∘ₗ h1Cotangentι.baseChange T) x =
      (h1Cotangentι ∘ₗ _) x
    congr 1
    ext x
    simp
  · intro x
    have : Function.Exact (h1Cotangentι.baseChange T) (P.cotangentComplex.baseChange T) :=
      Module.Flat.lTensor_exact T (LinearMap.exact_subtype_ker_map _)
    obtain ⟨a, ha⟩ := (this ((Extension.tensorCotangent f halg H₂).symm x.1)).mp (by
      apply (Extension.tensorCotangentSpaceOfFormallyEtale f H₁).injective
      rw [LinearEquiv.map_zero, ← x.2]
      have : (CotangentSpace.map f).liftBaseChange T ∘ₗ P.cotangentComplex.baseChange T =
          Q.cotangentComplex ∘ₗ (Cotangent.map f).liftBaseChange T := by
        ext x; obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x; dsimp
        simp only [CotangentSpace.map_tmul,
          map_one, Hom.toAlgHom_apply, one_smul, cotangentComplex_mk]
      exact (DFunLike.congr_fun this _).trans (DFunLike.congr_arg Q.cotangentComplex
        ((tensorCotangent f halg H₂).apply_symm_apply x.1)))
    refine ⟨a, Subtype.ext (.trans ?_ ((LinearEquiv.eq_symm_apply _).mp ha))⟩
    change (h1Cotangentι ∘ₗ (H1Cotangent.map f).liftBaseChange T) _ =
      ((Cotangent.map f).liftBaseChange T ∘ₗ h1Cotangentι.baseChange T) _
    congr 1
    ext; dsimp

end Extension

variable {S}

set_option backward.isDefEq.respectTransparency false in
/-- let `p` be a submonoid of an `R`-algebra `S`. Then `Sₚ ⊗ H¹(L_{S/R}) ≃ H¹(L_{Sₚ/R})`. -/
noncomputable
/-
**Algebra.tensorH1CotangentOfIsLocalization** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_1) →   {S : Type u_2} →     (T : Type u_3) →       [inst : Com
mRing R] →         [inst_1 : CommRing S] →           [inst_2 : CommRing T] →    
         [inst_3 : Algebra R S] →               [inst_4 : Algebra R T] →        
         [inst_5 : Algebra S T] →                   [IsScalarTower R S T] →     
                (M : Submonoid S) →                       [IsLocalization M T] →
 TensorProduct S T (Algebra.H1Cotangent R S) ≃ₗ[T] Algebra.H1Cotangent R T
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def tensorH1CotangentOfIsLocalization (M : Submonoid S) [IsLocalization M T] :
    T ⊗[S] H1Cotangent R S ≃ₗ[T] H1Cotangent R T := by
  letI P : Extension R S := (Generators.self R S).toExtension
  letI M' := M.comap (algebraMap P.Ring S)
  letI fQ : Localization M' →ₐ[R] T := IsLocalization.liftAlgHom (M := M')
    (f := (IsScalarTower.toAlgHom R S T).comp (IsScalarTower.toAlgHom R P.Ring S)) (fun ⟨y, hy⟩ ↦
    by simpa using IsLocalization.map_units T ⟨algebraMap P.Ring S y, hy⟩)
  letI Q : Extension R T := .ofSurjective fQ (by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := P.algebraMap_surjective x
    obtain ⟨s, rfl⟩ := P.algebraMap_surjective s
    refine ⟨IsLocalization.mk' _ x ⟨s, show s ∈ M' from hs⟩, ?_⟩
    simp only [fQ, IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe]
    rw [IsLocalization.lift_mk'_spec]
    simp)
  letI f : P.Hom Q :=
  { toRingHom := algebraMap P.Ring (Localization M')
    toRingHom_algebraMap x := (IsScalarTower.algebraMap_apply R P.Ring (Localization M') _).symm
    algebraMap_toRingHom x := @IsLocalization.lift_eq .. }
  haveI : FormallySmooth R P.Ring := inferInstanceAs (FormallySmooth R (MvPolynomial _ _))
  haveI : FormallySmooth P.Ring (Localization M') := .of_isLocalization M'
  haveI : FormallySmooth R Q.Ring := .comp R P.Ring (Localization M')
  haveI : Module.Flat S T := IsLocalization.flat T M
  letI : Algebra P.Ring Q.Ring := (inferInstance : Algebra P.Ring (Localization M'))
  letI := ((algebraMap S T).comp (algebraMap P.Ring S)).toAlgebra
  letI := fQ.toRingHom.toAlgebra
  haveI : IsScalarTower P.Ring S T := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P.Ring (Localization M') T :=
    .of_algebraMap_eq fun r ↦ (f.algebraMap_toRingHom r).symm
  haveI : IsLocalizedModule M' (IsScalarTower.toAlgHom P.Ring S T).toLinearMap := by
    rw [isLocalizedModule_iff_isLocalization]
    convert! ‹IsLocalization M T› using 1
    exact Submonoid.map_comap_eq_of_surjective P.algebraMap_surjective _
  refine Extension.tensorH1CotangentOfFormallyEtale f rfl ?_ ?_ ≪≫ₗ
      Extension.equivH1CotangentOfFormallySmooth _
  · exact RingHom.formallyEtale_algebraMap.mpr
      (FormallyEtale.of_isLocalization (M := M') (Rₘ := Localization M'))
  · let F : P.ker →ₗ[P.Ring] RingHom.ker fQ := f.mapKer rfl
    refine (isLocalizedModule_iff_isBaseChange M' (Localization M') F).mp ?_
    have : (LinearMap.ker <| Algebra.linearMap P.Ring S).localized' (Localization M') M'
        (Algebra.linearMap P.Ring (Localization M')) = RingHom.ker fQ := by
      rw [LinearMap.localized'_ker_eq_ker_localizedMap (Localization M') M'
        (Algebra.linearMap P.Ring (Localization M'))
        (f' := (IsScalarTower.toAlgHom P.Ring S T).toLinearMap)]
      ext x
      obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M' x
      simp only [LinearMap.mem_ker, LinearMap.extendScalarsOfIsLocalization_apply', RingHom.mem_ker,
        IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe, IsLocalization.lift_mk'_spec,
        RingHom.coe_coe, AlgHom.coe_comp, IsScalarTower.coe_toAlgHom', Function.comp_apply,
        mul_zero, fQ]
      have : IsLocalization.mk' (Localization M') x ⟨s, hs⟩ =
          IsLocalizedModule.mk' (Algebra.linearMap P.Ring (Localization M')) x ⟨s, hs⟩ := by
        rw [IsLocalization.mk'_eq_iff_eq_mul, mul_comm, ← Algebra.smul_def, ← Submonoid.smul_def,
          IsLocalizedModule.mk'_cancel']
        rfl
      simp [this, ← IsScalarTower.algebraMap_apply]
    have : F = ((LinearEquiv.ofEq _ _ this).restrictScalars P.Ring).toLinearMap ∘ₗ
      P.ker.toLocalized' (Localization M') M' (Algebra.linearMap P.Ring (Localization M')) := by
      ext; rfl
    rw [this]
    exact IsLocalizedModule.of_linearEquiv _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.tensorH1CotangentOfIsLocalization_toLinearMap** 是 Mathlib 中的一个定理，位于命名空
间 `Algebra`。
形式化陈述：∀ (R : Type u_1) {S : Type u_2} (T : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] (M : Submonoid S)   [
inst_7 : IsLocalization M T],   ↑(Algebra.tensorH1CotangentOfIsLocalization R T 
M) = LinearMap.liftBaseChange T (Algebra.H1Cotangent.map R R S T)
参数：R : Type u_1；T : Type u_3；M : Submonoid S；Algebra.tensorH1CotangentOfIsLocali
zation R T M；Algebra.H1Cotangent.map R R S T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Algebra.Extension.instIsScalarTowerH1CotangentOfCotangent`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{P : Algebra.Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用引理 `Algebra.Extension.algebraMap_surjective`：algebraMap_surjective : Functio
n.Surjective (algebraMap P.Ring S)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsLocalization.lift_mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] {P : Type u_3} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLocalization.mk'_spec'_mk`：∀ {R : Type u_1} [inst : CommSemiring R] {M
 : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S
] [inst_3 : IsLoc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
（共 43 条，此处仅展示前 30 条）
-/
lemma tensorH1CotangentOfIsLocalization_toLinearMap
    (M : Submonoid S) [IsLocalization M T] :
    (tensorH1CotangentOfIsLocalization R T M).toLinearMap =
      (Algebra.H1Cotangent.map R R S T).liftBaseChange T := by
  ext x : 3
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearMap.liftBaseChange_tmul, one_smul]
  simp only [tensorH1CotangentOfIsLocalization,
    Extension.tensorH1CotangentOfFormallyEtale,
    LinearEquiv.ofBijective_apply, LinearMap.liftBaseChange_tmul, one_smul,
    Extension.equivH1CotangentOfFormallySmooth, LinearEquiv.trans_apply]
  let P : Extension R S := (Generators.self R S).toExtension
  let M' := M.comap (algebraMap P.Ring S)
  let fQ : Localization M' →ₐ[R] T := IsLocalization.liftAlgHom (M := M')
    (f := (IsScalarTower.toAlgHom R S T).comp (IsScalarTower.toAlgHom R P.Ring S)) (fun ⟨y, hy⟩ ↦
    by simpa using IsLocalization.map_units T ⟨algebraMap P.Ring S y, hy⟩)
  let Q : Extension R T := .ofSurjective fQ (by
    intro x
    obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq M x
    obtain ⟨x, rfl⟩ := P.algebraMap_surjective x
    obtain ⟨s, rfl⟩ := P.algebraMap_surjective s
    refine ⟨IsLocalization.mk' _ x ⟨s, show s ∈ M' from hs⟩, ?_⟩
    simp only [fQ, IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe]
    rw [IsLocalization.lift_mk'_spec]
    simp)
  let f : (Generators.self R T).toExtension.Hom Q :=
  { toRingHom := (MvPolynomial.aeval Q.σ).toRingHom
    toRingHom_algebraMap := (MvPolynomial.aeval Q.σ).commutes
    algebraMap_toRingHom := by
      have : (IsScalarTower.toAlgHom R Q.Ring T).comp (MvPolynomial.aeval Q.σ) =
          IsScalarTower.toAlgHom _ (Generators.self R T).toExtension.Ring _ := by
        ext i
        change _ = algebraMap (Generators.self R T).Ring _ (.X i)
        simp
      exact DFunLike.congr_fun this }
  rw [← Extension.H1Cotangent.equivOfFormallySmooth_symm, LinearEquiv.symm_apply_eq,
    @Extension.H1Cotangent.equivOfFormallySmooth_apply (f := f),
    Algebra.H1Cotangent.map, ← (Extension.H1Cotangent.map f).coe_restrictScalars S,
    ← LinearMap.comp_apply, ← Extension.H1Cotangent.map_comp, Extension.H1Cotangent.map_eq]
/-
**Algebra.H1Cotangent.isLocalizedModule** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.H1Cot
angent`。
形式化陈述：∀ (R : Type u_1) {S : Type u_2} (T : Type u_3) [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] [inst_5 : Algebra S T] [inst_6 : IsScalarTower R S T] (M : Submonoid S)   [
IsLocalization M T], IsLocalizedModule M (Algebra.H1Cotangent.map R R S T)
参数：R : Type u_1；T : Type u_3；M : Submonoid S；Algebra.H1Cotangent.map R R S T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.instIsScalarTowerH1CotangentOfCotangent`：∀ {R : Type u
} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] 
{P : Algebra.Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.tensorH1CotangentOfIsLocalization_toLinearMap`：∀ (R : Type u_1) 
{S : Type u_2} (T : Type u_3) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 
: CommRing T]   [inst_3 : Algebra R S] [ins…
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
instance H1Cotangent.isLocalizedModule (M : Submonoid S) [IsLocalization M T] :
    IsLocalizedModule M (Algebra.H1Cotangent.map R R S T) := by
  rw [isLocalizedModule_iff_isBaseChange M T]
  change Function.Bijective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T)
  rw [← tensorH1CotangentOfIsLocalization_toLinearMap R T M]
  exact (tensorH1CotangentOfIsLocalization R T M).bijective

end Algebra

