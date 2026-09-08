/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# Disjoint extensions with coprime different ideals

Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are linearly disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes the different ideal
and `Frac R` denotes the fraction field of a domain `R`.

## Main results and definitions

* `IsDedekindDomain.differentIdeal_eq_map_differentIdeal`: `𝓓(B/R₁) = 𝓓(R₂/A)`
* `IsDedekindDomain.differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime`:
  `𝓓(B/A) = 𝓓(R₁/A) * 𝓓(R₂/A)`.
* `Module.Basis.ofIsCoprimeDifferentIdeal`: Construct a `R₁`-basis of `B` by lifting an
  `A`-basis of `R₂`.
* `IsDedekindDomain.range_sup_range_eq_top_of_isCoprime_differentIdeal`: `B` is generated
  (as an `A`-algebra) by `R₁` and `R₂`.

-/

@[expose] public section

open FractionalIdeal nonZeroDivisors IntermediateField Algebra Module Submodule

variable (A B : Type*) {K L : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing B] [Field L] [Algebra B L] [Algebra A L] [Algebra K L] [FiniteDimensional K L]
  [IsScalarTower A K L]
variable (R₁ R₂ : Type*) [CommRing R₁] [CommRing R₂] [IsDomain R₁] [Algebra A R₁] [Algebra A R₂]
  [Algebra R₁ B] [Algebra R₂ B] [Algebra R₁ L] [Algebra R₂ L]
  [IsScalarTower A R₁ L] [IsScalarTower R₁ B L] [IsScalarTower R₂ B L] [Module.Finite A R₂]
variable {F₁ F₂ : IntermediateField K L} [Algebra R₁ F₁] [Algebra R₂ F₂] [IsTorsionFree R₁ F₁]
  [IsScalarTower A F₂ L] [IsScalarTower A R₂ F₂] [IsScalarTower R₁ F₁ L] [IsScalarTower R₂ F₂ L]
  [Algebra.IsSeparable K F₂] [Algebra.IsSeparable F₁ L]

/-
**Submodule.traceDual_le_span_map_traceDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.traceDual_le_span_map_traceDual [Module.Free A R₂] [IsLocalizati
on (Algebra.algebraMapSubmonoid R₂ A⁰) F₂] (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ 
⊔ F₂ = ⊤) : (traceDual R₁ F₁ (1 : Submodule B L)).restrictScalars R₁ <= span R₁ 
(algebraMap F₂ L '' (traceDual A K (1 : Submodule R₂ F₂)))
参数：Algebra.algebraMapSubmonoid R₂ A⁰；h₁ : F₁.LinearDisjoint F₂；h₂ : F₁ ⊔ F₂ = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IntermediateField.sup_toSubalgebra_of_isAlgebraic_right`：sup_toSubalgebr
a_of_isAlgebraic_right [Algebra.IsAlgebraic K E2] : (E1 ⊔ E2).toSubalgebra = E1.
toSubalgebra ⊔ E2.toSubalgebra
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Basis.mem_span_iff_repr_mem`：∀ {ι : Type u_1} (R : Type u_3) {M :
 Type u_5} {S : Type u_7} [inst : CommRing R] [IsDomain R] [inst_2 : Ring S]   [
Nontrivial S] [inst_4 : …
· 使用定理 `Module.Basis.traceDual_repr_apply`：Module.Basis.traceDual_repr_apply (x 
: L) (i : ι) : (b.traceDual).repr x i = (traceForm K L x) (b i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Submodule.mem_traceDual`：mem_traceDual {I : Submodule B L} {x} : x in Iᵛ
 ↔ forall a in I, traceForm K L x a in (algebraMap A K).range
· 使用定理 `IntermediateField.LinearDisjoint.basisOfBasisRight_apply`：basisOfBasisRi
ght_apply (H : A.LinearDisjoint B) (H' : A.toSubalgebra ⊔ B.toSubalgebra = ⊤) {ι
 : Type*} (b : Basis ι F B) (i : ι) : H.basisO…
· 使用定理 `Module.Basis.localizationLocalization_apply`：localizationLocalization_ap
ply {ι : Type*} (b : Basis ι R A) (i) : b.localizationLocalization Rₛ S Aₛ i = a
lgebraMap A Aₛ (b i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Submodule.mem_one`：mem_one {x : A} : x in (1 : Submodule R A) ↔ exists y
, algebraMap R A y = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.traceDual_eq_iff`：Module.Basis.traceDual_eq_iff {v : ι -> L
} : b.traceDual = v ↔ forall i j, traceForm K L (v i) (b j) = if j = i then 1 el
se 0
· 使用定理 `Algebra.traceForm_apply`：traceForm_apply (x y : S) : traceForm R S x y =
 trace R S (x * y)
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `IsScalarTower.coe_toAlgHom'`：coe_toAlgHom' : (toAlgHom R S A : S -> A) =
 algebraMap S A
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IntermediateField.LinearDisjoint.trace_algebraMap`：trace_algebraMap [Fin
iteDimensional F E] (h₁ : A.LinearDisjoint B) (h₂ : A ⊔ B = ⊤) (x : B) : Algebra
.trace A E (algebraMap B E x) = algebra…
· 使用定理 `Module.Basis.trace_traceDual_mul`：Module.Basis.trace_traceDual_mul (i j 
: ι) : trace K L ((b.traceDual i) * (b j)) = if j = i then 1 else 0
· 使用定理 `MonoidWithZeroHom.map_ite_one_zero`：map_ite_one_zero {F : Type*} [FunLik
e F α β] [MonoidWithZeroHomClass F α β] (f : F) (p : Prop) [Decidable p] : f (it
e p 1 0) = ite p 1 0
（共 44 条，此处仅展示前 30 条）
-/
theorem Submodule.traceDual_le_span_map_traceDual [Module.Free A R₂]
    [IsLocalization (Algebra.algebraMapSubmonoid R₂ A⁰) F₂] (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁ ⊔ F₂ = ⊤) :
    (traceDual R₁ F₁ (1 : Submodule B L)).restrictScalars R₁ ≤
      span R₁ (algebraMap F₂ L '' (traceDual A K (1 : Submodule R₂ F₂))) := by
  intro x hx
  have h₂' : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤ := by
    simpa [sup_toSubalgebra_of_isAlgebraic_right] using congr_arg IntermediateField.toSubalgebra h₂
  let b₂ := (Free.chooseBasis A R₂).localizationLocalization K A⁰ F₂
  let B₁ := h₁.basisOfBasisRight h₂' b₂
  have h_main : x ∈ span R₁ (Set.range B₁.traceDual) := by
    rw [B₁.traceDual.mem_span_iff_repr_mem R₁ x]
    intro i
    rw [B₁.traceDual_repr_apply]
    refine mem_traceDual.mp hx _ ?_
    rw [LinearDisjoint.basisOfBasisRight_apply, Basis.localizationLocalization_apply,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₂ B L, mem_one]
    exact ⟨_, rfl⟩
  have h : Set.range B₁.traceDual =
      Set.range (IsScalarTower.toAlgHom A F₂ L ∘ b₂.traceDual) := by
    refine congr_arg Set.range <| B₁.traceDual_eq_iff.mpr fun i j ↦ ?_
    rw [LinearDisjoint.basisOfBasisRight_apply, traceForm_apply, Function.comp_apply,
      IsScalarTower.coe_toAlgHom', ← map_mul, h₁.trace_algebraMap h₂, b₂.trace_traceDual_mul,
      MonoidWithZeroHom.map_ite_one_zero]
  rwa [← span_span_of_tower A R₁, h, Set.range_comp, ← AlgHom.coe_toLinearMap, ← map_span,
    ← traceDual_span_of_basis A (1 : Submodule R₂ F₂) b₂
      (by rw [Basis.localizationLocalization_span K A⁰ F₂]; ext; simp)] at h_main

attribute [local instance] FractionRing.liftAlgebra

variable [IsDomain A] [IsDedekindDomain B] [IsDedekindDomain R₁] [IsDedekindDomain R₂]
    [IsFractionRing B L] [IsFractionRing R₁ F₁] [IsFractionRing R₂ F₂] [IsIntegrallyClosed A]
    [IsIntegralClosure B R₁ L] [IsTorsionFree R₁ B] [IsTorsionFree R₂ B]

set_option linter.overlappingInstances false

namespace IsDedekindDomain

/-
**IsDedekindDomain.differentIdeal_dvd_map_differentIdeal** 是 Mathlib 中的一个定理，位于命名
空间 `IsDedekindDomain`。
形式化陈述：differentIdeal_dvd_map_differentIdeal [Algebra.IsIntegral R₂ B] [Module.Fr
ee A R₂] [IsLocalization (Algebra.algebraMapSubmonoid R₂ A⁰) F₂] (h₁ : F₁.Linear
Disjoint F₂) (h₂ : F₁ ⊔ F₂ = ⊤) : differentIdeal R₁ B ∣ Ideal.map (algebraMap R₂
 B) (differentIdeal A R₂)
参数：Algebra.algebraMapSubmonoid R₂ A⁰；h₁ : F₁.LinearDisjoint F₂；h₂ : F₁ ⊔ F₂ = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用引理 `Algebra.IsSeparable.of_equiv_equiv`：Algebra.IsSeparable.of_equiv_equiv [
Algebra.IsSeparable A₁ B₁] : Algebra.IsSeparable A₂ B₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractionRing.algEquiv_commutes`：algEquiv_commutes (e : K₁ ≃ₐ[A] K₂) (f
 : L₁ ≃ₐ[B] L₂) (x : K₁) : algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x)
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coeIdeal_le_coeIdeal`：coeIdeal_le_coeIdeal (K : Type*) [
CommRing K] [Algebra R K] [IsFractionRing R K] {I J : Ideal R} : (I : Fractional
Ideal R⁰ K) <= J ↔ I <= J
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `coeIdeal_differentIdeal`：coeIdeal_differentIdeal : ↑(differentIdeal A B)
 = (FractionalIdeal.dual A K (1 : FractionalIdeal B⁰ L))⁻¹
· 使用定理 `FractionalIdeal.extendedHom_coeIdeal_eq_map`：extendedHom_coeIdeal_eq_map
 (I : Ideal A) : (I : FractionalIdeal A⁰ K).extendedHom L B = (I.map (algebraMap
 A B) : FractionalIdeal B⁰ L)
· 使用引理 `FractionalIdeal.le_inv_comm`：le_inv_comm {I J : FractionalIdeal A⁰ K} (h
I : I != 0) (hJ : J != 0) : I <= J⁻¹ ↔ J <= I⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `FractionalIdeal.instNontrivialNonZeroDivisors`：∀ {R₁ : Type u_3} [inst :
 CommRing R₁] {K : Type u_4} [inst_1 : Field K] [inst_2 : Algebra R₁ K],   Nontr
ivial (FractionalIdeal (nonZeroDivi…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `FractionalIdeal.coeIdeal_eq_zero`：coeIdeal_eq_zero {I : Ideal R} : (I : 
FractionalIdeal R⁰ K) = 0 ↔ I = ⊥
（共 46 条，此处仅展示前 30 条）
-/
theorem differentIdeal_dvd_map_differentIdeal [Algebra.IsIntegral R₂ B]
    [Module.Free A R₂] [IsLocalization (Algebra.algebraMapSubmonoid R₂ A⁰) F₂]
    (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂ = ⊤) :
    differentIdeal R₁ B ∣ Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) := by
  have : Algebra.IsSeparable (FractionRing A) (FractionRing R₂) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
          (FractionRing.algEquiv R₂ F₂).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K).symm
      (FractionRing.algEquiv R₂ ↥F₂).symm _
  rw [Ideal.dvd_iff_le, ← coeIdeal_le_coeIdeal L, coeIdeal_differentIdeal R₁ F₁ L B,
    ← extendedHom_coeIdeal_eq_map L B (K := F₂), le_inv_comm _ (by simp), ← map_inv₀,
    coeIdeal_differentIdeal A K, inv_inv, ← coe_le_coe, coe_dual_one, coe_extendedHom_eq_span,
    ← coeToSet_coeToSubmodule, coe_dual_one]
  · have := Submodule.span_mono (R := B) <| traceDual_le_span_map_traceDual A B R₁ R₂ h₁ h₂
    rwa [← span_coe_eq_restrictScalars, span_span_of_tower, span_span_of_tower, span_eq] at this
  · exact (_root_.map_ne_zero _).mpr <| coeIdeal_eq_zero.not.mpr differentIdeal_ne_bot

variable [Algebra A B] [Module.Finite A B] [IsTorsionFree A B] [IsTorsionFree A R₁]
  [IsTorsionFree A R₂] [Module.Finite A R₁] [Module.Finite R₂ B] [IsScalarTower A R₂ B]
  [Module.Finite R₁ B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [IsScalarTower A R₁ B]
/-
**IsDedekindDomain.map_differentIdeal_dvd_differentIdeal** 是 Mathlib 中的一个定理，位于命名
空间 `IsDedekindDomain`。
形式化陈述：map_differentIdeal_dvd_differentIdeal (h : IsCoprime ((differentIdeal A R₁
).map (algebraMap R₁ B)) ((differentIdeal A R₂).map (algebraMap R₂ B))) : Ideal.
map (algebraMap R₂ B) (differentIdeal A R₂) ∣ differentIdeal R₁ B
参数：h : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B)) ((differentIdeal 
A R₂).map (algebraMap R₂ B))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `differentIdeal_eq_differentIdeal_mul_differentIdeal`：differentIdeal_eq_d
ifferentIdeal_mul_differentIdeal (C : Type*) [IsDomain B] [CommRing C] [Algebra 
B C] [Algebra A C] [IsDedekindDomain C] […
· 使用定理 `IsCoprime.dvd_of_dvd_mul_right`：IsCoprime.dvd_of_dvd_mul_right (H1 : IsC
oprime x z) (H2 : x ∣ y * z) : x ∣ y
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `dvd_of_mul_left_eq`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α} 
(c : α), c * a = b → a ∣ b
-/
theorem map_differentIdeal_dvd_differentIdeal
    (h : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) ∣ differentIdeal R₁ B :=
  have := (differentIdeal_eq_differentIdeal_mul_differentIdeal A R₂ B).symm.trans
    (differentIdeal_eq_differentIdeal_mul_differentIdeal A R₁ B)
  h.symm.dvd_of_dvd_mul_right (dvd_of_mul_left_eq _ this)
/-
**IsDedekindDomain.differentIdeal_eq_map_differentIdeal** 是 Mathlib 中的一个定理，位于命名空
间 `IsDedekindDomain`。
形式化陈述：differentIdeal_eq_map_differentIdeal [Module.Free A R₂] (h₁ : F₁.LinearDis
joint F₂) (h₂ : F₁ ⊔ F₂ = ⊤) (h₃ : IsCoprime ((differentIdeal A R₁).map (algebra
Map R₁ B)) ((differentIdeal A R₂).map (algebraMap R₂ B))) : differentIdeal R₁ B 
= Ideal.map (algebraMap R₂ B) (differentIdeal A R₂)
参数：h₁ : F₁.LinearDisjoint F₂；h₂ : F₁ ⊔ F₂ = ⊤；h₃ : IsCoprime ((differentIdeal A 
R₁).map (algebraMap R₁ B)) ((differentIdeal A R₂).map (algebraMap R₂ B))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IsDedekindDomain.differentIdeal_dvd_map_differentIdeal`：differentIdeal_d
vd_map_differentIdeal [Algebra.IsIntegral R₂ B] [Module.Free A R₂] [IsLocalizati
on (Algebra.algebraMapSubmonoid R₂ A⁰) F₂] (…
· 使用定理 `Algebra.IsAlgebraic.instIsLocalizationAlgebraMapSubmonoidNonZeroDivisors
`：∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] (S' : Type u_5)   [inst_3 : CommRing S'] [F…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.map_differentIdeal_dvd_differentIdeal`：map_differentIde
al_dvd_differentIdeal (h : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B
)) ((differentIdeal A R₂).map (algebraMap R₂…
-/
theorem differentIdeal_eq_map_differentIdeal [Module.Free A R₂] (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁ ⊔ F₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    differentIdeal R₁ B = Ideal.map (algebraMap R₂ B) (differentIdeal A R₂) := by
  apply dvd_antisymm
  · exact differentIdeal_dvd_map_differentIdeal A B R₁ R₂ h₁ h₂
  · exact map_differentIdeal_dvd_differentIdeal A B R₁ R₂ h₃

/--
Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are linearly disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes the different ideal
and `Frac R` denotes the fraction field of a domain `R`.
We have `𝓓(B/A) = 𝓓(R₁/A) * 𝓓(R₂/A)`.
-/
/-
**IsDedekindDomain.differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCopr
ime** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain`。
形式化陈述：differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime [Module.F
ree A R₂] (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂ = ⊤) (h₃ : IsCoprime ((diffe
rentIdeal A R₁).map (algebraMap R₁ B)) ((differentIdeal A R₂).map (algebraMap R₂
 B))) : differentIdeal A B = differentIdeal R₁ B * differentIdeal R₂ B
参数：h₁ : F₁.LinearDisjoint F₂；h₂ : F₁ ⊔ F₂ = ⊤；h₃ : IsCoprime ((differentIdeal A 
R₁).map (algebraMap R₁ B)) ((differentIdeal A R₂).map (algebraMap R₂ B))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `differentIdeal_eq_differentIdeal_mul_differentIdeal`：differentIdeal_eq_d
ifferentIdeal_mul_differentIdeal (C : Type*) [IsDomain B] [CommRing C] [Algebra 
B C] [Algebra A C] [IsDedekindDomain C] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.differentIdeal_eq_map_differentIdeal`：differentIdeal_eq
_map_differentIdeal [Module.Free A R₂] (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂
 = ⊤) (h₃ : IsCoprime ((differentIdeal A R₁…

--- 原说明 ---
Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R
₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are lin
early disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes th
e different ideal
and `Frac R` denotes the fraction field of a domain `R`.
We have `𝓓(B/A) = 𝓓(R₁/A) * 𝓓(R₂/A)`.
-/
theorem differentIdeal_eq_differentIdeal_mul_differentIdeal_of_isCoprime
    [Module.Free A R₂] (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂ = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    differentIdeal A B = differentIdeal R₁ B * differentIdeal R₂ B := by
  have := differentIdeal_eq_differentIdeal_mul_differentIdeal A R₂ B
  rwa [← differentIdeal_eq_map_differentIdeal A B R₁ R₂ h₁ h₂ h₃,
    mul_comm] at this

end IsDedekindDomain

variable [Algebra A B] [Module.Finite A B] [IsTorsionFree A B] [IsTorsionFree A R₁]
  [IsTorsionFree A R₂] [Module.Finite A R₁] [Module.Finite R₂ B] [IsScalarTower A R₂ B]
  [Module.Finite R₁ B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [IsScalarTower A R₁ B]

/-
**Submodule.traceDual_eq_span_map_traceDual_of_linearDisjoint** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：Submodule.traceDual_eq_span_map_traceDual_of_linearDisjoint [Module.Free A
 R₂] [IsLocalization (Algebra.algebraMapSubmonoid R₂ A⁰) F₂] (h₁ : F₁.LinearDisj
oint F₂) (h₂ : F₁ ⊔ F₂ = ⊤) (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraM
ap R₁ B)) ((differentIdeal A R₂).map (algebraMap R₂ B))) : span R₁ (algebraMap F
₂ L '' (traceDual A K (1 : Submodule R₂ F₂))) = (traceDual R₁ F₁ (1 : Submodule 
B L)).restrictScalars R₁
参数：Algebra.algebraMapSubmonoid R₂ A⁰；h₁ : F₁.LinearDisjoint F₂；h₂ : F₁ ⊔ F₂ = ⊤；
h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B)) ((differentIdeal A 
R₂).map (algebraMap R₂ B))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用引理 `Algebra.IsSeparable.of_equiv_equiv`：Algebra.IsSeparable.of_equiv_equiv [
Algebra.IsSeparable A₁ B₁] : Algebra.IsSeparable A₂ B₂
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `IsFractionRing.algEquiv_commutes`：algEquiv_commutes (e : K₁ ≃ₐ[A] K₂) (f
 : L₁ ≃ₐ[B] L₂) (x : K₁) : algebraMap K₂ L₂ (e x) = f (algebraMap K₁ L₁ x)
· 使用定理 `FractionRing.instIsScalarTower`：∀ (R : Type u_1) [inst : CommRing R] (K 
: Type u_5) [inst_1 : Field K] [inst_2 : Algebra R K]   [inst_3 : FaithfulSMul R
 K] {R₀ : Type u_6} …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `dvd_of_eq`：dvd_of_eq (h : a = b) : a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.differentIdeal_eq_map_differentIdeal`：differentIdeal_eq
_map_differentIdeal [Module.Free A R₂] (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁ ⊔ F₂
 = ⊤) (h₃ : IsCoprime ((differentIdeal A R₁…
· 使用定理 `IsIntegralClosure.of_isIntegrallyClosed`：∀ (R : Type u_1) (S : Type u_2)
 [inst : CommRing R] [inst_1 : CommRing S] (K : Type u_3) [inst_2 : CommRing K] 
  [inst_3 : Algebra R K] [ifr…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.coe_dual_one`：coe_dual_one : (dual A K (1 : FractionalId
eal B⁰ L) : Submodule B L) = 1ᵛ
· 使用定理 `FractionalIdeal.coeToSet_coeToSubmodule`：coeToSet_coeToSubmodule (I : Fr
actionalIdeal S P) : ((I : Submodule R P) : Set P) = I
· 使用定理 `FractionalIdeal.coe_extendedHom_eq_span`：coe_extendedHom_eq_span (I : Fr
actionalIdeal A⁰ K) : extendedHom L B I = span B (algebraMap K L '' I)
· 使用定理 `FractionalIdeal.coe_le_coe`：coe_le_coe {I J : FractionalIdeal S P} : (I 
: Submodule R P) <= (J : Submodule R P) ↔ I <= J
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
（共 51 条，此处仅展示前 30 条）
-/
theorem Submodule.traceDual_eq_span_map_traceDual_of_linearDisjoint [Module.Free A R₂]
    [IsLocalization (Algebra.algebraMapSubmonoid R₂ A⁰) F₂] (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁ ⊔ F₂ = ⊤) (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) :
    span R₁ (algebraMap F₂ L '' (traceDual A K (1 : Submodule R₂ F₂))) =
      (traceDual R₁ F₁ (1 : Submodule B L)).restrictScalars R₁ := by
  have : Algebra.IsSeparable (FractionRing A) (FractionRing R₂) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
          (FractionRing.algEquiv R₂ F₂).symm.toRingEquiv ?_
    ext x
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv A K).symm
      (FractionRing.algEquiv R₂ ↥F₂).symm _
  suffices span B (algebraMap F₂ L '' (traceDual A K (1 : Submodule R₂ F₂))) ≤
      traceDual R₁ F₁ (1 : Submodule B L) by
    apply le_antisymm
    · refine SetLike.coe_subset_coe.mp (subset_trans ?_ this)
      rw [← Submodule.span_span_of_tower R₁ B]
      exact Submodule.subset_span
    · exact traceDual_le_span_map_traceDual A B R₁ R₂ h₁ h₂
  have := dvd_of_eq <|
    (IsDedekindDomain.differentIdeal_eq_map_differentIdeal A B R₁ R₂ h₁ h₂ h₃).symm
  rwa [Ideal.dvd_iff_le, ← coeIdeal_le_coeIdeal (K := L), coeIdeal_differentIdeal R₁ F₁,
    inv_le_comm, ← extendedHom_coeIdeal_eq_map (K := F₂), coeIdeal_differentIdeal A K, map_inv₀,
    inv_inv, ← coe_le_coe, coe_extendedHom_eq_span, coe_dual_one, ← coeToSet_coeToSubmodule,
    coe_dual_one] at this
  · simp
  · rw [← extendedHom_coeIdeal_eq_map (K := F₂), ne_eq, extendedHom_eq_zero_iff]
    rw [coeIdeal_eq_zero]
    exact differentIdeal_ne_bot

namespace Module.Basis

/-
**Module.Basis.ofIsCoprimeDifferentIdeal_aux** 是 Mathlib 中的一个定理，位于命名空间 `Module.B
asis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ofIsCoprimeDifferentIdeal_aux [Module.Free A R₂]
    (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) {ι : Type*} (b : Basis ι K F₂)
    (hb : span A (Set.range b) = LinearMap.range (IsScalarTower.toAlgHom A R₂ F₂ : R₂ →ₗ[A] F₂)) :
    span R₁ (Set.range (h₁.basisOfBasisRight h₂ b)) =
      Submodule.restrictScalars R₁ (1 : Submodule B L) := by
  classical
  have h₂' : F₁ ⊔ F₂ = ⊤ := by
    rwa [← sup_toSubalgebra_of_isAlgebraic_right, ← top_toSubalgebra, toSubalgebra_inj] at h₂
  have : Finite ι := Module.Finite.finite_basis b
  have h_main := congr_arg (Submodule.restrictScalars R₁) <|
    congr_arg coeToSubmodule <| (1 : FractionalIdeal B⁰ L).dual_dual R₁ F₁
  rw [← coe_one, ← h_main, coe_dual _ _ (by simp), coe_dual_one, restrictScalars_traceDual,
    ← traceDual_eq_span_map_traceDual_of_linearDisjoint A B R₁ R₂ h₁ h₂' h₃,
    ← coe_restrictScalars A, traceDual_span_of_basis A (1 : Submodule R₂ F₂) b,
    ← IsScalarTower.coe_toAlgHom' A F₂ L, ← AlgHom.coe_toLinearMap, ← map_coe, map_span,
    span_span_of_tower, AlgHom.coe_toLinearMap, IsScalarTower.coe_toAlgHom', ← Set.range_comp]
  · have : (h₁.basisOfBasisRight h₂ b).traceDual = algebraMap F₂ L ∘ b.traceDual := by
      refine Basis.traceDual_eq_iff.mpr fun i j ↦ ?_
      rw [Function.comp_apply, h₁.basisOfBasisRight_apply, traceForm_apply, ← map_mul,
        h₁.trace_algebraMap h₂', b.trace_traceDual_mul i j, MonoidWithZeroHom.map_ite_one_zero]
    rw [← this, (traceForm F₁ L).dualSubmodule_span_of_basis (traceForm_nondegenerate F₁ L),
      ← Basis.traceDual_def, Basis.traceDual_traceDual]
  · rw [hb]
    ext; simp

/--
Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are linearly disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes the different ideal
and `Frac R` denotes the fraction field of a domain `R`.
Construct a `R₁`-basis of `B` by lifting an `A`-basis of `R₂`.
-/
/-
**Module.Basis.ofIsCoprimeDifferentIdeal** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis
`。
形式化陈述：ofIsCoprimeDifferentIdeal (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁.toSubalgebr
a ⊔ F₂.toSubalgebra = ⊤) (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap 
R₁ B)) ((differentIdeal A R₂).map (algebraMap R₂ B))) {ι : Type*} (b : Basis ι A
 R₂) : Basis ι R₁ B
参数：h₁ : F₁.LinearDisjoint F₂；h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤；h₃ : IsC
oprime ((differentIdeal A R₁).map (algebraMap R₁ B)) ((differentIdeal A R₂).map 
(algebraMap R₂ B))；b : Basis ι A R₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A

--- 原说明 ---
Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R
₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are lin
early disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes th
e different ideal
and `Frac R` denotes the fraction field of a domain `R`.
Construct a `R₁`-basis of `B` by lifting an `A`-basis of `R₂`.
-/
noncomputable def ofIsCoprimeDifferentIdeal (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) {ι : Type*} (b : Basis ι A R₂) :
    Basis ι R₁ B :=
  have : Module.Free A R₂ := Free.of_basis b
  let v := fun i : ι ↦ algebraMap R₂ B (b i)
  let b₂ : Basis ι K F₂ := b.localizationLocalization K A⁰ F₂
  have P₁ : LinearIndependent R₁ v := by
    rw [← LinearMap.linearIndependent_iff (IsScalarTower.toAlgHom R₁ B L).toLinearMap
      (LinearMap.ker_eq_bot.mpr <| FaithfulSMul.algebraMap_injective _ _),
      LinearIndependent.iff_fractionRing R₁ F₁, Function.comp_def]
    simp_rw [AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom', v,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R₂ F₂ L,
      ← b.localizationLocalization_apply K A⁰ F₂]
    exact h₁.linearIndependent_right b₂.linearIndependent
  have P₂ : ⊤ ≤ span R₁ (Set.range v) := by
    rw [top_le_iff]
    apply map_injective_of_injective (f := (IsScalarTower.toAlgHom R₁ B L).toLinearMap)
      (FaithfulSMul.algebraMap_injective B L)
    rw [map_span, ← Set.range_comp]
    convert!
      Module.Basis.ofIsCoprimeDifferentIdeal_aux A B R₁ R₂ h₁ h₂ h₃ b₂
        (b.localizationLocalization_span K A⁰ F₂)
    · ext
      simp [b₂, v, ← IsScalarTower.algebraMap_apply]
    · ext; simp
  Basis.mk P₁ P₂

@[simp]
/-
**Module.Basis.ofIsCoprimeDifferentIdeal_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module
.Basis`。
形式化陈述：ofIsCoprimeDifferentIdeal_apply (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁.toSub
algebra ⊔ F₂.toSubalgebra = ⊤) (h₃ : IsCoprime ((differentIdeal A R₁).map (algeb
raMap R₁ B)) ((differentIdeal A R₂).map (algebraMap R₂ B))) {ι : Type*} (b : Bas
is ι A R₂) (i : ι) : b.ofIsCoprimeDifferentIdeal A B R₁ R₂ h₁ h₂ h₃ i = algebraM
ap R₂ B (b i)
参数：h₁ : F₁.LinearDisjoint F₂；h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤；h₃ : IsC
oprime ((differentIdeal A R₁).map (algebraMap R₁ B)) ((differentIdeal A R₂).map 
(algebraMap R₂ B))；b : Basis ι A R₂；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofIsCoprimeDifferentIdeal_apply (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) {ι : Type*} (b : Basis ι A R₂) (i : ι) :
    b.ofIsCoprimeDifferentIdeal A B R₁ R₂ h₁ h₂ h₃ i = algebraMap R₂ B (b i) := by
  simp [Module.Basis.ofIsCoprimeDifferentIdeal]

end Module.Basis

namespace IsDedekindDomain

/--
Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are linearly disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes the different ideal
and `Frac R` denotes the fraction field of a domain `R`.
Then `B` is generated (as an `A`-algebra) by `R₁` and `R₂`.
-/
/-
**IsDedekindDomain.range_sup_range_eq_top_of_isCoprime_differentIdeal** 是 Mathli
b 中的一个定理，位于命名空间 `IsDedekindDomain`。
形式化陈述：range_sup_range_eq_top_of_isCoprime_differentIdeal (h₁ : F₁.LinearDisjoint
 F₂) (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤) (h₃ : IsCoprime ((differentIde
al A R₁).map (algebraMap R₁ B)) ((differentIdeal A R₂).map (algebraMap R₂ B))) [
Module.Free A R₂] : (IsScalarTower.toAlgHom A R₁ B).range ⊔ (IsScalarTower.toAlg
Hom A R₂ B).range = ⊤
参数：h₁ : F₁.LinearDisjoint F₂；h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤；h₃ : IsC
oprime ((differentIdeal A R₁).map (algebraMap R₁ B)) ((differentIdeal A R₂).map 
(algebraMap R₂ B))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.eq_top_iff`：eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ forall x :
 A, x in S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `Subalgebra.sum_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {ι : Type w}
 {t : Fi…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Algebra.mem_sup_left`：mem_sup_left {S T : Subalgebra R A} : forall {x : 
A}, x in S -> x in S ⊔ T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.mem_sup_right`：mem_sup_right {S T : Subalgebra R A} : forall {x 
: A}, x in T -> x in S ⊔ T
· 使用定理 `Module.Basis.ofIsCoprimeDifferentIdeal_apply`：ofIsCoprimeDifferentIdeal_
apply (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤) (
h₃ : IsCoprime ((differentIdeal A …

--- 原说明 ---
Let `A ⊆ B` be a finite extension of Dedekind domains and assume that `A ⊆ R₁, R
₂ ⊆ B` are two
subrings such that `Frac R₁ ⊔ Frac R₂ = Frac B`, `Frac R₁` and `Frac R₂` are lin
early disjoint
over `Frac A`, and that `𝓓(R₁/A)` and `𝓓(R₂/A)` are coprime where `𝓓` denotes th
e different ideal
and `Frac R` denotes the fraction field of a domain `R`.
Then `B` is generated (as an `A`-algebra) by `R₁` and `R₂`.
-/
theorem range_sup_range_eq_top_of_isCoprime_differentIdeal
    (h₁ : F₁.LinearDisjoint F₂)
    (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) [Module.Free A R₂] :
    (IsScalarTower.toAlgHom A R₁ B).range ⊔
      (IsScalarTower.toAlgHom A R₂ B).range = ⊤ := by
  let B₁ := (Free.chooseBasis A R₂).ofIsCoprimeDifferentIdeal A B R₁ R₂ h₁ h₂ h₃
  refine Algebra.eq_top_iff.mpr fun x ↦ ?_
  rw [← B₁.sum_repr x]
  refine Subalgebra.sum_mem _ fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact Subalgebra.mul_mem _ (Algebra.mem_sup_left (by simp)) (Algebra.mem_sup_right (by simp [B₁]))
/-
**IsDedekindDomain.adjoin_union_eq_top_of_isCoprime_differentialIdeal** 是 Mathli
b 中的一个定理，位于命名空间 `IsDedekindDomain`。
形式化陈述：adjoin_union_eq_top_of_isCoprime_differentialIdeal [Module.Free A R₂] (h₁ 
: F₁.LinearDisjoint F₂) (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤) (h₃ : IsCop
rime ((differentIdeal A R₁).map (algebraMap R₁ B)) ((differentIdeal A R₂).map (a
lgebraMap R₂ B))) {s : Set R₁} {t : Set R₂} (hs : Algebra.adjoin A s = ⊤) (ht : 
Algebra.adjoin A t = ⊤) : Algebra.adjoin A (algebraMap R₁ B '' s union algebraMa
p R₂ B '' t) = ⊤
参数：h₁ : F₁.LinearDisjoint F₂；h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤；h₃ : IsC
oprime ((differentIdeal A R₁).map (algebraMap R₁ B)) ((differentIdeal A R₂).map 
(algebraMap R₂ B))；hs : Algebra.adjoin A s = ⊤；ht : Algebra.adjoin A t = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `FractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (A :
 Type u_4) [inst_1 : CommRing A] [inst_2 : Algebra R A] [FaithfulSMul R A],   Fa
ithfulSMul R (Fract…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_union`：adjoin_union (s t : Set A) : adjoin R (s union t) 
= adjoin R s ⊔ adjoin R t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.coe_toAlgHom'`：coe_toAlgHom' : (toAlgHom R S A : S -> A) =
 algebraMap S A
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `IsDedekindDomain.range_sup_range_eq_top_of_isCoprime_differentIdeal`：ran
ge_sup_range_eq_top_of_isCoprime_differentIdeal (h₁ : F₁.LinearDisjoint F₂) (h₂ 
: F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤) (h₃ : IsCoprime …
-/
theorem adjoin_union_eq_top_of_isCoprime_differentialIdeal [Module.Free A R₂]
    (h₁ : F₁.LinearDisjoint F₂) (h₂ : F₁.toSubalgebra ⊔ F₂.toSubalgebra = ⊤)
    (h₃ : IsCoprime ((differentIdeal A R₁).map (algebraMap R₁ B))
      ((differentIdeal A R₂).map (algebraMap R₂ B))) {s : Set R₁} {t : Set R₂}
    (hs : Algebra.adjoin A s = ⊤) (ht : Algebra.adjoin A t = ⊤) :
    Algebra.adjoin A (algebraMap R₁ B '' s ∪ algebraMap R₂ B '' t) = ⊤ := by
  rw [Algebra.adjoin_union, ← IsScalarTower.coe_toAlgHom' A R₁, ← IsScalarTower.coe_toAlgHom' A R₂,
    ← AlgHom.map_adjoin, hs, ← AlgHom.map_adjoin, ht, Algebra.map_top, Algebra.map_top]
  exact range_sup_range_eq_top_of_isCoprime_differentIdeal A B R₁ R₂ h₁ h₂ h₃

end IsDedekindDomain

