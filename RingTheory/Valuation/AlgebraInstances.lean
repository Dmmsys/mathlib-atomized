/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Algebra instances

This file contains several `Algebra` and `IsScalarTower` instances related to extensions
of a field with a valuation, as well as their unit balls.

## Main definitions
* `ValuationSubring.algebra` : Given an algebra between two field extensions `L` and `E` of a
  field `K` with a valuation, create an algebra between their two rings of integers.

## Main statements

* `integralClosure_algebraMap_injective` : the unit ball of a field `K` with respect to a
  valuation injects into its integral closure in a field extension `L` of `K`.
-/

@[expose] public section

open Function Valuation
open scoped WithZero

variable {K : Type*} [Field K] (v : Valuation K ℤᵐ⁰) (L : Type*) [Field L] [Algebra K L]

namespace ValuationSubring

-- Shortcut instance with potential performance benefit
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra v.valuationSubring L := inferInstance
/-
**ValuationSubring.algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `ValuationSubr
ing`。
形式化陈述：algebraMap_injective : Injective (algebraMap v.valuationSubring L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `ValuationSubring.instIsFractionRingSubtypeMem`：∀ {K : Type u} [inst : Fi
eld K] (A : ValuationSubring K), IsFractionRing (↥A) K
-/
theorem algebraMap_injective : Injective (algebraMap v.valuationSubring L) :=
  (FaithfulSMul.algebraMap_injective K L).comp (IsFractionRing.injective _ _)
/-
**ValuationSubring.isIntegral_of_mem_ringOfIntegers** 是 Mathlib 中的一个定理，位于命名空间 `V
aluationSubring`。
形式化陈述：isIntegral_of_mem_ringOfIntegers {x : L} (hx : x in integralClosure v.valu
ationSubring L) : IsIntegral v.valuationSubring (⟨x, hx⟩ : integralClosure v.val
uationSubring L)
参数：hx : x in integralClosure v.valuationSubring L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `integralClosure.isIntegral`：integralClosure.isIntegral (x : integralClos
ure R A) : IsIntegral R x
-/
theorem isIntegral_of_mem_ringOfIntegers {x : L} (hx : x ∈ integralClosure v.valuationSubring L) :
    IsIntegral v.valuationSubring (⟨x, hx⟩ : integralClosure v.valuationSubring L) :=
  integralClosure.isIntegral ⟨x, hx⟩
/-
**ValuationSubring.isIntegral_of_mem_ringOfIntegers'** 是 Mathlib 中的一个定理，位于命名空间 `
ValuationSubring`。
形式化陈述：isIntegral_of_mem_ringOfIntegers' {x : integralClosure v.valuationSubring 
L} : IsIntegral v.valuationSubring (x : integralClosure v.valuationSubring L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `ValuationSubring.isIntegral_of_mem_ringOfIntegers`：isIntegral_of_mem_rin
gOfIntegers {x : L} (hx : x in integralClosure v.valuationSubring L) : IsIntegra
l v.valuationSubring (⟨x, hx⟩ : integra…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isIntegral_of_mem_ringOfIntegers' {x : integralClosure v.valuationSubring L} :
    IsIntegral v.valuationSubring (x : integralClosure v.valuationSubring L) := by
  apply isIntegral_of_mem_ringOfIntegers

variable (E : Type _) [Field E] [Algebra K E] [Algebra L E] [IsScalarTower K L E]

-- Shortcut instance with potential performance benefit
/-
**ValuationSubring.** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower v.valuationSubring L E := inferInstance

/-- Given an algebra between two field extensions `L` and `E` of a field `K` with a valuation `v`,
  create an algebra between their two rings of integers. -/
-- TODO: fix the smul field
/-
**ValuationSubring.algebra** 是 Mathlib 中的一个实例，位于命名空间 `ValuationSubring`。
形式化陈述：algebra : Algebra (integralClosure v.valuationSubring L) (integralClosure 
v.valuationSubring E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra :
    Algebra (integralClosure v.valuationSubring L) (integralClosure v.valuationSubring E) :=
  RingHom.toAlgebra
    { toFun := fun k => ⟨algebraMap L E k, IsIntegral.algebraMap k.2⟩
      map_zero' :=
        Subtype.ext <| by simp only [Subalgebra.coe_zero, map_zero]
      map_one' := Subtype.ext <| by simp only [Subalgebra.coe_one, map_one]
      map_add' := fun x y =>
        Subtype.ext <| by simp only [map_add, Subalgebra.coe_add]
      map_mul' := fun x y =>
        Subtype.ext <| by simp only [Subalgebra.coe_mul, map_mul] }

/-- A ring equivalence between the integral closure of the valuation subring of `K` in `L`
  and a ring `R` satisfying `isIntegralClosure R v.valuationSubring L`. -/
/-
**ValuationSubring.equiv** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：{K : Type u_1} →   [inst : Field K] →     (v : Valuation K (WithZero (Mult
iplicative ℤ))) →       (L : Type u_2) →         [inst_1 : Field L] →           
[inst_2 : Algebra K L] →             (R : Type u_3) →               [inst_3 : Co
mmRing R] →                 [inst_4 : Algebra (↥v.valuationSubring) R] →        
           [inst_5 : Algebra R L] →                     [IsScalarTower (↥v.valua
tionSubring) R L] →                       [IsIntegralClosure R (↥v.valuationSubr
ing) L] → ↥(integralClosure (↥v.valuationSubring) L) ≃+* R
参数：v : Valuation K (WithZero (Multiplicative ℤ))；L : Type u_2；R : Type u_3；↥v.va
luationSubring；↥v.valuationSubring；↥v.valuationSubring；integralClosure (↥v.valua
tionSubring) L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring equivalence between the integral closure of the valuation subring of `K` 
in `L`
  and a ring `R` satisfying `isIntegralClosure R v.valuationSubring L`.
-/
protected noncomputable def equiv (R : Type*) [CommRing R] [Algebra v.valuationSubring R]
    [Algebra R L] [IsScalarTower v.valuationSubring R L]
    [IsIntegralClosure R v.valuationSubring L] : integralClosure v.valuationSubring L ≃+* R :=
  (IsIntegralClosure.equiv v.valuationSubring R L
    (integralClosure v.valuationSubring L)).symm.toRingEquiv
/-
**ValuationSubring.integralClosure_algebraMap_injective** 是 Mathlib 中的一个定理，位于命名空
间 `ValuationSubring`。
形式化陈述：integralClosure_algebraMap_injective : Injective (algebraMap v.valuationSu
bring (integralClosure v.valuationSubring L))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `ValuationSubring.instIsDomainSubtypeMem`：∀ {K : Type u} [inst : Field K]
 (A : ValuationSubring K), IsDomain ↥A
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `ValuationSubring.instSubringClass`：∀ {K : Type u} [inst : Field K], Subr
ingClass (ValuationSubring K) K
· 使用定理 `Subsemiring.instFaithfulSMulSubtypeMem`：∀ {M' : Type u_5} {α : Type u_6}
 [inst : SMul M' α] {S' : Type u_7} [inst_1 : SetLike S' M'] (s : S')   [Faithfu
lSMul M' α], FaithfulSMul (↥…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
theorem integralClosure_algebraMap_injective :
    Injective (algebraMap v.valuationSubring (integralClosure v.valuationSubring L)) :=
  FaithfulSMul.algebraMap_injective ..

end ValuationSubring

