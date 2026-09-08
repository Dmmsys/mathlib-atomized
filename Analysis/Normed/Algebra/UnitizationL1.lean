/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-! # Unitization equipped with the $L^1$ norm

In another file, the `Unitization 𝕜 A` of a non-unital normed `𝕜`-algebra `A` is equipped with the
norm inherited as the pullback via a map (closely related to) the left-regular representation of the
algebra on itself (see `Unitization.instNormedRing`).

However, this construction is only valid (and an isometry) when `A` is a `RegularNormedAlgebra`.
Sometimes it is useful to consider the unitization of a non-unital algebra with the $L^1$ norm
instead. This file provides that norm on the type synonym `WithLp 1 (Unitization 𝕜 A)`, along
with the algebra isomorphism between `Unitization 𝕜 A` and `WithLp 1 (Unitization 𝕜 A)`.
Note that `TrivSqZeroExt` is also equipped with the $L^1$ norm in the analogous way, but it is
registered as an instance without the type synonym.

One application of this is a straightforward proof that the quasispectrum of an element in a
non-unital Banach algebra is compact, which can be established by passing to the unitization.
-/

@[expose] public section

variable (𝕜 A : Type*) [NormedField 𝕜] [NonUnitalNormedRing A]
variable [NormedSpace 𝕜 A]

namespace WithLp

open Unitization

/-- The natural map between `Unitization 𝕜 A` and `𝕜 × A`, transferred to their `WithLp 1`
synonyms. -/
/-
**WithLp.unitization_addEquiv_prod** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：unitization_addEquiv_prod : WithLp 1 (Unitization 𝕜 A) ≃+ WithLp 1 (𝕜 × A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map between `Unitization 𝕜 A` and `𝕜 × A`, transferred to their `Wit
hLp 1`
synonyms.
-/
noncomputable def unitization_addEquiv_prod : WithLp 1 (Unitization 𝕜 A) ≃+ WithLp 1 (𝕜 × A) :=
  (WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).toAddEquiv.trans <|
    (addEquiv 𝕜 A).trans (WithLp.linearEquiv 1 𝕜 (𝕜 × A)).symm.toAddEquiv
/-
**WithLp.instUnitizationNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instUnitizationNormedAddCommGroup : NormedAddCommGroup (WithLp 1 (Unitizat
ion 𝕜 A))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
-/
noncomputable instance instUnitizationNormedAddCommGroup :
    NormedAddCommGroup (WithLp 1 (Unitization 𝕜 A)) :=
  NormedAddCommGroup.induced (WithLp 1 (Unitization 𝕜 A)) (WithLp 1 (𝕜 × A))
    (unitization_addEquiv_prod 𝕜 A) (AddEquiv.injective _)

/-- Bundle `WithLp.unitization_addEquiv_prod` as a `UniformEquiv`. -/
/-
**WithLp.uniformEquiv_unitization_addEquiv_prod** 是 Mathlib 中的一个定义，位于命名空间 `WithL
p`。
形式化陈述：uniformEquiv_unitization_addEquiv_prod : WithLp 1 (Unitization 𝕜 A) ≃ᵤ Wit
hLp 1 (𝕜 × A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `WithLp.unitization_addEquiv_prod` as a `UniformEquiv`.
-/
noncomputable def uniformEquiv_unitization_addEquiv_prod :
    WithLp 1 (Unitization 𝕜 A) ≃ᵤ WithLp 1 (𝕜 × A) :=
  { unitization_addEquiv_prod 𝕜 A with
    uniformContinuous_invFun := uniformContinuous_comap' uniformContinuous_id
    uniformContinuous_toFun := uniformContinuous_iff_le_comap.mpr le_rfl }
/-
**WithLp.instCompleteSpace** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] : CompleteSpace (Wit
hLp 1 (Unitization 𝕜 A))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `completeSpace_congr`：completeSpace_congr {e : α ≃ β} (he : IsUniformEmbe
dding e) : CompleteSpace α ↔ CompleteSpace β
· 使用引理 `UniformEquiv.isUniformEmbedding`：isUniformEmbedding (h : α ≃ᵤ β) : IsUni
formEmbedding h
-/
instance instCompleteSpace [CompleteSpace 𝕜] [CompleteSpace A] :
    CompleteSpace (WithLp 1 (Unitization 𝕜 A)) :=
  completeSpace_congr (uniformEquiv_unitization_addEquiv_prod 𝕜 A).isUniformEmbedding |>.mpr
    inferInstance

variable {𝕜 A}

open ENNReal in
/-
**WithLp.unitization_norm_def** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：unitization_norm_def (x : WithLp 1 (Unitization 𝕜 A)) : ‖x‖ = ‖(ofLp x).fs
t‖ + ‖(ofLp x).snd‖
参数：x : WithLp 1 (Unitization 𝕜 A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithLp.prod_norm_eq_add`：prod_norm_eq_add (hp : 0 < p.toReal) (f : WithL
p p (α × β)) : ‖f‖ = (‖f.fst‖ ^ p.toReal + ‖f.snd‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unitization_norm_def (x : WithLp 1 (Unitization 𝕜 A)) :
    ‖x‖ = ‖(ofLp x).fst‖ + ‖(ofLp x).snd‖ := calc
  ‖x‖ = (‖(ofLp x).fst‖ ^ (1 : ℝ≥0∞).toReal +
      ‖(ofLp x).snd‖ ^ (1 : ℝ≥0∞).toReal) ^ (1 / (1 : ℝ≥0∞).toReal) :=
    prod_norm_eq_add (by simp : 0 < (1 : ℝ≥0∞).toReal) _
  _ = ‖(ofLp x).fst‖ + ‖(ofLp x).snd‖ := by simp
/-
**WithLp.unitization_nnnorm_def** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：unitization_nnnorm_def (x : WithLp 1 (Unitization 𝕜 A)) : ‖x‖₊ = ‖(ofLp x)
.fst‖₊ + ‖(ofLp x).snd‖₊
参数：x : WithLp 1 (Unitization 𝕜 A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `WithLp.unitization_norm_def`：unitization_norm_def (x : WithLp 1 (Unitiza
tion 𝕜 A)) : ‖x‖ = ‖(ofLp x).fst‖ + ‖(ofLp x).snd‖
-/
lemma unitization_nnnorm_def (x : WithLp 1 (Unitization 𝕜 A)) :
    ‖x‖₊ = ‖(ofLp x).fst‖₊ + ‖(ofLp x).snd‖₊ :=
  Subtype.ext <| unitization_norm_def x
/-
**WithLp.unitization_norm_inr** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：unitization_norm_inr (x : A) : ‖toLp 1 (x : Unitization 𝕜 A)‖ = ‖x‖
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithLp.unitization_norm_def`：unitization_norm_def (x : WithLp 1 (Unitiza
tion 𝕜 A)) : ‖x‖ = ‖(ofLp x).fst‖ + ‖(ofLp x).snd‖
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unitization_norm_inr (x : A) : ‖toLp 1 (x : Unitization 𝕜 A)‖ = ‖x‖ := by
  simp [unitization_norm_def]
/-
**WithLp.unitization_nnnorm_inr** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：unitization_nnnorm_inr (x : A) : ‖toLp 1 (x : Unitization 𝕜 A)‖₊ = ‖x‖₊
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithLp.unitization_nnnorm_def`：unitization_nnnorm_def (x : WithLp 1 (Uni
tization 𝕜 A)) : ‖x‖₊ = ‖(ofLp x).fst‖₊ + ‖(ofLp x).snd‖₊
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unitization_nnnorm_inr (x : A) : ‖toLp 1 (x : Unitization 𝕜 A)‖₊ = ‖x‖₊ := by
  simp [unitization_nnnorm_def]
/-
**WithLp.unitization_isometry_inr** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：unitization_isometry_inr : Isometry fun x : A => toLp 1 (x : Unitization 𝕜
 A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `WithLp.unitization_norm_inr`：unitization_norm_inr (x : A) : ‖toLp 1 (x :
 Unitization 𝕜 A)‖ = ‖x‖
-/
lemma unitization_isometry_inr : Isometry fun x : A ↦ toLp 1 (x : Unitization 𝕜 A) :=
  AddMonoidHomClass.isometry_of_norm
    ((WithLp.linearEquiv 1 𝕜 (Unitization 𝕜 A)).symm.comp <| Unitization.inrHom 𝕜 𝕜 A)
    unitization_norm_inr

variable [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
/-
**WithLp.instUnitizationRing** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instUnitizationRing : Ring (WithLp 1 (Unitization 𝕜 A))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUnitizationRing : Ring (WithLp 1 (Unitization 𝕜 A)) :=
  (WithLp.equiv 1 (Unitization 𝕜 A)).ring

@[simp]
/-
**WithLp.unitization_mul** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：unitization_mul (x y : WithLp 1 (Unitization 𝕜 A)) : ofLp (x * y) = ofLp x
 * ofLp y
参数：x y : WithLp 1 (Unitization 𝕜 A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitization_mul (x y : WithLp 1 (Unitization 𝕜 A)) : ofLp (x * y) = ofLp x * ofLp y := rfl
/-
**WithLp.** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A] [IsScalarTower R 𝕜 A] :
    Algebra R (WithLp 1 (Unitization 𝕜 A)) :=
  (WithLp.equiv 1 (Unitization 𝕜 A)).algebra R

@[simp]
/-
**WithLp.unitization_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：unitization_algebraMap (r : 𝕜) : ofLp (algebraMap 𝕜 (WithLp 1 (Unitization
 𝕜 A)) r) = algebraMap 𝕜 (Unitization 𝕜 A) r
参数：r : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitization_algebraMap (r : 𝕜) :
    ofLp (algebraMap 𝕜 (WithLp 1 (Unitization 𝕜 A)) r) = algebraMap 𝕜 (Unitization 𝕜 A) r := rfl

/-- `equiv` bundled as an algebra isomorphism with `Unitization 𝕜 A`. -/
@[simps!]
/-
**WithLp.unitizationAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithLp`。
形式化陈述：unitizationAlgEquiv (R : Type*) [CommSemiring R] [Algebra R 𝕜] [DistribMul
Action R A] [IsScalarTower R 𝕜 A] : WithLp 1 (Unitization 𝕜 A) ≃ₐ[R] Unitization
 𝕜 A where __
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`equiv` bundled as an algebra isomorphism with `Unitization 𝕜 A`.
-/
def unitizationAlgEquiv (R : Type*) [CommSemiring R] [Algebra R 𝕜] [DistribMulAction R A]
    [IsScalarTower R 𝕜 A] : WithLp 1 (Unitization 𝕜 A) ≃ₐ[R] Unitization 𝕜 A where
  __ := WithLp.linearEquiv _ R _
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
/-
**WithLp.instUnitizationNormedRing** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instUnitizationNormedRing : NormedRing (WithLp 1 (Unitization 𝕜 A)) where 
dist_eq
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instUnitizationNormedRing : NormedRing (WithLp 1 (Unitization 𝕜 A)) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := by
    simp_rw [unitization_norm_def, add_mul, mul_add, unitization_mul, fst_mul, snd_mul]
    rw [add_assoc, add_assoc]
    gcongr
    · exact norm_mul_le _ _
    · apply (norm_add_le _ _).trans
      gcongr
      · simp [norm_smul]
      · apply (norm_add_le _ _).trans
        gcongr
        · simp [norm_smul, mul_comm]
        · exact norm_mul_le _ _
/-
**WithLp.instUnitizationNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `WithLp`。
形式化陈述：instUnitizationNormedAlgebra : NormedAlgebra 𝕜 (WithLp 1 (Unitization 𝕜 A)
) where norm_smul_le r x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instUnitizationNormedAlgebra :
    NormedAlgebra 𝕜 (WithLp 1 (Unitization 𝕜 A)) where
  norm_smul_le r x := by
    simp_rw [unitization_norm_def, ofLp_smul, fst_smul, snd_smul, norm_smul, mul_add]
    exact le_rfl

end WithLp

